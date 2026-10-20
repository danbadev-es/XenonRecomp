#include "dataflow_switch.h"

#include <algorithm>
#include <memory>

#include <byteswap.h>

namespace
{
    constexpr uint32_t kBctr = 0x4E800420;
    constexpr uint32_t kNop = 0x60000000; // ori r0, r0, 0
    constexpr int kWindow = 24;           // instructions searched backwards for definitions
    constexpr int kGuardWindow = 40;      // instructions searched backwards for cmplwi/bgt
    constexpr int kIndexGuardWindow = 256; // the same, for a cmplwi on the known index register

    uint32_t Op(uint32_t w) { return w >> 26; }
    uint32_t RT(uint32_t w) { return (w >> 21) & 31; }
    uint32_t RA(uint32_t w) { return (w >> 16) & 31; }
    uint32_t RB(uint32_t w) { return (w >> 11) & 31; }
    uint32_t XO(uint32_t w) { return (w >> 1) & 0x3FF; }
    int32_t SImm(uint32_t w) { return int16_t(w & 0xFFFF); }
    uint32_t UImm(uint32_t w) { return w & 0xFFFF; }

    bool IsMtctr(uint32_t w) { return Op(w) == 31 && XO(w) == 467 && ((RB(w) << 5) | RA(w)) == 9; }

    // Registers written by an instruction; conservative for anything not decoded.
    // Returns -1 when nothing (that we track) is written, -2 when unknown.
    int WrittenGpr(uint32_t w)
    {
        switch (Op(w))
        {
        case 14: case 15: case 12: case 13: case 7: case 8:          // addi, addis, addic(.), mulli, subfic
        case 32: case 33: case 34: case 35: case 40: case 41: case 42: case 43: case 58: // loads
            return RT(w);
        case 24: case 25: case 26: case 27: case 28: case 29:         // ori/oris/xori/xoris/andi./andis.
        case 20: case 21: case 23: case 30:                           // rlwimi/rlwinm/rlwnm/rld*
            return RA(w);
        case 36: case 37: case 38: case 39: case 44: case 45: case 52: case 53: case 54: case 55: case 62: // stores
        case 10: case 11:                                             // cmpli/cmpi
        case 16: case 18:                                             // branches
        case 48: case 49: case 50: case 51:                           // fp loads (fpr)
        case 4: case 6: case 59: case 63:                             // vmx / fp arith
            return -1;
        case 31:
        {
            uint32_t xo = XO(w);
            if (xo == 0 || xo == 32) return -1;                       // cmp/cmpl
            if (xo == 467 || xo == 151 || xo == 215 || xo == 407 || xo == 150 || xo == 149 || xo == 183) return -1; // mtspr, stores
            // Logical ops (and/or/xor/nor/andc/orc/nand/eqv/slw/srw/sraw/srawi/cntlzw/extsb/extsh/extsw)
            // write rA; arithmetic and loads write rT.
            switch (xo)
            {
            case 28: case 444: case 316: case 124: case 60: case 412: case 476: case 284:
            case 24: case 536: case 792: case 824: case 26: case 954: case 922: case 986:
            case 27: case 539: case 794: case 413:
                return RA(w);
            default:
                return RT(w);
            }
        }
        case 19:
            return -1;                                                 // bclr/bcctr/cr ops
        default:
            return -2;
        }
    }

    // A call (bl, bcl, bctrl, bclrl): it returns in r3 and may change every volatile register.
    bool IsCall(uint32_t w)
    {
        return (w & 1) && (Op(w) == 18 || Op(w) == 16 || (Op(w) == 19 && (XO(w) == 16 || XO(w) == 528)));
    }

    bool IsVolatile(uint32_t reg) { return reg == 0 || (reg >= 3 && reg <= 12); }

    // Whether the instruction may change `reg`.
    bool Clobbers(uint32_t w, uint32_t reg)
    {
        if (IsCall(w))
            return IsVolatile(reg);
        const int written = WrittenGpr(w);
        return written == int(reg) || written == -2;
    }

    struct Expr
    {
        enum Kind { Unknown, Const, Reg, Add, Shl, Load } kind = Unknown;
        uint32_t value = 0;      // Const value, Reg number, Shl amount, Load size
        uint32_t srcReg = 0;     // Shl: register that was shifted
        std::shared_ptr<Expr> a, b;
    };
    using ExprPtr = std::shared_ptr<Expr>;

    ExprPtr MakeConst(uint32_t v) { auto e = std::make_shared<Expr>(); e->kind = Expr::Const; e->value = v; return e; }
    ExprPtr MakeUnknown() { return std::make_shared<Expr>(); }

    ExprPtr Simplify(ExprPtr e)
    {
        if (e->kind == Expr::Add && e->a->kind == Expr::Const && e->b->kind == Expr::Const)
            return MakeConst(e->a->value + e->b->value);
        return e;
    }

    struct Resolver
    {
        const uint32_t* words; // host pointer to the instruction at `start`
        uint32_t start;        // guest address of words[0]
        uint32_t limit;        // lowest guest address we may look at

        uint32_t At(uint32_t addr) const { return ByteSwap(words[(int64_t(addr) - start) / 4]); }

        // Value of `reg` just before the instruction at `pos`.
        ExprPtr Resolve(uint32_t reg, uint32_t pos, int depth = 0) const
        {
            if (depth > 12) return MakeUnknown();
            for (int i = 1; i <= kWindow; i++)
            {
                uint32_t addr = pos - 4 * i;
                if (addr < limit) break;
                uint32_t w = At(addr);
                if (w == kNop) continue;
                // Code before an unconditional b/blr/bctr doesn't fall through to here (it is often the
                // end of the previous function): the value comes from elsewhere.
                if ((Op(w) == 18 && !(w & 1)) || w == 0x4E800020 || w == kBctr)
                    break;
                if (IsCall(w))
                {
                    if (IsVolatile(reg)) return MakeUnknown();
                    continue;
                }

                int written = WrittenGpr(w);
                if (written == -1) continue;
                if (written == -2) return MakeUnknown();
                if (uint32_t(written) != reg) continue;

                auto e = std::make_shared<Expr>();
                switch (Op(w))
                {
                case 15: // lis / addis
                    if (RA(w) == 0) return MakeConst(UImm(w) << 16);
                    e->kind = Expr::Add; e->a = Resolve(RA(w), addr, depth + 1); e->b = MakeConst(UImm(w) << 16);
                    return Simplify(e);
                case 14: // li / addi
                    if (RA(w) == 0) return MakeConst(uint32_t(SImm(w)));
                    e->kind = Expr::Add; e->a = Resolve(RA(w), addr, depth + 1); e->b = MakeConst(uint32_t(SImm(w)));
                    return Simplify(e);
                case 24: // ori
                {
                    auto src = Resolve(RT(w), addr, depth + 1);
                    if (UImm(w) == 0) return src;
                    if (src->kind == Expr::Const) return MakeConst(src->value | UImm(w));
                    return MakeUnknown();
                }
                case 21: // rlwinm
                {
                    uint32_t sh = RB(w), mb = (w >> 6) & 31, me = (w >> 1) & 31;
                    auto src = Resolve(RT(w), addr, depth + 1);
                    if (mb == 0 && me == 31 - sh) { e->kind = Expr::Shl; e->value = sh; e->srcReg = RT(w); e->a = src; return e; }
                    if (sh == 0 && me == 31) return src; // clrlwi: masking only
                    return MakeUnknown();
                }
                case 31:
                    switch (XO(w))
                    {
                    case 444: // or (mr when rS == rB)
                        if (RT(w) == RB(w)) return Resolve(RT(w), addr, depth + 1);
                        return MakeUnknown();
                    case 266: // add
                        e->kind = Expr::Add; e->a = Resolve(RA(w), addr, depth + 1); e->b = Resolve(RB(w), addr, depth + 1);
                        return Simplify(e);
                    case 23: case 279: case 87: // lwzx, lhzx, lbzx
                        e->kind = Expr::Load;
                        e->value = XO(w) == 23 ? 4 : XO(w) == 279 ? 2 : 1;
                        e->a = RA(w) ? Resolve(RA(w), addr, depth + 1) : MakeConst(0);
                        e->b = Resolve(RB(w), addr, depth + 1);
                        return e;
                    }
                    return MakeUnknown();
                default:
                    return MakeUnknown();
                }
            }
            auto e = std::make_shared<Expr>();
            e->kind = Expr::Reg;
            e->value = reg;
            return e;
        }
    };

    // Splits a Load's address into (constant table address, index expression).
    bool SplitTable(const ExprPtr& load, uint32_t& table)
    {
        if (load->a->kind == Expr::Const && load->b->kind != Expr::Const) { table = load->a->value; return true; }
        if (load->b->kind == Expr::Const && load->a->kind != Expr::Const) { table = load->b->value; return true; }
        return false;
    }

    // The register indexing the table, when the index expression is that register (possibly
    // shifted); ~0u otherwise.
    uint32_t IndexRegister(const ExprPtr& load)
    {
        const ExprPtr& index = load->a->kind == Expr::Const ? load->b : load->a;
        if (index->kind == Expr::Shl) return index->srcReg;
        if (index->kind == Expr::Reg) return index->value;
        return ~0u;
    }

    // The branch to the default case after a bounds check on crN: "bgt crN, default",
    // "ble crN, +8; b default" or "bgtlr crN" (default 0).
    bool GuardBranch(const Resolver& resolver, uint32_t addr, uint32_t cr, uint32_t& defaultLabel)
    {
        const uint32_t w = resolver.At(addr);
        const bool gtBit = (RA(w) & 3) == 1 && (RA(w) >> 2) == cr;
        if (Op(w) == 16 && RT(w) == 12 && gtBit && (w & 3) == 0)
        {
            defaultLabel = addr + uint32_t(int32_t(int16_t(w & 0xFFFC)));
            return true;
        }
        if (Op(w) == 19 && XO(w) == 16 && RT(w) == 12 && gtBit)
        {
            defaultLabel = 0;
            return true;
        }
        if (Op(w) == 16 && RT(w) == 4 && gtBit && (w & 0xFFFF) == 8)
        {
            const uint32_t next = resolver.At(addr + 4);
            if (Op(next) == 18 && (next & 3) == 0)
            {
                defaultLabel = addr + 4 + uint32_t(int32_t((next & 0x03FFFFFC) << 6) >> 6);
                return true;
            }
        }
        return false;
    }

    const Section* SectionOf(const Image& image, uint32_t addr)
    {
        auto it = image.sections.upper_bound(addr);
        if (it == image.sections.begin()) return nullptr;
        --it;
        if (addr < it->base || addr >= it->base + it->size) return nullptr;
        return &*it;
    }
}

std::vector<DataflowSwitch> ScanDataflowSwitches(const Image& image, std::vector<uint32_t>* rejected)
{
    std::vector<DataflowSwitch> result;

    for (const auto& section : image.sections)
    {
        if (!(section.flags & SectionFlags_Code))
            continue;

        const auto* words = reinterpret_cast<const uint32_t*>(section.data);
        const uint32_t base = uint32_t(section.base);
        const uint32_t count = section.size / 4;
        Resolver resolver{ words, base, base };

        for (uint32_t i = 1; i < count; i++)
        {
            if (ByteSwap(words[i]) != kBctr)
                continue;

            // mtctr rX right before the bctr (allowing scheduling nops).
            uint32_t j = i - 1;
            while (j > 0 && ByteSwap(words[j]) == kNop) j--;
            const uint32_t mtctr = ByteSwap(words[j]);
            if (!IsMtctr(mtctr))
                continue;

            const uint32_t bctrAddr = base + i * 4;
            const uint32_t mtctrAddr = base + j * 4;
            ExprPtr target = resolver.Resolve(RT(mtctr), mtctrAddr);

            DataflowSwitch sw;
            sw.bctr = bctrAddr;
            uint32_t shift = 0;
            uint32_t caseBase = 0;
            uint32_t entrySize = 0;
            uint32_t indexReg = ~0u;

            if (target->kind == Expr::Load && target->value == 4 && SplitTable(target, sw.table))
            {
                sw.kind = 0;
                entrySize = 4;
                indexReg = IndexRegister(target);
            }
            else if (target->kind == Expr::Add)
            {
                ExprPtr c = target->a->kind == Expr::Const ? target->a : target->b;
                ExprPtr off = target->a->kind == Expr::Const ? target->b : target->a;
                if (c->kind != Expr::Const)
                    continue;
                if (off->kind == Expr::Shl) { shift = off->value; off = off->a; }
                if (off->kind != Expr::Load || off->value == 4)
                    continue;
                if (!SplitTable(off, sw.table))
                {
                    // "code + loaded offset" but the table address isn't recognisable: report it rather
                    // than leave a silent indirect call (its cases would run as separate functions).
                    if (rejected) rejected->push_back(bctrAddr);
                    continue;
                }
                caseBase = c->value;
                entrySize = off->value;
                sw.kind = entrySize == 1 ? 2 : 3;
                indexReg = IndexRegister(off);
            }
            else
            {
                continue; // vtable call or other indirect branch
            }

            // Guard on the index register itself: the nearest "cmplwi crN, rIndex, N" before the
            // bctr (after the index's last definition), followed within 8 instructions by the branch
            // to the default case. It can be far from the bctr when cases share code in between.
            bool guarded = false;
            for (int k = 1; indexReg != ~0u && k <= kIndexGuardWindow; k++)
            {
                const uint32_t addr = bctrAddr - 4 * k;
                if (addr < base) break;
                const uint32_t w = resolver.At(addr);
                if (Op(w) == 10 && RA(w) == indexReg)
                {
                    const uint32_t cr = RT(w) >> 2;
                    for (uint32_t b = addr + 4; b <= addr + 4 * 8 && b < bctrAddr && !guarded; b += 4)
                        guarded = GuardBranch(resolver, b, cr, sw.defaultLabel);
                    if (guarded)
                    {
                        sw.r = indexReg;
                        sw.labels.resize(UImm(w) + 1);
                        for (uint32_t a = addr + 4; a < bctrAddr; a += 4)
                        {
                            if (Clobbers(resolver.At(a), sw.r)) { guarded = false; break; }
                        }
                        if (!guarded) sw.labels.clear();
                    }
                    break;
                }
                if (Clobbers(w, indexReg)) break;
            }

            // Otherwise: cmplwi crN, rI, N followed by a bgt crN (or ble crN), close to the bctr.
            bool haveBranch = false;
            uint32_t guardCr = 0;
            for (int k = 1; k <= kGuardWindow && !guarded; k++)
            {
                uint32_t addr = bctrAddr - 4 * k;
                if (addr < base) break;
                uint32_t w = resolver.At(addr);
                const bool gtBit = (RA(w) & 3) == 1;
                if (!haveBranch && Op(w) == 16 && RT(w) == 12 && gtBit) // bgt crN, default
                {
                    haveBranch = true;
                    guardCr = RA(w) >> 2;
                    sw.defaultLabel = addr + uint32_t(int32_t(int16_t(w & 0xFFFC)));
                }
                else if (!haveBranch && Op(w) == 19 && XO(w) == 16 && RT(w) == 12 && gtBit) // bgtlr crN
                {
                    haveBranch = true;
                    guardCr = RA(w) >> 2;
                    sw.defaultLabel = 0;
                }
                else if (Op(w) == 10 && haveBranch && (RT(w) >> 2) == guardCr)
                {
                    sw.r = RA(w);
                    sw.labels.resize(UImm(w) + 1);
                    guarded = true;

                    // The index register must survive until the bctr. (A guard that doesn't count, e.g.
                    // another switch's before this one, leaves no labels behind for the checks below.)
                    for (uint32_t a = addr + 4; a < bctrAddr; a += 4)
                    {
                        if (Clobbers(resolver.At(a), sw.r)) { guarded = false; break; }
                    }
                    if (!guarded) sw.labels.clear();
                }
            }
            // Unguarded switch (index known to be in range) with an absolute table placed right after
            // the bctr: the table ends where the code of the lowest case label after it begins. Cases
            // may also go back to code before the dispatch (a shared default, for instance).
            if (!guarded && sw.kind == 0 && sw.table == bctrAddr + 4)
            {
                ExprPtr index = target->a->kind == Expr::Const ? target->b : target->a;
                if (index->kind == Expr::Shl && index->value == 2)
                {
                    sw.r = index->srcReg;
                    sw.defaultLabel = 0;
                    uint32_t lowest = UINT32_MAX;
                    const uint32_t sectionEnd = base + section.size;
                    for (uint32_t addr = sw.table; addr < lowest && addr < sectionEnd; addr += 4)
                    {
                        uint32_t label = resolver.At(addr);
                        const uint32_t distance = label > bctrAddr ? label - bctrAddr : bctrAddr - label;
                        if ((label & 3) != 0 || label == bctrAddr || label < base || label >= sectionEnd ||
                            distance > 0x10000)
                        {
                            lowest = 0;
                            break;
                        }
                        if (label > bctrAddr)
                            lowest = std::min(lowest, label);
                        sw.labels.push_back(label);
                    }
                    guarded = lowest != 0 && lowest != UINT32_MAX && !sw.labels.empty() &&
                        sw.table + sw.labels.size() * 4 == lowest;
                    // The index must not change between its use in the address computation (the
                    // nearest rlwinm of it before the mtctr) and the bctr.
                    for (uint32_t a = mtctrAddr - 4; guarded && a >= base && a + 4 * kWindow > mtctrAddr; a -= 4)
                    {
                        uint32_t w = resolver.At(a);
                        if (Op(w) == 21 && RT(w) == sw.r) { for (uint32_t b = a + 4; b < bctrAddr; b += 4) if (Clobbers(resolver.At(b), sw.r)) guarded = false; break; }
                    }
                    if (!guarded) sw.labels.clear();
                }
            }

            // Unguarded offset table: no length, so every valid entry (aligned code near the bctr, up
            // to 256) is a possible target, and the recompiler dispatches on the target address.
            if (!guarded && (sw.kind == 2 || sw.kind == 3))
            {
                sw.labels.clear();
                const Section* tableSection = SectionOf(image, sw.table);
                const auto* raw = static_cast<const uint8_t*>(image.Find(sw.table));
                if (tableSection && raw)
                {
                    const uint32_t available = (tableSection->base + tableSection->size - sw.table) / entrySize;
                    uint32_t n = 0;
                    for (; n < std::min(256u, available); n++)
                    {
                        const uint32_t value = entrySize == 2 ? ByteSwap(reinterpret_cast<const uint16_t*>(raw)[n]) : raw[n];
                        const uint32_t label = caseBase + (value << shift);
                        if ((label & 3) != 0 || label < base || label >= base + section.size || label - bctrAddr > 0x10000)
                            break;
                        if (std::find(sw.labels.begin(), sw.labels.end(), label) == sw.labels.end())
                            sw.labels.push_back(label);
                    }
                    if (!sw.labels.empty())
                    {
                        sw.byAddress = true;
                        sw.r = 0;
                        sw.defaultLabel = 0;
                        sw.tableSize = n * entrySize;
                        result.push_back(std::move(sw));
                        continue;
                    }
                }
            }

            if (!guarded || sw.labels.empty() || sw.labels.size() > 4096)
            {
                if (rejected) rejected->push_back(bctrAddr);
                continue;
            }

            const Section* tableSection = SectionOf(image, sw.table);
            if (!tableSection || sw.table + sw.labels.size() * entrySize > tableSection->base + tableSection->size)
            {
                if (rejected) rejected->push_back(bctrAddr);
                continue;
            }

            const auto* raw = static_cast<const uint8_t*>(image.Find(sw.table));
            bool valid = true;
            for (size_t n = 0; n < sw.labels.size(); n++)
            {
                uint32_t label;
                if (entrySize == 4) label = ByteSwap(reinterpret_cast<const uint32_t*>(raw)[n]);
                else if (entrySize == 2) label = caseBase + (uint32_t(ByteSwap(reinterpret_cast<const uint16_t*>(raw)[n])) << shift);
                else label = caseBase + (uint32_t(raw[n]) << shift);

                if ((label & 3) != 0 || label < base || label >= base + section.size) { valid = false; break; }
                sw.labels[n] = label;
            }
            if (!valid)
            {
                if (rejected) rejected->push_back(bctrAddr);
                continue;
            }

            sw.tableSize = uint32_t(sw.labels.size() * entrySize);
            result.push_back(std::move(sw));
        }
    }

    return result;
}
