#pragma once

#include <cstddef>
#include <cstdint>
#include <unordered_map>
#include <vector>

#ifdef _DEBUG
#define DEBUG(X) X
#else
#define DEBUG(X)
#endif

// Known jump table at a bctr: its case labels, plus the table bytes when they sit inline in code.
struct FunctionSwitchInfo
{
    std::vector<uint32_t> labels;
    uint32_t table{};
    uint32_t tableSize{};
};
using FunctionSwitchMap = std::unordered_map<uint32_t, FunctionSwitchInfo>; // keyed by bctr address

struct Function
{
    struct Block
    {
        size_t base{};
        size_t size{};
        size_t projectedSize{ static_cast<size_t>(-1) }; // scratch
        DEBUG(size_t parent{});

        Block() 
        {
        }

        Block(size_t base, size_t size)
            : base(base), size(size) 
        {
        }

        Block(size_t base, size_t size, size_t projectedSize) 
            : base(base), size(size), projectedSize(projectedSize)
        {
        }
    };

    size_t base{};
    size_t size{};
    std::vector<Block> blocks{};

    Function()
    {
    }

    Function(size_t base, size_t size)
        : base(base), size(size)
    {
    }
    
    size_t SearchBlock(size_t address) const;
    // `switches` lets the analysis follow jump table targets instead of treating bctr as a tail call.
    static Function Analyze(const void* code, size_t size, size_t base, const FunctionSwitchMap* switches = nullptr);
};
