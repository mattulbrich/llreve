#pragma once

#include "Interpreter.h"
#include "MonoPair.h"
#include "ThreadSafeQueue.h"

#include "gmpxx.h"

#include "llvm/IR/Function.h"

// All combinations of values inside the bounds, upperbound included
class Range {
    VarIntVal lowerBound;
    VarIntVal upperBound;
    size_t n;

  public:
    Range(VarIntVal lowerBound, VarIntVal upperBound, size_t n)
        : lowerBound(lowerBound), upperBound(upperBound), n(n) {}
    class RangeIterator
        : std::iterator<std::forward_iterator_tag, std::vector<VarIntVal>> {
        VarIntVal lowerBound;
        VarIntVal upperBound;
        std::vector<VarIntVal> vals;

      public:
        RangeIterator(VarIntVal lowerBound, VarIntVal upperBound,
                      std::vector<VarIntVal> vals)
            : lowerBound(lowerBound), upperBound(upperBound), vals(vals) {}
        RangeIterator &operator++();
        bool operator==(const RangeIterator &other) {
            return vals == other.vals;
        }
        bool operator!=(const RangeIterator &other) {
            return vals != other.vals;
        }
        std::vector<VarIntVal> &operator*() { return vals; }
    };
    RangeIterator begin();
    RangeIterator end();
};

struct WorkItem {
    MonoPair<std::vector<VarIntVal>> vals;
    MonoPair<Heap> heaps;
    bool heapSet;
    int counter;
};
