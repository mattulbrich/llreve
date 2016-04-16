#pragma once

#include "Interpreter.h"
#include "MonoPair.h"
#include "ThreadSafeQueue.h"

#include "gmpxx.h"

#include "llvm/IR/Function.h"

/// Interprets the provided functions for all combinations of inputs
/// within the provided bounds. The output is written to the output
/// directory to files named ${functionName}_(1|2)_${counter}.cbor
/// where counter just ensures that the names are unique. The actual
/// function arguments can be found in the entry state.
auto serializeValuesInRange(MonoPair<const llvm::Function *> funs,
                            VarIntVal lowerBound, VarIntVal upperBound,
                            std::string outputDirectory) -> void;

// All combinations of values inside the bounds, upperbound included
class Range {
    VarIntVal lowerBound;
    VarIntVal upperBound;
    size_t n;

  public:
    Range(VarIntVal lowerBound, VarIntVal upperBound, size_t n)
        : lowerBound(lowerBound), upperBound(upperBound), n(n) {
        assert(n > 0);
    }
    class RangeIterator
        : std::iterator<std::forward_iterator_tag, std::vector<VarIntVal>> {
        VarIntVal lowerBound;
        VarIntVal upperBound;
        std::vector<VarIntVal> vals;
        size_t index;

      public:
        RangeIterator(VarIntVal lowerBound, VarIntVal upperBound,
                      std::vector<VarIntVal> vals)
            : lowerBound(lowerBound), upperBound(upperBound), vals(vals),
              index(vals.size() - 1) {}
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
    std::vector<VarIntVal> vals;
    int counter;
};

void workerThread(MonoPair<const llvm::Function *> funs,
                  ThreadSafeQueue<WorkItem> &q,
                  const std::vector<std::string> varNames,
                  std::string outputDirectory);
