#pragma once

#include "MonoPair.h"

#include "gmpxx.h"

#include "llvm/IR/Function.h"

/// Interprets the provided functions for all combinations of inputs
/// within the provided bounds. The output is written to the output
/// directory to files named ${functionName}_(1|2)_${counter}.json
/// where counter just ensures that the names are unique. The actual
/// function arguments can be found in the entry state.
auto serializeValuesInRange(MonoPair<const llvm::Function *> funs,
                            mpz_class lowerBound, mpz_class upperBound,
                            std::string outputDirectory) -> void;

// All combinations of values inside the bounds, upperbound included
class Range {
    mpz_class lowerBound;
    mpz_class upperBound;
    size_t n;

  public:
    Range(mpz_class lowerBound, mpz_class upperBound, size_t n)
        : lowerBound(lowerBound), upperBound(upperBound), n(n) {
        assert(n > 0);
    }
    class RangeIterator
        : std::iterator<std::forward_iterator_tag, std::vector<mpz_class>> {
        mpz_class lowerBound;
        mpz_class upperBound;
        std::vector<mpz_class> vals;
        size_t index;

      public:
        RangeIterator(mpz_class lowerBound, mpz_class upperBound,
                      std::vector<mpz_class> vals)
            : lowerBound(lowerBound), upperBound(upperBound), vals(vals),
              index(vals.size()-1) {}
        RangeIterator &operator++();
        bool operator==(const RangeIterator &other) {
            return vals == other.vals;
        }
        bool operator!=(const RangeIterator &other) {
            return vals != other.vals;
        }
        std::vector<mpz_class> &operator*() { return vals; }
    };
    RangeIterator begin();
    RangeIterator end();
};
