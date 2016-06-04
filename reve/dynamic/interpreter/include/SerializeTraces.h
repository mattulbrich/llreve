#pragma once

#include "Interpreter.h"
#include "MonoPair.h"
#include "ThreadSafeQueue.h"

#include "gmpxx.h"

#include "llvm/IR/Function.h"

// All combinations of values inside the bounds, upperbound included
class Range {
    mpz_class lowerBound;
    mpz_class upperBound;
    size_t n;

  public:
    Range(mpz_class lowerBound, mpz_class upperBound, size_t n)
        : lowerBound(lowerBound), upperBound(upperBound), n(n) {}
    class RangeIterator
        : std::iterator<std::forward_iterator_tag, std::vector<mpz_class>> {
        mpz_class lowerBound;
        mpz_class upperBound;
        std::vector<mpz_class> vals;

      public:
        RangeIterator(mpz_class lowerBound, mpz_class upperBound,
                      std::vector<mpz_class> vals)
            : lowerBound(lowerBound), upperBound(upperBound), vals(vals) {}
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

struct WorkItem {
    MonoPair<std::vector<mpz_class>> vals;
    MonoPair<Heap> heaps;
    bool heapSet;
    int counter;
};
