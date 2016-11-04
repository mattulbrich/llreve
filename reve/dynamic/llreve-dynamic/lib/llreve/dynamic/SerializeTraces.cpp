/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/SerializeTraces.h"

#include "llreve/dynamic/Interpreter.h"
#include "llreve/dynamic/ThreadSafeQueue.h"

#include <fstream>
#include <iostream>
#include <thread>

using std::vector;
using std::string;
using std::make_shared;
using std::map;

using llvm::Function;

Range::RangeIterator Range::begin() {
    vector<mpz_class> vals(n);
    if (n == 0) {
        return RangeIterator(lowerBound, upperBound, vals);
    }
    if (lowerBound > upperBound) {
        return end();
    }
    for (size_t i = 0; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator Range::end() {
    vector<mpz_class> vals(n);
    if (n == 0) {
        return RangeIterator(lowerBound, upperBound, vals);
    }
    vals[0] = upperBound + 1;
    for (size_t i = 1; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator &Range::RangeIterator::operator++() {
    mpz_class carry = 1;
    size_t index = 0;
    while (carry == 1 && index < vals.size()) {
        vals[index]++;
        if (vals[index] == upperBound + 1) {
            carry = 1;
            vals[index] = lowerBound;
        } else {
            carry = 0;
        }
        ++index;
    }
    if (carry == 1) {
        vals[0] = upperBound + 1;
    }
    return *this;
}
