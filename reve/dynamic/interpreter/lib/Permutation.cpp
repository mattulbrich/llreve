/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Permutation.h"

#include <set>
#include <vector>

using std::vector;
using std::set;
using std::multiset;

vector<vector<size_t>> kCombinationsWithRepetitionsInt(size_t n, size_t k) {
    if (n == 0 || k == 0) {
        return {};
    }
    vector<vector<size_t>> result;
    vector<size_t> current(k, 0);
    set<multiset<size_t>> alreadyAdded;
    size_t i = 0;
    while (1) {
        multiset<size_t> cur;
        cur.insert(current.begin(), current.end());
        if (alreadyAdded.count(cur) == 0) {
            result.push_back(current);
        }
        if (current[i] < n - 1) {
            current[i]++;
        } else {
            while (current[i] == n - 1) {
                ++i;
            }
            if (i == k) {
                break;
            } else {
                current[i]++;
                for (size_t j = 0; j < i; ++j) {
                    current[j] = 0;
                }
                i = 0;
            }
        }
    }
    return result;
}
