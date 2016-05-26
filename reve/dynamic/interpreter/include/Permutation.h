#pragma once

#include <iostream>
#include <list>
#include <vector>
#include <algorithm>

template <typename T>
std::list<std::vector<T>> kSubset(std::vector<T> input, size_t k) {
    if (k > input.size()) {
        return {};
    }
    std::list<std::vector<T>> output;
    assert(input.size() < 64);
    uint64_t bitVec = (1 << k) - 1;
    do {
        std::vector<T> subset(k);
        size_t j = 0;
        for (size_t i = 0; i < input.size(); ++i) {
            if (bitVec & (1 << i)) {
                subset.at(j) = input.at(i);
                ++j;
            }
        }
        output.push_back(subset);
        // Dark magic from
        // https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
        uint64_t t = bitVec | (bitVec - 1);
        bitVec = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzl(bitVec) + 1));
    } while (!(bitVec & (1 << input.size())));
    return output;
}

// Somebody should really write a test for this :P
template <typename T>
std::list<std::vector<T>> kPermutations(std::vector<T> input, size_t k) {
    if (k > input.size()) {
        return {};
    }
    std::list<std::vector<T>> output;
    std::list<std::vector<T>> subsets = kSubset(input, k);
    for (auto vec : subsets) {
        // Sort for next_permutation
        std::sort(vec.begin(), vec.end());
        do {
            output.push_back(vec);
        } while (std::next_permutation(vec.begin(), vec.end()));
    }
    return output;
}

std::vector<std::vector<size_t>> kCombinationsWithRepetitionsInt(size_t n,
                                                                 size_t k);

template <typename T>
std::vector<std::vector<T>> kCombinationsWithRepetitions(std::vector<T> input,
                                                         size_t k) {
    auto ints = kCombinationsWithRepetitionsInt(input.size(), k);
    std::vector<std::vector<T>> result;
    for (auto vec : ints) {
        std::vector<T> vecT(k);
        for (size_t i = 0; i < k; ++i) {
            vecT.at(i) = input.at(vec[i]);
        }
        result.push_back(vecT);
    }
    return result;
}
