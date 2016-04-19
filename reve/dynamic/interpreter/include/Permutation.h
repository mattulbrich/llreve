#pragma once


template <typename T>
std::list<std::vector<T>> kSubset(std::vector<T> input, size_t k) {
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
        uint64_t t = (bitVec | (bitVec - 1)) + 1;
        bitVec = t | ((((t & -t) / (bitVec & -bitVec)) >> 1) - 1);
    } while (!(bitVec & (1 << input.size())));
    return output;
}

// Somebody should really write a test for this :P
template <typename T>
std::list<std::vector<T>> kPermutations(std::vector<T> input, size_t k) {
    if (k > input.size()) {
        logError("Requested more elements than the input contains\n");
        return {};
    }
    std::list<std::vector<T>> output;
    std::list<std::vector<T>> subsets = kSubset(input, k);
    for (auto vec : subsets) {
        // Sort for next_permutation
        std::sort(vec.begin(), vec.end());
        do {
            output.push_back(vec);
        } while (std::next_permutation(vec.begin(),
                                       vec.end()));
    }
    return output;
}
