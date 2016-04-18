#pragma once

// Somebody should really write a test for this :P
template <typename T>
std::list<std::vector<T>> kPermutations(std::vector<T> input, size_t k) {
    if (k > input.size()) {
        logError("Requested more elements than the input contains\n");
        return {};
    }
    std::list<std::vector<T>> output;
    assert(input.size() < 64);
    uint64_t bitVec = (1 << k) - 1;
    do {
        // take the first k elements
        std::vector<T> firstKElements(k);
        size_t j = 0;
        for (size_t i = 0; i < input.size(); ++i) {
            if (bitVec & (1 << i)) {
                firstKElements.at(j) = input.at(i);
                ++j;
            }
        }
        // Sort for next_permutation
        std::sort(firstKElements.begin(), firstKElements.end());
        assert(j == k);
        do {
            output.push_back(firstKElements);
        } while (std::next_permutation(firstKElements.begin(),
                                       firstKElements.end()));
        // Dark magic from
        // https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
        uint64_t t = (bitVec | (bitVec - 1)) + 1;
        bitVec = t | ((((t & -t) / (bitVec & -bitVec)) >> 1) - 1);
        if (bitVec & (1 << input.size())) {
            break;
        }
    } while (true);
    return output;
}
