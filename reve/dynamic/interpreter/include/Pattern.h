#pragma once

#include "Helper.h"
#include "MonoPair.h"

namespace pattern {
enum class Placeholder { Variable, Constant };
enum class Operation { Eq, Add };
enum class ExprType { BinOp, Val };
template <typename T> using VecIter = typename std::vector<T>::iterator;

template <typename T> struct Expr {
    virtual ExprType getType() const = 0;
    virtual ~Expr() = default;
    bool matches(std::vector<T> vec) const {
        return matches(vec.begin(), vec.end());
    }
    virtual bool matches(VecIter<T> begin, VecIter<T> end) const = 0;
    virtual T eval(VecIter<T> begin, VecIter<T> end) const = 0;
    virtual size_t arguments() const = 0;
    virtual std::ostream &dump(std::ostream &os, VecIter<std::string> begin,
                               VecIter<std::string> end) const = 0;
    virtual std::ostream &dump(std::ostream &os,
                               std::vector<std::string> vec) const {
        return dump(os, vec.begin(), vec.end());
    }
};

template <typename T> struct BinaryOp : Expr<T> {
    Operation op;
    MonoPair<std::shared_ptr<Expr<T>>> args;
    BinaryOp(Operation op, std::shared_ptr<Expr<T>> arg1,
             std::shared_ptr<Expr<T>> arg2)
        : op(op), args(makeMonoPair(arg1, arg2)) {}
    ExprType getType() const override { return ExprType::BinOp; }
    bool matches(VecIter<T> begin, VecIter<T> end) const override {
        assert(static_cast<size_t>(end - begin) ==
               args.first->arguments() + args.second->arguments());
        switch (op) {
        case Operation::Eq: {
            VecIter<T> mid = begin + static_cast<long>(args.first->arguments());
            T left = args.first->eval(begin, mid);
            T right = args.second->eval(mid, end);
            return left == right;
        }
        case Operation::Add:
            logWarning("Matching on an addition is always true\n");
            return true;
        }
    }
    T eval(VecIter<T> begin, VecIter<T> end) const override {
        assert(static_cast<size_t>(end - begin) ==
               args.first->arguments() + args.second->arguments());
        VecIter<T> mid = begin + static_cast<long>(args.first->arguments());
        T left = args.first->eval(begin, mid);
        T right = args.second->eval(mid, end);
        switch (op) {
        case Operation::Eq:
            logWarning("Evaluating equality equality, converting to integer\n");
            return left == right;
            break;
        case Operation::Add:
            return left + right;
            break;
        }
    }
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::ostream &dump(std::ostream &os, VecIter<std::string> begin,
                       VecIter<std::string> end) const override {
        assert(static_cast<size_t>(end - begin) ==
               args.first->arguments() + args.second->arguments());
        VecIter<std::string> mid =
            begin + static_cast<long>(args.first->arguments());
        os << "(";
        args.first->dump(os, begin, mid);
        switch (op) {
        case Operation::Eq:
            os << " = ";
            break;
        case Operation::Add:
            os << " + ";
            break;
        }
        args.second->dump(os, mid, end);
        os << ")";
        return os;
    }
};

template <typename T> struct Value : Expr<T> {
    Placeholder val;
    explicit Value(Placeholder val) : val(val) {}
    ExprType getType() const override { return ExprType::Val; }
    bool matches(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin == 1);
        return true;
    }
    T eval(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin == 1);
        return *begin;
    }
    size_t arguments() const override { return 1; }
    std::ostream &dump(std::ostream &os, VecIter<std::string> begin,
                       VecIter<std::string> end) const override {
        assert(end - begin == 1);
        os << *begin;
        return os;
    }
};

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
}
