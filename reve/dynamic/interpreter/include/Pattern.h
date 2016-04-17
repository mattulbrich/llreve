#pragma once

#include "Helper.h"
#include "MonoPair.h"

enum class Placeholder { Variable, Constant };
enum class Operation { Eq, Add };
enum class ExprType { BinOp, Val };
template <typename T> using VecIter = typename std::vector<T>::iterator;

template <typename T> struct Expr {
    virtual ExprType getType() const = 0;
    virtual ~Expr();
    bool matches(std::vector<T> vec) const {
        return matches(vec.begin(), vec.end());
    }
    virtual bool matches(VecIter<T> begin, VecIter<T> end) const = 0;
    virtual T eval(VecIter<T> begin, VecIter<T> end) const = 0;
    virtual size_t arguments() const = 0;
};

template <typename T> struct BinaryOp : Expr<T> {
    Operation op;
    MonoPair<std::shared_ptr<Expr<T>>> args;
    ExprType getType() const override { return ExprType::BinOp; }
    bool matches(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin = args.first.arguments() + args.second.arguments());
        switch (op) {
        case Operation::Eq: {
            VecIter<T> mid = begin + args.first.arguments();
            T left = args.first.eval(begin, mid);
            T right = args.second.eval(mid, end);
            return left == right;
        }
        case Operation::Add:
            logWarning("Matching on an addition is always true\n");
            return true;
        }
    }
    T eval(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin = args.first.arguments() + args.second.arguments());
        VecIter<T> mid = begin + args.first.arguments();
        T left = args.first.eval(begin, mid);
        T right = args.second.eval(mid, end);
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
    virtual size_t arguments() const {
        return args.first.arguments() + args.second.arguments();
    }
};

template <typename T> struct Value : Expr<T> {
    Placeholder val;
    ExprType getType() const override { return ExprType::Val; }
    bool matches(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin == 1);
        return true;
    }
    T eval(VecIter<T> begin, VecIter<T> end) const override {
        assert(end - begin == 1);
        return *begin;
    }
    size_t arguments() const { return 1; }
};
