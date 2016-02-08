#pragma once

#include <functional>

// Monomorphic pair
// Monomorphic refers to the fact that both elements have the same type
template <typename T> struct MonoPair {
    T first;
    T second;
    template <typename NewT>
    MonoPair<NewT> map(std::function<NewT(T)> f) const {
        NewT newFirst = f(first);
        NewT newSecond = f(second);
        return {newFirst, newSecond};
    }
    void forEach(std::function<void(T)> f) const {
        f(first);
        f(second);
    }
    // left fold
    template <typename Result>
    Result foldl(Result init, std::function<Result(Result, T)> f) const {
        return f(f(init, first), second);
    }
    // right fold
    template <typename Result>
    Result foldr(std::function<Result(T, Result)> f, Result init) const {
        return f(first, f(second, init));
    }
    MonoPair(T first, T second)
        : first(std::move(first)), second(std::move(second)) {}
};

template <typename T> MonoPair<T> makeMonoPair(T first, T second) {
    return MonoPair<T>(std::move(first), std::move(second));
}

template <typename A, typename B, typename C>
MonoPair<C> zipWith(MonoPair<A> pairA, MonoPair<B> pairB,
                    std::function<C(A, B)> f) {
    return {f(pairA.first, pairB.first), f(pairA.second, pairB.second)};
}
