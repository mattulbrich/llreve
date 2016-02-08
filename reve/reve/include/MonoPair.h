#pragma once

#include <functional>
#include <vector>

// Monomorphic pair
// Monomorphic refers to the fact that both elements have the same type
template <typename T> struct MonoPair {
    T first;
    T second;

    MonoPair(T first, T second)
        : first(std::move(first)), second(std::move(second)) {}

    template <typename NewT>
    MonoPair<NewT> map(std::function<NewT(T)> f) const {
        NewT newFirst = f(first);
        NewT newSecond = f(second);
        return {newFirst, newSecond};
    }

    template <typename NewT>
    MonoPair<NewT> indexedMap(std::function<NewT(T, int)> f) const {
        NewT newFirst = f(first, 1);
        NewT newSecond = f(second, 2);
        return {newFirst, newSecond};
    }

    void forEach(std::function<void(T)> f) const {
        f(first);
        f(second);
    }

    void indexedForEach(std::function<void(T, int)> f) const {
        f(first, 1);
        f(second, 2);
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
};

template <typename T> MonoPair<T> makeMonoPair(T first, T second) {
    return MonoPair<T>(std::move(first), std::move(second));
}

template <typename A, typename B, typename C>
MonoPair<C> zipWith(MonoPair<A> pairA, MonoPair<B> pairB,
                    std::function<C(A, B)> f) {
    return {f(pairA.first, pairB.first), f(pairA.second, pairB.second)};
}

template <typename A, typename B>
MonoPair<std::pair<A, B>> zip(MonoPair<A> pairA, MonoPair<B> pairB) {
    return zipWith<A, B, std::pair<A, B>>(
        pairA, pairB,
        [](A a, B b) -> std::pair<A, B> { return std::make_pair(a, b); });
}

template <typename A, typename B>
auto rewrapMonoPair(MonoPair<A> pair) -> MonoPair<B> {
    return {pair.first, pair.second};
}

template <typename A>
void appendTo(std::vector<A> &to, MonoPair<std::vector<A>> pair) {
    to.insert(to.end(), pair.first.begin(), pair.first.end());
    to.insert(to.end(), pair.second.begin(), pair.second.end());
}

// special folds
template <typename A> std::vector<A> concat(MonoPair<std::vector<A>> pair) {
    return pair.template foldl<std::vector<A>>(
        {},
        [](std::vector<A> acc, std::vector<A> vec) -> std::vector<A> {
            acc.insert(acc.end(), vec.begin(), vec.end());
            return acc;
        });
}
