#pragma once

#include <functional>
#include <vector>

// Monomorphic pair
// Monomorphic refers to the fact that both elements have the same type
template <typename T> struct MonoPair {
    T first;
    T second;

    MonoPair(const T &first, const T &second) : first(first), second(second) {}

    template <typename T1>
    MonoPair(const MonoPair<T1> &p,
             typename std::enable_if<
                 std::is_convertible<const T1 &, T>::value>::type * = 0)
        : first(p.first), second(p.second) {}

    MonoPair(const MonoPair &p) = default;

    MonoPair &operator=(const MonoPair &p) = default;

    MonoPair(MonoPair &&p) = default;

    MonoPair &operator=(MonoPair &&p) = default;

    template <typename T1, class = typename std::enable_if<
                               std::is_convertible<T1, T>::value>::type>
    MonoPair(T1 &&first, T1 &&second)
        : first(std::forward<T1>(first)), second(std::forward<T1>(second)) {}

    template <typename T1>
    MonoPair(
        MonoPair<T1> &&p,
        typename std::enable_if<std::is_convertible<T1, T>::value>::type * = 0)
        : first(std::forward<T1>(p.first)), second(std::forward<T1>(p.second)) {
    }

    template <typename NewT>
    MonoPair<NewT> map(std::function<NewT(T)> f) const {
        return {f(first), f(second)};
    }

    template <typename NewT>
    MonoPair<NewT> indexedMap(std::function<NewT(T, int)> f) const {
        return {f(first, 1), f(second, 2)};
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

// This weird template magic is stolen from libc++
template <class _Tp> struct __make_pair_return_impl { typedef _Tp type; };
template <class _Tp>
struct __make_pair_return_impl<std::reference_wrapper<_Tp>> {
    typedef _Tp &type;
};
template <class _Tp> struct __make_pair_return {
    typedef
        typename __make_pair_return_impl<typename std::decay<_Tp>::type>::type
            type;
};

template <typename T>
MonoPair<typename __make_pair_return<T>::type> makeMonoPair(T &&first,
                                                            T &&second) {
    return MonoPair<typename __make_pair_return<T>::type>(
        std::forward<T>(first), std::forward<T>(second));
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

template <typename T>
void forEach(MonoPair<T> &&pair, std::function<void(T)> f) {
    f(std::forward<T>(pair.first));
    f(std::forward<T>(pair.second));
}
