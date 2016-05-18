#pragma once

#include <algorithm>
#include <iterator>
#include <set>

// Used to silence unused variable warnings when something is only used in an
// assert
#define unused(x) ((void)(x))

template <class T> class Reverse {
  private:
    T t;

  public:
    using iterator = typename T::reverse_iterator;
    using value_type = typename T::value_type;
    Reverse(T t) : t(t) {}
    auto begin() -> decltype(t.rbegin()) { return t.rbegin(); }
    auto end() -> decltype(t.rend()) { return t.rend(); }
};

template <class T> Reverse<T> makeReverse(T t) { return Reverse<T>(t); }

template <typename A, typename B> class Zip {
  public:
    class iterator
        : std::iterator<
              std::forward_iterator_tag,
              std::pair<typename A::value_type, typename B::value_type>> {

      public:
        std::pair<typename A::iterator, typename B::iterator> Cur;
        iterator(typename A::iterator a, typename B::iterator b)
            : Cur(std::make_pair(a, b)) {}
        iterator(const iterator &rhs) : Cur(rhs.Cur) {}
        bool operator!=(const iterator &rhs) {
            return Cur.first != rhs.Cur.first && Cur.second != rhs.Cur.second;
        }
        iterator &operator++() {
            Cur.first++;
            Cur.second++;
            return *this;
        }
        typename iterator::value_type operator*() {
            return std::make_pair(*Cur.first, *Cur.second);
        }
    };
    A a;
    B b;
    Zip<A, B>::iterator begin() {
        return Zip<A, B>::iterator(a.begin(), b.begin());
    }
    Zip<A, B>::iterator end() { return Zip<A, B>::iterator(a.end(), b.end()); }
    Zip(A a, B b) : a(a), b(b) {}
};

template <typename A, typename B> Zip<A, B> makeZip(A a, B b) {
    return Zip<A, B>(a, b);
}

template <typename A>
std::set<A> intersection(std::set<A> SetA, std::set<A> SetB) {
    std::set<A> Ret;
    std::set_intersection(SetA.begin(), SetA.end(), SetB.begin(), SetB.end(),
                          std::inserter(Ret, Ret.begin()));
    return Ret;
}

template <typename A> std::set<A> immutableInsert(std::set<A> Set, A El) {
    std::set<A> SetNew = Set;
    SetNew.insert(El);
    return SetNew;
}
