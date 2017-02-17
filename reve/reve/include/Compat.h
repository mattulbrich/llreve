/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

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
