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

#include <cassert>
#include <gmpxx.h>
#include <iostream>

#include "Helper.h"

#include "llvm/ADT/APInt.h"

enum class IntType { Unbounded, Bounded };

struct Integer {
    union {
        mpz_class unbounded;
        llvm::APInt bounded;
    };
    IntType type;
    Integer() : unbounded(mpz_class(0)), type(IntType::Unbounded) {}
    explicit Integer(mpz_class i) : unbounded(std::move(i)), type(IntType::Unbounded) {}
    explicit Integer(llvm::APInt i) : bounded(i), type(IntType::Bounded) {}

    friend std::ostream &operator<<(std::ostream &os, const Integer &obj);
    Integer(const Integer &other) : type(other.type) {
        switch (type) {
        case IntType::Unbounded:
            new (&unbounded) mpz_class(other.unbounded);
            break;
        case IntType::Bounded:
            new (&bounded) llvm::APInt(other.bounded);
            break;
        }
    }
    Integer &operator=(Integer other);
    ~Integer();
    Integer asPointer() const;
    Integer &operator+=(const Integer &other) {
        assert(type == other.type);
        switch (type) {
        case IntType::Unbounded:
            unbounded += other.unbounded;
            break;
        case IntType::Bounded:
            bounded += other.bounded;
            break;
        }
        return *this;
    }
    friend Integer operator+(Integer lhs, const Integer &rhs) {
        lhs += rhs;
        return lhs;
    }
    Integer operator-() const {
        switch (type) {
        case IntType::Unbounded:
            return Integer(-unbounded);
        case IntType::Bounded:
            return Integer(-bounded);
        }
    }
    Integer &operator-=(const Integer &other) {
        assert(type == other.type);
        operator+=(-other);
        return *this;
    }
    friend Integer operator-(Integer lhs, const Integer &rhs) {
        lhs -= rhs;
        return lhs;
    }
    Integer operator/=(const Integer &other) {
        assert(type == other.type);
        switch (type) {
        case IntType::Unbounded:
            unbounded /= other.unbounded;
            break;
        case IntType::Bounded:
            logError("Use sdiv and udiv instead\n");
            exit(1);
        }
        return *this;
    }
    friend Integer operator/(Integer lhs, const Integer &rhs) {
        lhs /= rhs;
        return lhs;
    }
    Integer operator*=(const Integer &other) {
        assert(type == other.type);
        switch (type) {
        case IntType::Unbounded:
            unbounded *= other.unbounded;
            break;
        case IntType::Bounded:
            bounded *= other.bounded;
            break;
        }
        return *this;
    }
    friend Integer operator*(Integer lhs, const Integer &rhs) {
        lhs *= rhs;
        return lhs;
    }
    Integer &operator++() {
        switch (type) {
        case IntType::Unbounded:
            unbounded++;
            break;
        case IntType::Bounded:
            bounded++;
            break;
        }
        return *this;
    }
    Integer operator++(int) {
        Integer tmp(*this);
        operator++();
        return tmp;
    }
    Integer &operator--() {
        switch (type) {
        case IntType::Unbounded:
            unbounded--;
            break;
        case IntType::Bounded:
            bounded--;
            break;
        }
        return *this;
    }
    Integer operator--(int) {
        Integer tmp(*this);
        operator--();
        return tmp;
    }
    std::string get_str() const {
        switch (type) {
        case IntType::Unbounded:
            return unbounded.get_str();
        case IntType::Bounded:
            return bounded.toString(10, true);
        }
    }
    mpz_class asUnbounded() const {
        switch (type) {
        case IntType::Unbounded:
            return unbounded;
        case IntType::Bounded:
            return bounded.getSExtValue();
        }
    }
    Integer zext(unsigned width);
    Integer sext(unsigned width);
    bool eq(const Integer &rhs) const;
    bool ne(const Integer &rhs) const;
    bool ult(const Integer &rhs) const;
    bool slt(const Integer &rhs) const;
    bool ule(const Integer &rhs) const;
    bool sle(const Integer &rhs) const;
    bool ugt(const Integer &rhs) const;
    bool sgt(const Integer &rhs) const;
    bool uge(const Integer &rhs) const;
    bool sge(const Integer &rhs) const;

    Integer sdiv(const Integer &rhs) const;
    Integer udiv(const Integer &rhs) const;
    Integer srem(const Integer &rhs) const;
    Integer urem(const Integer &rhs) const;

    Integer shl(const Integer &rhs) const;
    Integer lshr(const Integer &rhs) const;
    Integer ashr(const Integer &rhs) const;
    Integer and_(const Integer &rhs) const;
    Integer or_(const Integer &rhs) const;
    Integer xor_(const Integer &rhs) const;

    Integer zextOrTrunc(unsigned width);
};

inline bool operator<(const Integer &lhs, const Integer &rhs) {
    assert(lhs.type == rhs.type);
    switch (lhs.type) {
    case IntType::Unbounded:
        return lhs.unbounded < rhs.unbounded;
    case IntType::Bounded:
        // Only used for putting it in a map
        return lhs.bounded.slt(rhs.bounded);
    }
}
inline bool operator>(const Integer &lhs, const Integer &rhs) {
    return rhs < lhs;
}

inline bool operator<=(const Integer &lhs, const Integer &rhs) {
    return !(lhs > rhs);
}

inline bool operator>=(const Integer &lhs, const Integer &rhs) {
    return !(lhs < rhs);
}

inline bool operator==(const Integer &lhs, const Integer &rhs) {
    assert(lhs.type == rhs.type);
    switch (lhs.type) {
    case IntType::Unbounded:
        return lhs.unbounded == rhs.unbounded;
    case IntType::Bounded:
        return lhs.bounded == rhs.bounded;
    }
}
inline bool operator!=(const Integer &lhs, const Integer &rhs) {
    return !(lhs == rhs);
}

llvm::APInt makeBoundedInt(unsigned numBits, int64_t i);
