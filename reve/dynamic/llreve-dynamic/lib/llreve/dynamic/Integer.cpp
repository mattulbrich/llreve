/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Integer.h"

#include <cassert>

using namespace llreve::opts;

Integer &Integer::operator=(Integer other) {
    switch (type) {
    case IntType::Unbounded:
        unbounded.~mpz_class();
        break;
    case IntType::Bounded:
        bounded.~APInt();
        break;
    }
    type = other.type;
    switch (type) {
    case IntType::Unbounded:
        new (&unbounded) mpz_class(other.unbounded);
        break;
    case IntType::Bounded:
        new (&bounded) llvm::APInt(other.bounded);
        break;
    }
    return *this;
}

Integer::~Integer() {
    switch (type) {
    case IntType::Unbounded:
        unbounded.~mpz_class();
        break;
    case IntType::Bounded:
        bounded.~APInt();
        break;
    }
}

std::ostream &operator<<(std::ostream &os, const Integer &obj) {
    std::string prefix;
    switch (obj.type) {
    case IntType::Unbounded:
        prefix = "unbounded_";
        break;
    case IntType::Bounded:
        prefix = "bounded" + std::to_string(obj.bounded.getBitWidth()) + "_";
        break;
    }
    os << prefix << obj.get_str();
    return os;
}

Integer Integer::zext(unsigned width) {
    Integer res(*this);
    switch (res.type) {
    case IntType::Unbounded:
        break;
    case IntType::Bounded:
        res.bounded = res.bounded.zext(width);
        break;
    }
    return res;
}

Integer Integer::zextOrTrunc(unsigned width) {
    Integer res(*this);
    switch (res.type) {
    case IntType::Unbounded:
        break;
    case IntType::Bounded:
        res.bounded = res.bounded.zextOrTrunc(width);
        break;
    }
    return res;
}

Integer Integer::sext(unsigned width) {
    Integer res(*this);
    switch (res.type) {
    case IntType::Unbounded:
        break;
    case IntType::Bounded:
        res.bounded = res.bounded.sext(width);
        break;
    }
    return res;
}

bool Integer::eq(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded == rhs.unbounded;
    case IntType::Bounded:
        return bounded.eq(rhs.bounded);
    }
}
bool Integer::ne(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded != rhs.unbounded;
    case IntType::Bounded:
        return bounded.ne(rhs.bounded);
    }
}
bool Integer::ult(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        if (SMTGenerationOpts::getInstance().EverythingSigned) {
            return unbounded < rhs.unbounded;
        }
        return abs(unbounded) < abs(rhs.unbounded);
    case IntType::Bounded:
        return bounded.ult(rhs.bounded);
    }
}
bool Integer::slt(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded < rhs.unbounded;
    case IntType::Bounded:
        return bounded.slt(rhs.bounded);
    }
}
bool Integer::ule(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        if (SMTGenerationOpts::getInstance().EverythingSigned) {
            return unbounded <= rhs.unbounded;
        }
        return abs(unbounded) <= abs(rhs.unbounded);
    case IntType::Bounded:
        return bounded.ule(rhs.bounded);
    }
}
bool Integer::sle(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded <= rhs.unbounded;
    case IntType::Bounded:
        return bounded.sle(rhs.bounded);
    }
}
bool Integer::ugt(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        if (SMTGenerationOpts::getInstance().EverythingSigned) {
            return unbounded > rhs.unbounded;
        }
        return abs(unbounded) > abs(rhs.unbounded);
    case IntType::Bounded:
        return bounded.ugt(rhs.bounded);
    }
}
bool Integer::sgt(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded > rhs.unbounded;
    case IntType::Bounded:
        return bounded.sgt(rhs.bounded);
    }
}
bool Integer::uge(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        if (SMTGenerationOpts::getInstance().EverythingSigned) {
            return unbounded >= rhs.unbounded;
        }
        return abs(unbounded) >= abs(rhs.unbounded);
    case IntType::Bounded:
        return bounded.uge(rhs.bounded);
    }
}
bool Integer::sge(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return unbounded >= rhs.unbounded;
    case IntType::Bounded:
        return bounded.sge(rhs.bounded);
    }
}

Integer Integer::sdiv(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return Integer(unbounded / rhs.unbounded);
    case IntType::Bounded:
        return Integer(bounded.sdiv(rhs.bounded));
    }
}
Integer Integer::udiv(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return Integer(unbounded / rhs.unbounded);
    case IntType::Bounded:
        return Integer(bounded.udiv(rhs.bounded));
    }
}
Integer Integer::srem(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return Integer(unbounded % rhs.unbounded);
    case IntType::Bounded:
        return Integer(bounded.srem(rhs.bounded));
    }
}
Integer Integer::urem(const Integer &rhs) const {
    assert(type == rhs.type);
    switch (type) {
    case IntType::Unbounded:
        return Integer(unbounded % rhs.unbounded);
    case IntType::Bounded:
        return Integer(bounded.urem(rhs.bounded));
    }
}

Integer Integer::shl(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.shl(rhs.bounded));
}
Integer Integer::lshr(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.lshr(rhs.bounded));
}
Integer Integer::ashr(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.ashr(rhs.bounded));
}
Integer Integer::and_(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.And(rhs.bounded));
}
Integer Integer::or_(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.Or(rhs.bounded));
}
Integer Integer::xor_(const Integer &rhs) const {
    assert(type == IntType::Bounded);
    assert(type == IntType::Bounded);
    return Integer(bounded.Xor(rhs.bounded));
}

Integer Integer::asPointer() const {
    if (!SMTGenerationOpts::getInstance().BitVect) {
        return Integer(asUnbounded());
    }
    switch (type) {
    case IntType::Bounded:
        assert(bounded.getBitWidth() <= 64);
        if (bounded.getBitWidth() == 64) {
            return *this;
        }
        return Integer(bounded.sext(64));
    case IntType::Unbounded:
        assert(unbounded.fits_slong_p());
        return Integer(makeBoundedInt(64, unbounded.get_si()));
    }
}

llvm::APInt makeBoundedInt(unsigned numBits, int64_t val) {
    llvm::APInt ret(numBits, static_cast<uint64_t>(val));
    if (val < 0) {
        return -ret;
    }
    return ret;
}
