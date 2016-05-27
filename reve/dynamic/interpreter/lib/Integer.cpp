#include "Integer.h"

#include <cassert>

Integer &Integer::operator=(Integer other) {
    type = other.type;
    switch (type) {
    case IntType::Unbounded:
        swap(unbounded, other.unbounded);
        break;
    case IntType::Bounded:
        bounded = other.bounded;
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
        return unbounded < rhs.unbounded;
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
        return unbounded <= rhs.unbounded;
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
        return unbounded > rhs.unbounded;
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
        return unbounded >= rhs.unbounded;
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
