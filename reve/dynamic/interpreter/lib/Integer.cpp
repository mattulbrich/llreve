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
