#pragma once

#include "SExpr.h"

#include "llvm/IR/Type.h"

namespace smt {
enum class TypeTag { Bool, Int, Float, Array };

// This is modeled via the ideas from Sean Parent’s talk “Inheritance is the
// Base Class of Evil”. The main advantage is that we get value semantics and
// don’t need to deal with copying ptrs or using shared ptrs.
struct Type {
    template <typename T> Type(T ty) : self(new Model<T>(std::move(ty))) {}
    Type(const Type &other) : self(other.self->copy()) {}
    Type &operator=(const Type &other) {
        Type tmp(other);
        *this = std::move(tmp);
        return *this;
    }
    Type &operator=(Type &&) noexcept = default;

    TypeTag getTag() const { return self->getTag(); }
    sexpr::SExprRef toSExpr() const { return self->toSExpr(); }
    unsigned unsafeBitWidth() const { return self->unsafeBitWidth(); }

  private:
    struct Concept {
        virtual ~Concept() = default;
        virtual Concept *copy() const = 0;
        virtual TypeTag getTag() const = 0;
        virtual sexpr::SExprRef toSExpr() const = 0;
        virtual unsigned unsafeBitWidth() const = 0;
    };

    template <typename T> struct Model : Concept {
        T data;
        Model(T x) : data(std::move(x)) {}
        Concept *copy() const override { return new Model(*this); }
        TypeTag getTag() const override { return data.getTag(); }
        sexpr::SExprRef toSExpr() const override { return data.toSExpr(); }
        unsigned unsafeBitWidth() const override {
            return data.unsafeBitWidth();
        }
    };

    std::unique_ptr<const Concept> self;
};

struct BoolType {
    TypeTag getTag() const;
    sexpr::SExprRef toSExpr() const;
    unsigned unsafeBitWidth() const {
        assert(false && "unsafeBitWidth() can only be called on an IntType");
        return 0;
    }
};

struct IntType {
    unsigned bitWidth;
    explicit IntType(unsigned bitWidth) : bitWidth(bitWidth) {}
    TypeTag getTag() const;
    sexpr::SExprRef toSExpr() const;
    unsigned unsafeBitWidth() const { return bitWidth; }
};

struct FloatType {
    unsigned exponentWidth;
    unsigned significandWidth;
    explicit FloatType(unsigned exponentWidth, unsigned significandWidth)
        : exponentWidth(exponentWidth), significandWidth(significandWidth) {}
    TypeTag getTag() const;
    sexpr::SExprRef toSExpr() const;
    unsigned unsafeBitWidth() const {
        assert(false && "unsafeBitWidth() can only be called on an IntType");
        return 0;
    }
};

struct ArrayType {
    Type domain;
    Type target;
    explicit ArrayType(Type domain, Type target)
        : domain(std::move(domain)), target(std::move(target)) {}
    TypeTag getTag() const;
    sexpr::SExprRef toSExpr() const;
    unsigned unsafeBitWidth() const {
        assert(false && "unsafeBitWidth() can only be called on an IntType");
        return 0;
    }
};

auto memoryType() -> ArrayType;
auto int64Type() -> IntType;
auto boolType() -> BoolType;
auto pointerType() -> IntType;

auto llvmType(const llvm::Type *type) -> Type;
// This function needs to die
auto inferTypeByName(std::string name) -> Type;
}
