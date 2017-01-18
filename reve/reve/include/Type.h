#pragma once

#include "SExpr.h"

#include "llvm/IR/Type.h"

namespace smt {
enum class TypeTag { Bool, Int, Float, Array };

struct Type {
    virtual ~Type() = default;
    // Used for safe casting without rtti
    virtual TypeTag getTag() const = 0;
    virtual sexpr::SExprRef toSExpr() const = 0;
    virtual std::unique_ptr<Type> copy() const = 0;
};

struct BoolType : Type {
    TypeTag getTag() const override;
    sexpr::SExprRef toSExpr() const override;
    std::unique_ptr<Type> copy() const override;
};

struct IntType : Type {
    unsigned bitWidth;
    explicit IntType(unsigned bitWidth) : bitWidth(bitWidth) {}
    TypeTag getTag() const override;
    sexpr::SExprRef toSExpr() const override;
    std::unique_ptr<Type> copy() const override;
};

struct FloatType : Type {
    unsigned exponentWidth;
    unsigned significandWidth;
    explicit FloatType(unsigned exponentWidth, unsigned significandWidth)
        : exponentWidth(exponentWidth), significandWidth(significandWidth) {}
    TypeTag getTag() const override;
    sexpr::SExprRef toSExpr() const override;
    std::unique_ptr<Type> copy() const override;
};

struct ArrayType : Type {
    std::unique_ptr<Type> domain;
    std::unique_ptr<Type> target;
    explicit ArrayType(std::unique_ptr<Type> domain,
                       std::unique_ptr<Type> target)
        : domain(std::move(domain)), target(std::move(target)) {}
    TypeTag getTag() const override;
    sexpr::SExprRef toSExpr() const override;
    std::unique_ptr<Type> copy() const override;
};

auto memoryType() -> std::unique_ptr<ArrayType>;
auto int64Type() -> std::unique_ptr<IntType>;
auto boolType() -> std::unique_ptr<BoolType>;
auto pointerType() -> std::unique_ptr<IntType>;

auto llvmType(const llvm::Type *type) -> std::unique_ptr<Type>;
// This function needs to die
auto inferTypeByName(std::string name) -> std::unique_ptr<Type>;
}
