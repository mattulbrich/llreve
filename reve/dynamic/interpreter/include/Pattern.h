#pragma once

#include <list>

#include "Helper.h"
#include "Interpreter.h"
#include "MonoPair.h"

namespace pattern {
enum class Placeholder { Variable, Constant };
 enum class Operation { Eq, Add, Mul, LE };
enum class ExprType { BinOp, Val };
using VecIter = typename std::vector<VarIntVal>::iterator;

struct InstantiatedValue {
    virtual Placeholder getType() const = 0;
    virtual ~InstantiatedValue();
    virtual VarIntVal getValue(VarMap<std::string> varVals) const = 0;
};
struct Constant : InstantiatedValue {
    VarIntVal val;
    Constant(VarIntVal val) : val(val) {}
    Placeholder getType() const override;
    VarIntVal getValue(VarMap<std::string> varVals) const override;
};
struct Variable : InstantiatedValue {
    std::string name;
    Variable(std::string name) : name(name) {}
    Placeholder getType() const override;
    VarIntVal getValue(VarMap<std::string> varVals) const override;
};

struct Expr {
    virtual ExprType getType() const = 0;
    virtual ~Expr() = default;
    bool matches(std::vector<VarIntVal> vec) const {
        return matches(vec.begin(), vec.end());
    }
    virtual bool matches(VecIter begin, VecIter end) const = 0;
    virtual VarIntVal eval(VecIter begin, VecIter end) const = 0;
    virtual size_t arguments() const = 0;
    virtual size_t variables() const = 0;
    virtual std::ostream &
    dump(std::ostream &os,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator begin,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator end)
        const = 0;
    virtual std::ostream &
    dump(std::ostream &os,
         std::vector<std::shared_ptr<InstantiatedValue>> vec) const;
    virtual std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiate(std::vector<std::string> variables,
                VarMap<std::string> variableValues) const = 0;
    virtual std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiateToValue(std::vector<std::string> variables,
                       VarMap<std::string> variableValues,
                       VarIntVal value) const = 0;
};

struct BinaryOp : Expr {
    Operation op;
    MonoPair<std::shared_ptr<Expr>> args;
    BinaryOp(Operation op, std::shared_ptr<Expr> arg1,
             std::shared_ptr<Expr> arg2)
        : op(op), args(makeMonoPair(arg1, arg2)) {}
    ExprType getType() const override { return ExprType::BinOp; }
    bool matches(VecIter begin, VecIter end) const override;
    VarIntVal eval(VecIter begin, VecIter end) const override;
    size_t arguments() const override;
    size_t variables() const override;
    std::ostream &
    dump(std::ostream &os,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator begin,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator end)
        const override;
    std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiate(std::vector<std::string> variables,
                VarMap<std::string> variableValues) const override;
    std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiateToValue(std::vector<std::string> variables,
                       VarMap<std::string> variableValues,
                       VarIntVal value) const override;
};

struct Value : Expr {
    Placeholder val;
    explicit Value(Placeholder val) : val(val) {}
    ExprType getType() const override { return ExprType::Val; }
    bool matches(VecIter begin, VecIter end) const override;
    VarIntVal eval(VecIter begin, VecIter end) const override;
    size_t arguments() const override;
    size_t variables() const override;
    std::ostream &
    dump(std::ostream &os,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator begin,
         std::vector<std::shared_ptr<InstantiatedValue>>::iterator end)
        const override;
    std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiate(std::vector<std::string> variables,
                VarMap<std::string> variableValues) const override;
    std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
    instantiateToValue(std::vector<std::string> variables,
                       VarMap<std::string> variableValues,
                       VarIntVal value) const override;
};

struct CombineResult {
    llvm::Optional<VarIntVal> value;
    bool alwaysTrue;
    CombineResult(VarIntVal value) : value(value), alwaysTrue(false) {}
    CombineResult(bool alwaysTrue)
        : value(llvm::Optional<VarIntVal>()), alwaysTrue(alwaysTrue) {}
};

// Goes through each instantiation of pat and calculates its value.
// That value is then used to find all instantiations of otherPat whose value is
// the result of applying the
// supplied function to (value,patResult).
std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
instantiateBinaryOperation(
    const Expr &pat, const Expr &otherPat, std::vector<std::string> variables,
    VarMap<std::string> variableValues,
    std::function<llvm::Optional<VarIntVal>(VarIntVal, VarIntVal)>
        combineValues,
    VarIntVal value, bool otherPatFirst);
// Variant of the above where the operation can always be inverted
std::list<std::vector<std::shared_ptr<InstantiatedValue>>>
instantiateBijectiveBinaryOperation(
    const Expr &pat, const Expr &otherPat, std::vector<std::string> variables,
    VarMap<std::string> variableValues,
    std::function<VarIntVal(VarIntVal, VarIntVal)> combineValues,
    VarIntVal value, bool otherPatFirst);
}
