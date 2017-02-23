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

#include "SExpr.h"
#include "Type.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/Instruction.h"

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "z3++.h"

namespace smt {

// forward declare
class SortedVar;
class SMTExpr;
using SharedSMTRef = std::shared_ptr<SMTExpr>;

using Assignment = std::pair<std::string, SharedSMTRef>;
using AssignmentVec = llvm::SmallVector<Assignment, 3>;

struct HeapInfo {
    std::string arrayName;
    std::string index;
    std::string suffix;
    HeapInfo(std::string arrayName, std::string index, std::string suffix)
        : arrayName(arrayName), index(index), suffix(suffix) {}
};

struct Z3DefineFun {
    z3::expr_vector vars;
    z3::expr e;
};

class SetLogic;
class Assert;
class TypedVariable;
class Forall;
class CheckSat;
class GetModel;
class Let;
class ConstantFP;
class ConstantInt;
class ConstantBool;
class ConstantString;
class Op;
class FPCmp;
class BinaryFPOperator;
class TypeCast;
class Query;
class FunDecl;
class FunDef;
class Comment;
class VarDecl;

struct BottomUpVisitor {
    virtual void dispatch(SetLogic &expr) = 0;
    virtual void dispatch(Assert &expr) = 0;
    virtual void dispatch(TypedVariable &expr) = 0;
    virtual void dispatch(Forall &expr) = 0;
    virtual void dispatch(CheckSat &expr) = 0;
    virtual void dispatch(GetModel &expr) = 0;
    virtual void dispatch(Let &expr) = 0;
    virtual void dispatch(ConstantFP &expr) = 0;
    virtual void dispatch(ConstantInt &expr) = 0;
    virtual void dispatch(ConstantBool &expr) = 0;
    virtual void dispatch(ConstantString &expr) = 0;
    virtual void dispatch(Op &expr) = 0;
    virtual void dispatch(FPCmp &expr) = 0;
    virtual void dispatch(BinaryFPOperator &expr) = 0;
    virtual void dispatch(TypeCast &expr) = 0;
    virtual void dispatch(Query &expr) = 0;
    virtual void dispatch(FunDecl &expr) = 0;
    virtual void dispatch(FunDef &expr) = 0;
    virtual void dispatch(Comment &expr) = 0;
    virtual void dispatch(VarDecl &expr) = 0;
};

struct NoopBottomUpVisitor : BottomUpVisitor {
    virtual void dispatch(SetLogic &expr) override { return; }
    virtual void dispatch(Assert &expr) override { return; }
    virtual void dispatch(TypedVariable &expr) override { return; }
    virtual void dispatch(Forall &expr) override { return; }
    virtual void dispatch(CheckSat &expr) override { return; }
    virtual void dispatch(GetModel &expr) override { return; }
    virtual void dispatch(Let &expr) override { return; }
    virtual void dispatch(ConstantFP &expr) override { return; }
    virtual void dispatch(ConstantInt &expr) override { return; }
    virtual void dispatch(ConstantBool &expr) override { return; }
    virtual void dispatch(ConstantString &expr) override { return; }
    virtual void dispatch(Op &expr) override { return; }
    virtual void dispatch(FPCmp &expr) override { return; }
    virtual void dispatch(BinaryFPOperator &expr) override { return; }
    virtual void dispatch(TypeCast &expr) override { return; }
    virtual void dispatch(Query &expr) override { return; }
    virtual void dispatch(FunDecl &expr) override { return; }
    virtual void dispatch(FunDef &expr) override { return; }
    virtual void dispatch(Comment &expr) override { return; }
    virtual void dispatch(VarDecl &expr) override { return; }
};

class SMTExpr : public std::enable_shared_from_this<SMTExpr> {
  public:
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr &operator=(SMTExpr &) = delete;
    SMTExpr() = default;
    virtual ~SMTExpr() = default;
    virtual void acceptBottomUp(BottomUpVisitor &visitor) = 0;
    virtual sexpr::SExprRef toSExpr() const = 0;
    virtual SharedSMTRef compressLets(AssignmentVec defs = {});
    virtual std::vector<SharedSMTRef> splitConjunctions();
    // Rename assignments to unique names. This allows moving things around as
    // done by mergeImplications.
    virtual SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap);
    virtual SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions);
    virtual SharedSMTRef instantiateArrays();
    virtual std::unique_ptr<const HeapInfo> heapInfo() const;
    // This removes foralls and declares them as global variables. This is
    // needed for the z3 muz format.
    virtual SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables);
    virtual SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments);
    virtual void toZ3(z3::context &cxt, z3::solver &solver,
                      llvm::StringMap<z3::expr> &nameMap,
                      llvm::StringMap<Z3DefineFun> &defineFunMap) const;
    virtual z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const;
    // Needed because we compile without rtti and thereby can’t use a dynamic
    // cast to check the type
    virtual bool isConstantFalse() const { return false; }
};

using SMTRef = std::unique_ptr<SMTExpr>;
auto makeAssignment(std::string name, SharedSMTRef val)
    -> std::unique_ptr<Assignment>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string logic) : logic(std::move(logic)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    std::string logic;
};

class Assert : public SMTExpr {
  public:
    std::shared_ptr<SMTExpr> expr;
    explicit Assert(std::shared_ptr<SMTExpr> expr) : expr(std::move(expr)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) override;
    std::vector<SharedSMTRef> splitConjunctions() override;
    SharedSMTRef instantiateArrays() override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

// TypedVariable is simply a reference to a variable with a type attached to it,
// SortedVar is used in binders where the type should also be serialized, e.g.
// forall
class TypedVariable : public SMTExpr {
  public:
    std::string name;
    std::unique_ptr<Type> type;
    TypedVariable(std::string name, std::unique_ptr<Type> type)
        : name(std::move(name)), type(std::move(type)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    std::unique_ptr<const HeapInfo> heapInfo() const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class SortedVar {
  public:
    std::string name;
    std::unique_ptr<Type> type;
    SortedVar(std::string name, std::unique_ptr<Type> type)
        : name(std::move(name)), type(std::move(type)) {}
    sexpr::SExprRef toSExpr() const;
    SortedVar &operator=(const SortedVar &other) {
        name = other.name;
        type = other.type->copy();
        return *this;
    }
    SortedVar(const SortedVar &other)
        : name(other.name), type(other.type->copy()) {}
};

inline bool operator<(const SortedVar &lhs, const SortedVar &rhs) {
    return lhs.name < rhs.name;
}

inline bool operator>(const SortedVar &lhs, const SortedVar &rhs) {
    return rhs < lhs;
}

inline bool operator<=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs > rhs);
}

inline bool operator>=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs < rhs);
}

inline bool operator==(const SortedVar &lhs, const SortedVar &rhs) {
    return lhs.name == rhs.name;
}

inline bool operator!=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs == rhs);
}

class Forall : public SMTExpr {
  public:
    std::vector<SortedVar> vars;
    std::shared_ptr<SMTExpr> expr;
    Forall(std::vector<SortedVar> vars, std::shared_ptr<SMTExpr> expr)
        : vars(std::move(vars)), expr(std::move(expr)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    SharedSMTRef instantiateArrays() override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) override;
    std::vector<SharedSMTRef> splitConjunctions() override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class CheckSat : public SMTExpr {
  public:
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class GetModel : public SMTExpr {
  public:
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Let : public SMTExpr {
  public:
    AssignmentVec defs;
    std::shared_ptr<SMTExpr> expr;
    Let(AssignmentVec defs, std::shared_ptr<SMTExpr> expr)
        : defs(std::move(defs)), expr(std::move(expr)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) override;
    SharedSMTRef compressLets(AssignmentVec passedDefs) override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) override;
    std::vector<SharedSMTRef> splitConjunctions() override;
    SharedSMTRef instantiateArrays() override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

// We could unify these in a generic type but it’s probably not worth the
// trouble
class ConstantFP : public SMTExpr {
  public:
    llvm::APFloat value;
    explicit ConstantFP(const llvm::APFloat value) : value(value) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
};

class ConstantInt : public SMTExpr {
  public:
    llvm::APInt value;
    explicit ConstantInt(const llvm::APInt value) : value(value) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class ConstantBool : public SMTExpr {
  public:
    bool value;
    explicit ConstantBool(bool value) : value(value) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
    bool isConstantFalse() const override { return !value; }
};

// This is for constants or expressions that have not been parsed and should
// just be included literally
class ConstantString : public SMTExpr {
  public:
    std::string value;
    explicit ConstantString(std::string value) : value(value) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override; //  {
    SharedSMTRef compressLets(AssignmentVec defs) override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Op : public SMTExpr {
  public:
    std::string opName;
    std::vector<std::shared_ptr<SMTExpr>> args;
    // whether to instantiate arrays for eldarica or not
    bool instantiate;
    Op(std::string opName, std::vector<std::shared_ptr<SMTExpr>> args)
        : opName(std::move(opName)), args(std::move(args)), instantiate(true) {}
    Op(std::string opName, std::vector<std::shared_ptr<SMTExpr>> args,
       bool instantiate)
        : opName(std::move(opName)), args(std::move(args)),
          instantiate(instantiate) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) override;
    SharedSMTRef compressLets(AssignmentVec defs) override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) override;
    std::vector<SharedSMTRef> splitConjunctions() override;
    SharedSMTRef instantiateArrays() override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class FPCmp : public SMTExpr {
  public:
    enum class Predicate {
        False,
        OEQ,
        OGT,
        OGE,
        OLT,
        OLE,
        ONE,
        ORD,
        UNO,
        UEQ,
        UGT,
        UGE,
        ULT,
        ULE,
        UNE,
        True
    };
    // Operations that take two floats and return a bool
    Predicate op;
    // This is the type of the two arguments that an fcmp instruction retrieves
    // (they have to be identical)
    std::unique_ptr<Type> type;
    SharedSMTRef op0;
    SharedSMTRef op1;
    FPCmp(Predicate op, std::unique_ptr<Type> type, SharedSMTRef op0,
          SharedSMTRef op1)
        : op(op), type(std::move(type)), op0(op0), op1(op1) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class BinaryFPOperator : public SMTExpr {
  public:
    enum class Opcode { FAdd, FSub, FMul, FDiv, FRem };
    Opcode op;
    std::unique_ptr<Type> type;
    std::shared_ptr<SMTExpr> op0;
    std::shared_ptr<SMTExpr> op1;
    BinaryFPOperator(Opcode op, std::unique_ptr<Type> type,
                     std::shared_ptr<SMTExpr> op0, std::shared_ptr<SMTExpr> op1)
        : op(std::move(op)), type(std::move(type)), op0(std::move(op0)),
          op1(std::move(op1)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class TypeCast : public SMTExpr {
  public:
    llvm::Instruction::CastOps op;
    std::unique_ptr<Type> sourceType;
    std::unique_ptr<Type> destType;
    std::shared_ptr<SMTExpr> operand;

    TypeCast(llvm::Instruction::CastOps op, std::unique_ptr<Type> sourceType,
             std::unique_ptr<Type> destType, std::shared_ptr<SMTExpr> operand)
        : op(std::move(op)), sourceType(std::move(sourceType)),
          destType(std::move(destType)), operand(std::move(operand)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &,
             const llvm::StringMap<Z3DefineFun> &funMap) const override;
};

class Query : public SMTExpr {
    std::string queryName;

  public:
    Query(std::string queryName) : queryName(std::move(queryName)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
};

auto stringExpr(llvm::StringRef name) -> std::unique_ptr<ConstantString>;

auto makeSMTRef(std::shared_ptr<SMTExpr> arg) -> std::shared_ptr<SMTExpr>;
auto makeSMTRef(std::string arg) -> std::shared_ptr<SMTExpr>;

template <typename... Args>
auto makeOp(std::string opName, Args... args) -> std::unique_ptr<Op> {
    std::vector<std::shared_ptr<SMTExpr>> args_ = {
        makeSMTRef(std::move(args))...};
    return std::make_unique<Op>(opName, args_);
}

auto makeOp(std::string opName, std::vector<std::string> args)
    -> std::unique_ptr<const Op>;

class FunDecl : public SMTExpr {
  public:
    std::string funName;
    std::vector<std::unique_ptr<Type>> inTypes;
    std::unique_ptr<Type> outType;

    FunDecl(std::string funName, std::vector<std::unique_ptr<Type>> inTypes,
            std::unique_ptr<Type> outType)
        : funName(std::move(funName)), inTypes(std::move(inTypes)),
          outType(std::move(outType)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() override;
};

class FunDef : public SMTExpr {
  public:
    std::string funName;
    std::vector<SortedVar> args;
    std::unique_ptr<Type> outType;
    std::shared_ptr<SMTExpr> body;

    FunDef(std::string funName, std::vector<SortedVar> args,
           std::unique_ptr<Type> outType, std::shared_ptr<SMTExpr> body)
        : funName(std::move(funName)), args(std::move(args)),
          outType(std::move(outType)), body(std::move(body)) {}

    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Comment : public SMTExpr {
  public:
    std::string val;

    Comment(std::string val) : val(std::move(val)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
};

class VarDecl : public SMTExpr {
  public:
    SortedVar var;

    VarDecl(SortedVar var) : var(std::move(var)) {}
    void acceptBottomUp(BottomUpVisitor &visitor) override;
    sexpr::SExprRef toSExpr() const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

auto nestLets(SharedSMTRef clause, llvm::ArrayRef<Assignment> defs)
    -> SharedSMTRef;

auto fastNestLets(SharedSMTRef clause, llvm::ArrayRef<Assignment> defs)
    -> SharedSMTRef;

bool isArray(const Type &type);

std::unique_ptr<SMTExpr> memoryVariable(std::string name);
std::unique_ptr<TypedVariable> typedVariableFromSortedVar(const SortedVar &var);
SortedVar sortedVarFromTypedVariable(const TypedVariable &var);
}
void setSMTLexerInput(const char *input);
smt::SharedSMTRef parseSMT(const std::string &input);
