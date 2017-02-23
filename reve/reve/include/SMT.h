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
using SharedSMTRef = std::shared_ptr<const SMTExpr>;

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

class SMTExpr : public std::enable_shared_from_this<SMTExpr> {
  public:
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr &operator=(SMTExpr &) = delete;
    SMTExpr() = default;
    virtual ~SMTExpr() = default;
    virtual sexpr::SExprRef toSExpr() const = 0;
    virtual llvm::StringSet<> uses() const;
    virtual SharedSMTRef compressLets(AssignmentVec defs = {}) const;
    virtual std::vector<SharedSMTRef> splitConjunctions() const;
    // Rename assignments to unique names. This allows moving things around as
    // done by mergeImplications.
    virtual SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const;
    virtual SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const;
    virtual SharedSMTRef instantiateArrays() const;
    virtual std::unique_ptr<const HeapInfo> heapInfo() const;
    // This removes foralls and declares them as global variables. This is
    // needed for the z3 muz format.
    virtual SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) const;
    virtual SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const;
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

using SMTRef = std::unique_ptr<const SMTExpr>;
auto makeAssignment(std::string name, SharedSMTRef val)
    -> std::unique_ptr<const Assignment>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string logic) : logic(std::move(logic)) {}
    sexpr::SExprRef toSExpr() const override;
    std::string logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(SharedSMTRef expr) : expr(std::move(expr)) {}
    SharedSMTRef expr;
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    std::vector<SharedSMTRef> splitConjunctions() const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
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
    std::unique_ptr<const HeapInfo> heapInfo() const override;
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
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
    llvm::StringSet<> uses() const;
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
    SharedSMTRef expr;
    Forall(std::vector<SortedVar> vars, SharedSMTRef expr)
        : vars(std::move(vars)), expr(std::move(expr)) {}
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    std::vector<SharedSMTRef> splitConjunctions() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
};

class CheckSat : public SMTExpr {
  public:
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class GetModel : public SMTExpr {
  public:
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Let : public SMTExpr {
  public:
    AssignmentVec defs;
    SharedSMTRef expr;
    Let(AssignmentVec defs, SharedSMTRef expr)
        : defs(std::move(defs)), expr(std::move(expr)) {}
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef compressLets(AssignmentVec passedDefs) const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    std::vector<SharedSMTRef> splitConjunctions() const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
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
    sexpr::SExprRef toSExpr() const override;
};

class ConstantInt : public SMTExpr {
  public:
    llvm::APInt value;
    explicit ConstantInt(const llvm::APInt value) : value(value) {}
    sexpr::SExprRef toSExpr() const override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class ConstantBool : public SMTExpr {
  public:
    bool value;
    explicit ConstantBool(bool value) : value(value) {}
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
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
    sexpr::SExprRef toSExpr() const override; //  {
    llvm::StringSet<> uses() const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Op : public SMTExpr {
  public:
    Op(std::string opName, std::vector<SharedSMTRef> args)
        : opName(std::move(opName)), args(std::move(args)), instantiate(true) {}
    Op(std::string opName, std::vector<SharedSMTRef> args, bool instantiate)
        : opName(std::move(opName)), args(std::move(args)),
          instantiate(instantiate) {}
    std::string opName;
    std::vector<SharedSMTRef> args;
    bool instantiate;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    removeForalls(std::set<SortedVar> &introducedVariables) const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef compressLets(AssignmentVec defs) const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    std::vector<SharedSMTRef> splitConjunctions() const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
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
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
};

class BinaryFPOperator : public SMTExpr {
  public:
    enum class Opcode { FAdd, FSub, FMul, FDiv, FRem };
    Opcode op;
    std::unique_ptr<Type> type;
    SharedSMTRef op0;
    SharedSMTRef op1;
    BinaryFPOperator(Opcode op, std::unique_ptr<Type> type, SharedSMTRef op0,
                     SharedSMTRef op1)
        : op(op), type(std::move(type)), op0(op0), op1(op1) {}
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
};

class TypeCast : public SMTExpr {
  public:
    llvm::Instruction::CastOps op;
    std::unique_ptr<Type> sourceType;
    std::unique_ptr<Type> destType;
    SharedSMTRef operand;
    TypeCast(llvm::Instruction::CastOps op, std::unique_ptr<Type> sourceType,
             std::unique_ptr<Type> destType, SharedSMTRef operand)
        : op(op), sourceType(std::move(sourceType)),
          destType(std::move(destType)), operand(operand) {}
    sexpr::SExprRef toSExpr() const override;
    llvm::StringSet<> uses() const override;
    SharedSMTRef
    renameAssignments(std::map<std::string, int> variableMap) const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) const override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &,
             const llvm::StringMap<Z3DefineFun> &funMap) const override;
};

class Query : public SMTExpr {
  public:
    Query(std::string queryName) : queryName(std::move(queryName)) {}
    std::string queryName;
    sexpr::SExprRef toSExpr() const override;
};

auto stringExpr(llvm::StringRef name) -> std::unique_ptr<ConstantString>;

auto makeSMTRef(SharedSMTRef arg) -> SharedSMTRef;
auto makeSMTRef(std::string arg) -> SharedSMTRef;

template <typename... Args>
auto makeOp(std::string opName, Args... args) -> std::unique_ptr<Op> {
    std::vector<SharedSMTRef> args_ = {makeSMTRef(std::move(args))...};
    return std::make_unique<Op>(opName, args_);
}

auto makeOp(std::string opName, std::vector<std::string> args)
    -> std::unique_ptr<const Op>;

class FunDecl : public SMTExpr {
  public:
    FunDecl(std::string funName, std::vector<std::unique_ptr<Type>> inTypes,
            std::unique_ptr<Type> outType)
        : funName(std::move(funName)), inTypes(std::move(inTypes)),
          outType(std::move(outType)) {}
    std::string funName;
    std::vector<std::unique_ptr<Type>> inTypes;
    std::unique_ptr<Type> outType;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() const override;
};

class FunDef : public SMTExpr {
  public:
    FunDef(std::string funName, std::vector<SortedVar> args,
           std::unique_ptr<Type> outType, SharedSMTRef body)
        : funName(std::move(funName)), args(std::move(args)),
          outType(std::move(outType)), body(std::move(body)) {}
    std::string funName;
    std::vector<SortedVar> args;
    std::unique_ptr<Type> outType;
    SharedSMTRef body;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class Comment : public SMTExpr {
  public:
    Comment(std::string val) : val(std::move(val)) {}
    std::string val;
    sexpr::SExprRef toSExpr() const override;
};

class VarDecl : public SMTExpr {
  public:
    VarDecl(SortedVar var) : var(std::move(var)) {}
    SortedVar var;
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
}
void setSMTLexerInput(const char *input);
smt::SharedSMTRef parseSMT(const std::string &input);
