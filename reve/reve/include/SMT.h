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

struct TopDownVisitor;
class SMTExpr : public std::enable_shared_from_this<SMTExpr> {
  public:
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr &operator=(SMTExpr &) = delete;
    SMTExpr() = default;
    virtual ~SMTExpr() = default;
    virtual std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const = 0;
    virtual sexpr::SExprRef toSExpr() const = 0;
    virtual std::vector<SharedSMTRef> splitConjunctions();
    // TODO implement using visitor
    virtual SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions);
    // TODO implement using visitor
    virtual SharedSMTRef instantiateArrays();
    virtual std::unique_ptr<const HeapInfo> heapInfo() const;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    std::string logic;
};

class Assert : public SMTExpr {
  public:
    std::shared_ptr<SMTExpr> expr;
    explicit Assert(std::shared_ptr<SMTExpr> expr) : expr(std::move(expr)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    Type type;
    TypedVariable(std::string name, Type type)
        : name(std::move(name)), type(std::move(type)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    std::unique_ptr<const HeapInfo> heapInfo() const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class SortedVar {
  public:
    std::string name;
    Type type;
    SortedVar(std::string name, Type type)
        : name(std::move(name)), type(std::move(type)) {}
    sexpr::SExprRef toSExpr() const;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) override;
    std::vector<SharedSMTRef> splitConjunctions() override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class CheckSat : public SMTExpr {
  public:
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class GetModel : public SMTExpr {
  public:
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
};

class ConstantInt : public SMTExpr {
  public:
    llvm::APInt value;
    explicit ConstantInt(const llvm::APInt value) : value(value) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    z3::expr
    toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
             const llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

class ConstantBool : public SMTExpr {
  public:
    bool value;
    explicit ConstantBool(bool value) : value(value) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override; //  {
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    Type type;
    SharedSMTRef op0;
    SharedSMTRef op1;
    FPCmp(Predicate op, Type type, SharedSMTRef op0, SharedSMTRef op1)
        : op(op), type(std::move(type)), op0(op0), op1(op1) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class BinaryFPOperator : public SMTExpr {
  public:
    enum class Opcode { FAdd, FSub, FMul, FDiv, FRem };
    Opcode op;
    Type type;
    std::shared_ptr<SMTExpr> op0;
    std::shared_ptr<SMTExpr> op1;
    BinaryFPOperator(Opcode op, Type type, std::shared_ptr<SMTExpr> op0,
                     std::shared_ptr<SMTExpr> op1)
        : op(std::move(op)), type(std::move(type)), op0(std::move(op0)),
          op1(std::move(op1)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef
    inlineLets(std::map<std::string, SharedSMTRef> assignments) override;
};

class TypeCast : public SMTExpr {
  public:
    llvm::Instruction::CastOps op;
    Type sourceType;
    Type destType;
    std::shared_ptr<SMTExpr> operand;

    TypeCast(llvm::Instruction::CastOps op, Type sourceType, Type destType,
             std::shared_ptr<SMTExpr> operand)
        : op(std::move(op)), sourceType(std::move(sourceType)),
          destType(std::move(destType)), operand(std::move(operand)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
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
    std::vector<Type> inTypes;
    Type outType;

    FunDecl(std::string funName, std::vector<Type> inTypes, Type outType)
        : funName(std::move(funName)), inTypes(std::move(inTypes)),
          outType(std::move(outType)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() override;
};

class FunDef : public SMTExpr {
  public:
    std::string funName;
    std::vector<SortedVar> args;
    Type outType;
    std::shared_ptr<SMTExpr> body;

    FunDef(std::string funName, std::vector<SortedVar> args, Type outType,
           std::shared_ptr<SMTExpr> body)
        : funName(std::move(funName)), args(std::move(args)),
          outType(std::move(outType)), body(std::move(body)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
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
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
};

class VarDecl : public SMTExpr {
  public:
    SortedVar var;

    VarDecl(SortedVar var) : var(std::move(var)) {}
    std::shared_ptr<SMTExpr> accept(TopDownVisitor &visitor) const override;
    sexpr::SExprRef toSExpr() const override;
    void toZ3(z3::context &cxt, z3::solver &solver,
              llvm::StringMap<z3::expr> &nameMap,
              llvm::StringMap<Z3DefineFun> &defineFunMap) const override;
};

struct TopDownVisitor {
    bool ignoreLetBindings = false;
    TopDownVisitor() = default;
    TopDownVisitor(bool ignoreLetBindings)
        : ignoreLetBindings(ignoreLetBindings) {}
    virtual void dispatch(SetLogic &expr) {}
    virtual void dispatch(Assert &expr) {}
    virtual void dispatch(TypedVariable &expr) {}
    virtual void dispatch(Forall &expr) {}
    virtual void dispatch(CheckSat &expr) {}
    virtual void dispatch(GetModel &expr) {}
    virtual void dispatch(Let &expr) {}
    virtual void dispatch(ConstantFP &expr) {}
    virtual void dispatch(ConstantInt &expr) {}
    virtual void dispatch(ConstantBool &expr) {}
    virtual void dispatch(ConstantString &expr) {}
    virtual void dispatch(Op &expr) {}
    virtual void dispatch(FPCmp &expr) {}
    virtual void dispatch(BinaryFPOperator &expr) {}
    virtual void dispatch(TypeCast &expr) {}
    virtual void dispatch(Query &expr) {}
    virtual void dispatch(FunDecl &expr) {}
    virtual void dispatch(FunDef &expr) {}
    virtual void dispatch(Comment &expr) {}
    virtual void dispatch(VarDecl &expr) {}
    virtual std::shared_ptr<SMTExpr> reassemble(SetLogic &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Assert &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(TypedVariable &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Forall &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(CheckSat &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(GetModel &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Let &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(ConstantFP &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(ConstantInt &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(ConstantBool &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(ConstantString &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Op &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(FPCmp &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(BinaryFPOperator &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(TypeCast &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Query &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(FunDecl &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(FunDef &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(Comment &expr) {
        return expr.shared_from_this();
    }
    virtual std::shared_ptr<SMTExpr> reassemble(VarDecl &expr) {
        return expr.shared_from_this();
    }
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
