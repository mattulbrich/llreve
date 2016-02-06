#include "SMT.h"

#include "SExpr.h"

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using llvm::make_unique;
using std::make_shared;
using sexpr::Apply;
using sexpr::Value;
using sexpr::List;

// Avoid out-of-line warning by defining function here
SMTExpr::~SMTExpr() = default;

SExprRef SetLogic::toSExpr() const {
    std::vector<SExprRef> Args;
    SExprRef LogicPtr = make_unique<const Value<std::string>>(Logic);

    Args.push_back(std::move(LogicPtr));
    return make_unique<Apply<std::string>>("set-logic", std::move(Args));
}

set<string> SetLogic::uses() const { return set<string>(); }

SExprRef CheckSat::toSExpr() const {
    std::vector<SExprRef> Args;
    return make_unique<Apply<std::string>>("check-sat", std::move(Args));
}

set<string> CheckSat::uses() const { return set<string>(); }

SExprRef GetModel::toSExpr() const {
    std::vector<SExprRef> Args;
    return make_unique<Apply<std::string>>("get-model", std::move(Args));
}

set<string> GetModel::uses() const { return set<string>(); }

SExprRef Assert::toSExpr() const {
    std::vector<SExprRef> Args;
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("assert", std::move(Args));
}

set<string> Assert::uses() const { return Expr->uses(); }

SExprRef Forall::toSExpr() const {
    std::vector<SExprRef> Args;
    std::vector<SExprRef> SortedVars;
    for (auto &SortedVar : Vars) {
        SortedVars.push_back(SortedVar.toSExpr());
    }
    Args.push_back(make_unique<List<std::string>>(std::move(SortedVars)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("forall", std::move(Args));
}

set<string> Forall::uses() const { return Expr->uses(); }

SExprRef SortedVar::toSExpr() const {
    std::vector<SExprRef> TypeSExpr;
    TypeSExpr.push_back(make_unique<const Value<std::string>>(Type));
    return make_unique<Apply<std::string>>(Name, std::move(TypeSExpr));
}

set<string> SortedVar::uses() const {
    set<string> Uses = {Name};
    return Uses;
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> Args;
    std::vector<SExprRef> DefSExprs;
    for (auto &Def : Defs) {
        std::vector<SExprRef> ArgSExprs;
        ArgSExprs.push_back(Def.second->toSExpr());
        DefSExprs.push_back(
            make_unique<Apply<std::string>>(Def.first, std::move(ArgSExprs)));
    }
    Args.push_back(make_unique<List<std::string>>(std::move(DefSExprs)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("let", std::move(Args));
}

set<string> Let::uses() const {
    set<string> Uses;
    for (auto Def : Defs) {
        for (auto Use : Def.second->uses()) {
            Uses.insert(Use);
        }
    }
    for (auto Use : Expr->uses()) {
        Uses.insert(Use);
    }
    return Uses;
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> ArgSExprs;
    // Special case for emty and
    if (OpName == "and" && Args.empty()) {
        return make_unique<Value<string>>("true");
    }
    for (auto &Arg : Args) {
        ArgSExprs.push_back(Arg->toSExpr());
    }
    return make_unique<Apply<std::string>>(OpName, std::move(ArgSExprs));
}

set<string> Op::uses() const {
    set<string> Uses;
    for (auto Arg : Args) {
        for (auto Use : Arg->uses()) {
            Uses.insert(Use);
        }
    }
    return Uses;
}

std::shared_ptr<Op> makeBinOp(std::string OpName, std::string Arg1,
                              std::string Arg2) {
    std::vector<SMTRef> Args;
    Args.push_back(name(Arg1));
    Args.push_back(name(Arg2));
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeBinOp(std::string OpName, SMTRef Arg1, SMTRef Arg2) {
    std::vector<SMTRef> Args;
    Args.push_back(Arg1);
    Args.push_back(Arg2);
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeUnaryOp(std::string OpName, std::string Arg) {
    std::vector<SMTRef> Args;
    Args.push_back(name(Arg));
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeUnaryOp(std::string OpName, SMTRef Arg) {
    std::vector<SMTRef> Args;
    Args.push_back(Arg);
    return make_unique<Op>(OpName, Args);
}

SMTRef name(std::string Name) {
    return make_unique<Primitive<std::string>>(Name);
}

SMTRef makeOp(std::string OpName, std::vector<std::string> Args) {
    std::vector<SMTRef> SMTArgs;
    for (auto Arg : Args) {
        SMTArgs.push_back(name(Arg));
    }
    return make_unique<Op>(OpName, SMTArgs);
}

SExprRef FunDecl::toSExpr() const {
    std::vector<SExprRef> InTypeSExprs;
    for (auto InType : InTypes) {
        InTypeSExprs.push_back(name(InType)->toSExpr());
    }
    std::vector<SExprRef> Args;
    Args.push_back(name(FunName)->toSExpr());
    Args.push_back(make_unique<List<std::string>>(std::move(InTypeSExprs)));
    Args.push_back(name(OutType)->toSExpr());
    return make_unique<Apply<std::string>>("declare-fun", std::move(Args));
}

SExprRef FunDef::toSExpr() const {
    std::vector<SExprRef> ArgSExprs;
    for (auto Arg : Args) {
        ArgSExprs.push_back(Arg.toSExpr());
    }
    std::vector<SExprRef> Args;
    Args.push_back(name(FunName)->toSExpr());
    Args.push_back(make_unique<List<std::string>>(std::move(ArgSExprs)));
    Args.push_back(name(OutType)->toSExpr());
    Args.push_back(Body->toSExpr());
    return make_unique<Apply<std::string>>("define-fun", std::move(Args));
}

set<string> FunDecl::uses() const { return set<string>(); }

set<string> FunDef::uses() const { return set<string>(); }

template <> set<string> Primitive<string>::uses() const {
    set<string> Uses;
    Uses.insert(Val);
    return Uses;
}

SMTRef SetLogic::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<SetLogic>(Logic), Defs);
}

SMTRef Assert::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<Assert>(Expr->compressLets()), Defs);
}

SMTRef SortedVar::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<SortedVar>(Name, Type), Defs);
}

SMTRef Forall::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<Forall>(Vars, Expr->compressLets()), Defs);
}

SMTRef CheckSat::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<CheckSat>(), Defs);
}

SMTRef GetModel::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<GetModel>(), Defs);
}

SMTRef Let::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> PassedDefs)
    const {
    PassedDefs.insert(PassedDefs.end(), Defs.begin(), Defs.end());
    return Expr->compressLets(PassedDefs);
}

SMTRef Op::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    std::vector<SMTRef> CompressedArgs;
    for (auto Arg : Args) {
        CompressedArgs.push_back(Arg->compressLets());
    }
    return nestLets(make_shared<Op>(OpName, CompressedArgs), Defs);
}

SMTRef FunDecl::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<FunDecl>(FunName, InTypes, OutType), Defs);
}

SMTRef FunDef::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<FunDef>(FunName, Args, OutType, Body), Defs);
}

template <typename T>
SMTRef Primitive<T>::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<Primitive<T>>(Val), Defs);
}

SMTRef nestLets(SMTRef Clause, std::vector<std::pair<string, SMTRef>> Defs) {
    SMTRef Lets = Clause;
    set<string> Uses;
    std::vector<std::pair<string, SMTRef>> DefsAccum;
    for (auto I = Defs.rbegin(), E = Defs.rend(); I != E; ++I) {
        if (Uses.find(I->first) != Uses.end()) {
            Lets = llvm::make_unique<const Let>(DefsAccum, Lets);
            Uses = set<string>();
            DefsAccum = std::vector<std::pair<string, SMTRef>>();
        }
        DefsAccum.insert(DefsAccum.begin(), *I);
        for (auto Use : I->second->uses()) {
            Uses.insert(Use);
        }
    }
    if (!DefsAccum.empty()) {
        Lets = llvm::make_unique<const Let>(DefsAccum, Lets);
    }
    return Lets;
}

SMTRef Comment::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> Defs) const {
    return nestLets(make_shared<Comment>(Val), Defs);
}

SExprRef Comment::toSExpr() const {
    return llvm::make_unique<class sexpr::Comment<std::string>>(Val);
}

std::set<std::string> Comment::uses() const { return std::set<std::string>(); }
