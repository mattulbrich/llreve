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
SMTExpr::~SMTExpr() {}

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
    std::vector<SExprRef> Type_;
    Type_.push_back(make_unique<const Value<std::string>>(Type));
    return make_unique<Apply<std::string>>(Name, std::move(Type_));
}

set<string> SortedVar::uses() const {
    set<string> Uses = {Name};
    return Uses;
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> Args;
    std::vector<SExprRef> Defs_;
    for (auto &Def : Defs) {
        std::vector<SExprRef> Args_;
        Args_.push_back(std::get<1>(Def)->toSExpr());
        Defs_.push_back(make_unique<Apply<std::string>>(std::get<0>(Def),
                                                        std::move(Args_)));
    }
    Args.push_back(make_unique<List<std::string>>(std::move(Defs_)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("let", std::move(Args));
}

set<string> Let::uses() const {
    set<string> Uses;
    for (auto Def : Defs) {
        for (auto Use : std::get<1>(Def)->uses()) {
            Uses.insert(Use);
        }
    }
    for (auto Use : Expr->uses()) {
        Uses.insert(Use);
    }
    return Uses;
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> Args_;
    for (auto &Arg : Args) {
        Args_.push_back(Arg->toSExpr());
    }
    return make_unique<Apply<std::string>>(OpName, std::move(Args_));
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

std::shared_ptr<Op> makeBinOp(std::string OpName, std::string Arg_1,
                              std::string Arg_2) {
    std::vector<SMTRef> Args;
    Args.push_back(name(Arg_1));
    Args.push_back(name(Arg_2));
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeBinOp(std::string OpName, SMTRef Arg_1, SMTRef Arg_2) {
    std::vector<SMTRef> Args;
    Args.push_back(Arg_1);
    Args.push_back(Arg_2);
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
    std::vector<SMTRef> Args_;
    for (auto Arg : Args) {
        Args_.push_back(name(Arg));
    }
    return make_unique<Op>(OpName, Args_);
}

SExprRef Fun::toSExpr() const {
    std::vector<SExprRef> InTypes_;
    for (auto InType : InTypes) {
        InTypes_.push_back(name(InType)->toSExpr());
    }
    std::vector<SExprRef> Args;
    Args.push_back(name(FunName)->toSExpr());
    Args.push_back(make_unique<List<std::string>>(std::move(InTypes_)));
    Args.push_back(name(OutType)->toSExpr());
    return make_unique<Apply<std::string>>("declare-fun", std::move(Args));
}

set<string> Fun::uses() const { return set<string>(); }

template <> set<string> Primitive<string>::uses() const {
    set<string> Uses;
    Uses.insert(Val);
    return Uses;
}

SMTRef SetLogic::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<SetLogic>(Logic), Defs);
}

SMTRef Assert::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<Assert>(Expr->compressLets()), Defs);
}

SMTRef SortedVar::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<SortedVar>(Name, Type), Defs);
}

SMTRef Forall::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<Forall>(Vars, Expr->compressLets()), Defs);
}

SMTRef CheckSat::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<CheckSat>(), Defs);
}

SMTRef GetModel::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<GetModel>(), Defs);
}

SMTRef Let::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs_)
    const {
    Defs_.insert(Defs_.end(), Defs.begin(), Defs.end());
    return Expr->compressLets(Defs_);
}

SMTRef Op::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    std::vector<SMTRef> Args_;
    for (auto Arg : Args) {
        Args_.push_back(Arg->compressLets());
    }
    return nestLets(make_shared<Op>(OpName, Args_), Defs);
}

SMTRef Fun::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<Fun>(FunName, InTypes, OutType), Defs);
}

template <typename T>
SMTRef Primitive<T>::compressLets(
    std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
    const {
    return nestLets(make_shared<Primitive<T>>(Val), Defs);
}

SMTRef nestLets(SMTRef Clause, std::vector<std::tuple<string, SMTRef>> Defs) {
    SMTRef Lets = Clause;
    set<string> Uses;
    std::vector<std::tuple<string, SMTRef>> DefsAccum;
    for (auto I = Defs.rbegin(), E = Defs.rend(); I != E; ++I) {
        if (Uses.find(std::get<0>(*I)) != Uses.end()) {
            Lets = llvm::make_unique<const Let>(DefsAccum, Lets);
            Uses = set<string>();
            DefsAccum = std::vector<std::tuple<string, SMTRef>>();
        }
        DefsAccum.insert(DefsAccum.begin(), *I);
        for (auto Use : std::get<1>(*I)->uses()) {
            Uses.insert(Use);
        }
    }
    if (!DefsAccum.empty()) {
        Lets = llvm::make_unique<const Let>(DefsAccum, Lets);
    }
    return Lets;
}
