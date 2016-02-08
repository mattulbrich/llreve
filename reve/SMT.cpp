#include "SMT.h"

#include <iostream>

using llvm::make_unique;
using std::make_shared;
using sexpr::Apply;
using sexpr::Value;
using sexpr::List;

// Avoid out-of-line warning by defining function here
SMTExpr::~SMTExpr() = default;

SExprRef SetLogic::toSExpr() const {
    std::vector<SExprRef> args;
    SExprRef logicPtr = make_unique<const Value<std::string>>(logic);

    args.push_back(std::move(logicPtr));
    return make_unique<Apply<std::string>>("set-logic", std::move(args));
}

set<string> SetLogic::uses() const { return set<string>(); }

SExprRef CheckSat::toSExpr() const {
    std::vector<SExprRef> args;
    return make_unique<Apply<std::string>>("check-sat", std::move(args));
}

set<string> CheckSat::uses() const { return set<string>(); }

SExprRef GetModel::toSExpr() const {
    std::vector<SExprRef> args;
    return make_unique<Apply<std::string>>("get-model", std::move(args));
}

set<string> GetModel::uses() const { return set<string>(); }

SExprRef Assert::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(expr->toSExpr());
    return make_unique<Apply<std::string>>("assert", std::move(args));
}

set<string> Assert::uses() const { return expr->uses(); }

SExprRef Forall::toSExpr() const {
    std::vector<SExprRef> args;
    std::vector<SExprRef> sortedVars;
    for (auto &sortedVar : vars) {
        sortedVars.push_back(sortedVar.toSExpr());
    }
    args.push_back(make_unique<List<std::string>>(std::move(sortedVars)));
    args.push_back(expr->toSExpr());
    return make_unique<Apply<std::string>>("forall", std::move(args));
}

set<string> Forall::uses() const { return expr->uses(); }

SExprRef SortedVar::toSExpr() const {
    std::vector<SExprRef> typeSExpr;
    typeSExpr.push_back(make_unique<const Value<std::string>>(type));
    return make_unique<Apply<std::string>>(name, std::move(typeSExpr));
}

set<string> SortedVar::uses() const {
    set<string> uses = {name};
    return uses;
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> args;
    std::vector<SExprRef> defSExprs;
    for (auto &def : defs) {
        std::vector<SExprRef> argSExprs;
        argSExprs.push_back(def.second->toSExpr());
        defSExprs.push_back(
            make_unique<Apply<std::string>>(def.first, std::move(argSExprs)));
    }
    args.push_back(make_unique<List<std::string>>(std::move(defSExprs)));
    args.push_back(expr->toSExpr());
    return make_unique<Apply<std::string>>("let", std::move(args));
}

set<string> Let::uses() const {
    set<string> uses;
    for (auto def : defs) {
        for (auto use : def.second->uses()) {
            uses.insert(use);
        }
    }
    for (auto use : expr->uses()) {
        uses.insert(use);
    }
    return uses;
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    // Special case for emty and
    if (opName == "and" && args.empty()) {
        return make_unique<Value<string>>("true");
    }
    for (auto &arg : args) {
        argSExprs.push_back(arg->toSExpr());
    }
    return make_unique<Apply<std::string>>(opName, std::move(argSExprs));
}

set<string> Op::uses() const {
    set<string> uses;
    for (auto arg : args) {
        for (auto use : arg->uses()) {
            uses.insert(use);
        }
    }
    return uses;
}

std::shared_ptr<Op> makeBinOp(std::string opName, std::string arg1,
                              std::string arg2) {
    std::vector<SMTRef> args;
    args.push_back(name(arg1));
    args.push_back(name(arg2));
    return make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeBinOp(std::string opName, SMTRef arg1, SMTRef arg2) {
    std::vector<SMTRef> args;
    args.push_back(arg1);
    args.push_back(arg2);
    return make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeUnaryOp(std::string opName, std::string arg) {
    std::vector<SMTRef> args;
    args.push_back(name(arg));
    return make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeUnaryOp(std::string opName, SMTRef arg) {
    std::vector<SMTRef> args;
    args.push_back(arg);
    return make_unique<Op>(opName, args);
}

SMTRef name(std::string name) {
    return make_unique<Primitive<std::string>>(name);
}

SMTRef makeOp(std::string opName, std::vector<std::string> args) {
    std::vector<SMTRef> smtArgs;
    for (auto arg : args) {
        smtArgs.push_back(name(arg));
    }
    return make_unique<Op>(opName, smtArgs);
}

SExprRef FunDecl::toSExpr() const {
    std::vector<SExprRef> inTypeSExprs;
    for (auto inType : inTypes) {
        inTypeSExprs.push_back(name(inType)->toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(name(funName)->toSExpr());
    args.push_back(make_unique<List<std::string>>(std::move(inTypeSExprs)));
    args.push_back(name(outType)->toSExpr());
    return make_unique<Apply<std::string>>("declare-fun", std::move(args));
}

SExprRef FunDef::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    for (auto arg : args) {
        argSExprs.push_back(arg.toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(name(funName)->toSExpr());
    args.push_back(make_unique<List<std::string>>(std::move(argSExprs)));
    args.push_back(name(outType)->toSExpr());
    args.push_back(body->toSExpr());
    return make_unique<Apply<std::string>>("define-fun", std::move(args));
}

set<string> FunDecl::uses() const { return set<string>(); }

set<string> FunDef::uses() const { return set<string>(); }

template <> set<string> Primitive<string>::uses() const {
    set<string> uses;
    uses.insert(val);
    return uses;
}

SMTRef SetLogic::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<SetLogic>(logic), defs);
}

SMTRef Assert::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<Assert>(expr->compressLets()), defs);
}

SMTRef SortedVar::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<SortedVar>(name, type), defs);
}

SMTRef Forall::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<Forall>(vars, expr->compressLets()), defs);
}

SMTRef CheckSat::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<CheckSat>(), defs);
}

SMTRef GetModel::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<GetModel>(), defs);
}

SMTRef Let::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> passedDefs)
    const {
    passedDefs.insert(passedDefs.end(), defs.begin(), defs.end());
    return expr->compressLets(passedDefs);
}

SMTRef Op::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    std::vector<SMTRef> compressedArgs;
    for (auto arg : args) {
        compressedArgs.push_back(arg->compressLets());
    }
    return nestLets(make_shared<Op>(opName, compressedArgs), defs);
}

SMTRef FunDecl::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<FunDecl>(funName, inTypes, outType), defs);
}

SMTRef FunDef::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<FunDef>(funName, args, outType, body), defs);
}

template <typename T>
SMTRef Primitive<T>::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<Primitive<T>>(val), defs);
}

SMTRef nestLets(SMTRef clause, std::vector<std::pair<string, SMTRef>> defs) {
    SMTRef lets = clause;
    set<string> uses;
    std::vector<std::pair<string, SMTRef>> defsAccum;
    for (auto i = defs.rbegin(), e = defs.rend(); i != e; ++i) {
        if (uses.find(i->first) != uses.end()) {
            lets = llvm::make_unique<const Let>(defsAccum, lets);
            uses = set<string>();
            defsAccum = std::vector<std::pair<string, SMTRef>>();
        }
        defsAccum.insert(defsAccum.begin(), *i);
        for (auto use : i->second->uses()) {
            uses.insert(use);
        }
    }
    if (!defsAccum.empty()) {
        lets = llvm::make_unique<const Let>(defsAccum, lets);
    }
    return lets;
}

SMTRef Comment::compressLets(
    std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs) const {
    return nestLets(make_shared<Comment>(val), defs);
}

SExprRef Comment::toSExpr() const {
    return llvm::make_unique<class sexpr::Comment<std::string>>(val);
}

std::set<std::string> Comment::uses() const { return std::set<std::string>(); }
