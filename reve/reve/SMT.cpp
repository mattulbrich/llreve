#include "SMT.h"
#include "Memory.h"
#include "Opts.h"

#include <iostream>

namespace smt {
using std::make_shared;
using std::shared_ptr;
using sexpr::Apply;
using sexpr::Value;
using sexpr::List;
using std::set;
using std::string;

SExprRef SetLogic::toSExpr() const {
    std::vector<SExprRef> args;
    SExprRef logicPtr = llvm::make_unique<const Value<std::string>>(logic);

    args.push_back(std::move(logicPtr));
    return llvm::make_unique<Apply<std::string>>("set-logic", std::move(args));
}

SExprRef CheckSat::toSExpr() const {
    std::vector<SExprRef> args;
    return llvm::make_unique<Apply<std::string>>("check-sat", std::move(args));
}

SExprRef Query::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(llvm::make_unique<Value<string>>(queryName));
    args.push_back(llvm::make_unique<Value<string>>(":print-certificate"));
    args.push_back(llvm::make_unique<Value<string>>("true"));
    return llvm::make_unique<Apply<std::string>>("query", std::move(args));
}

SExprRef GetModel::toSExpr() const {
    std::vector<SExprRef> args;
    return llvm::make_unique<Apply<std::string>>("get-model", std::move(args));
}

SExprRef Assert::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(expr->toSExpr());
    const string keyword = MuZFlag ? "rule" : "assert";
    return llvm::make_unique<Apply<std::string>>(keyword, std::move(args));
}

SExprRef Forall::toSExpr() const {
    std::vector<SExprRef> args;
    std::vector<SExprRef> sortedVars;
    for (auto &sortedVar : vars) {
        sortedVars.push_back(sortedVar.toSExpr());
    }
    args.push_back(llvm::make_unique<List<std::string>>(std::move(sortedVars)));
    args.push_back(expr->toSExpr());
    return llvm::make_unique<Apply<std::string>>("forall", std::move(args));
}

SExprRef SortedVar::toSExpr() const {
    std::vector<SExprRef> typeSExpr;
    typeSExpr.push_back(llvm::make_unique<const Value<std::string>>(type));
    return llvm::make_unique<Apply<std::string>>(name, std::move(typeSExpr));
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> args;
    std::vector<SExprRef> defSExprs;
    for (auto &def : defs) {
        std::vector<SExprRef> argSExprs;
        argSExprs.push_back(def.second->toSExpr());
        defSExprs.push_back(llvm::make_unique<Apply<std::string>>(
            def.first, std::move(argSExprs)));
    }
    args.push_back(llvm::make_unique<List<std::string>>(std::move(defSExprs)));
    args.push_back(expr->toSExpr());
    return llvm::make_unique<Apply<std::string>>("let", std::move(args));
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    // Special case for emty and
    if (opName == "and" && args.empty()) {
        return llvm::make_unique<Value<string>>("true");
    }
    for (auto &arg : args) {
        argSExprs.push_back(arg->toSExpr());
    }
    return llvm::make_unique<Apply<std::string>>(opName, std::move(argSExprs));
}

SExprRef FunDecl::toSExpr() const {
    std::vector<SExprRef> inTypeSExprs;
    for (auto inType : inTypes) {
        inTypeSExprs.push_back(name(inType)->toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(name(funName)->toSExpr());
    args.push_back(
        llvm::make_unique<List<std::string>>(std::move(inTypeSExprs)));
    if (!MuZFlag) {
        args.push_back(name(outType)->toSExpr());
    }
    const string keyword = MuZFlag ? "declare-rel" : "declare-fun";
    return llvm::make_unique<Apply<std::string>>(keyword, std::move(args));
}

SExprRef FunDef::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    for (auto arg : args) {
        argSExprs.push_back(arg.toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(name(funName)->toSExpr());
    args.push_back(llvm::make_unique<List<std::string>>(std::move(argSExprs)));
    args.push_back(name(outType)->toSExpr());
    args.push_back(body->toSExpr());
    return llvm::make_unique<Apply<std::string>>("define-fun", std::move(args));
}

SExprRef Comment::toSExpr() const {
    return llvm::make_unique<class sexpr::Comment<std::string>>(val);
}

SExprRef VarDecl::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(name(varName)->toSExpr());
    args.push_back(name(type)->toSExpr());
    return llvm::make_unique<Apply<std::string>>("declare-var",
                                                 std::move(args));
}

set<string> SMTExpr::uses() const { return {}; }

set<string> Assert::uses() const { return expr->uses(); }

set<string> Forall::uses() const { return expr->uses(); }

set<string> SortedVar::uses() const {
    set<string> uses = {name};
    return uses;
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

set<string> Op::uses() const {
    set<string> uses;
    for (auto arg : args) {
        for (auto use : arg->uses()) {
            uses.insert(use);
        }
    }
    return uses;
}

template <> set<string> Primitive<string>::uses() const {
    set<string> uses;
    uses.insert(val);
    return uses;
}

SMTRef SMTExpr::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    return shared_from_this();
}

SMTRef Assert::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    return make_shared<Assert>(expr->compressLets());
}

SMTRef SortedVar::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    return make_shared<SortedVar>(name, type);
}

SMTRef Forall::compressLets(std::vector<Assignment> defs) const {
    return nestLets(make_shared<Forall>(vars, expr->compressLets()), defs);
}

SMTRef CheckSat::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    return shared_from_this();
}

SMTRef GetModel::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    return shared_from_this();
}

SMTRef Let::compressLets(std::vector<Assignment> passedDefs) const {
    passedDefs.insert(passedDefs.end(), defs.begin(), defs.end());
    return expr->compressLets(passedDefs);
}

SMTRef Op::compressLets(std::vector<Assignment> defs) const {
    std::vector<SMTRef> compressedArgs;
    for (auto arg : args) {
        compressedArgs.push_back(arg->compressLets());
    }
    return nestLets(make_shared<Op>(opName, compressedArgs), defs);
}

template <typename T>
SMTRef Primitive<T>::compressLets(std::vector<Assignment> defs) const {
    return nestLets(make_shared<Primitive<T>>(val), defs);
}

SMTRef SMTExpr::mergeImplications(std::vector<SMTRef> conditions) const {
    if (conditions.empty()) {
        return shared_from_this();
    } else {
        return makeBinOp("=>", make_shared<Op>("and", conditions),
                         shared_from_this());
    }
}

SMTRef Assert::mergeImplications(std::vector<SMTRef> conditions) const {
    assert(conditions.empty());
    return make_shared<Assert>(expr->mergeImplications(conditions));
}

SMTRef Let::mergeImplications(std::vector<SMTRef> conditions) const {
    return make_shared<Let>(defs, expr->mergeImplications(conditions));
}

SMTRef Op::mergeImplications(std::vector<SMTRef> conditions) const {
    if (opName == "=>") {
        assert(args.size() == 2);
        conditions.push_back(args.at(0));
        return args.at(1)->mergeImplications(conditions);
    } else {
        return makeBinOp("=>", make_shared<Op>("and", conditions),
                         shared_from_this());
    }
}

SMTRef SMTExpr::instantiateArrays() const { return shared_from_this(); }

SMTRef Assert::instantiateArrays() const {
    return make_shared<Assert>(expr->instantiateArrays());
}

SMTRef Forall::instantiateArrays() const {
    return make_shared<Forall>(vars, expr->instantiateArrays());
}

SMTRef Let::instantiateArrays() const {
    return make_shared<Let>(defs, expr->instantiateArrays());
}

SMTRef Op::instantiateArrays() const {
    if (opName.compare(0, 4, "INV_") == 0) {
        std::vector<SortedVar> indices;
        std::vector<SMTRef> newArgs;
        for (const auto &arg : args) {
            if (auto array = arg->heapInfo()) {
                string index = "i" + array->index + array->suffix;
                newArgs.push_back(name(index));
                newArgs.push_back(makeBinOp("select", arg, name(index)));
                indices.push_back(SortedVar(index, "Int"));
            } else {
                newArgs.push_back(arg);
            }
        }
        return make_shared<Forall>(indices, make_shared<Op>(opName, newArgs));
    } else if (opName == "=" && args.size() == 2 && args.at(0)->heapInfo()) {
        std::vector<SortedVar> indices = {SortedVar("i", "Int")};
        return make_shared<Forall>(
            indices, makeBinOp("=", makeBinOp("select", args.at(0), name("i")),
                               makeBinOp("select", args.at(1), name("i"))));
    } else {
        std::vector<SMTRef> newArgs;
        for (const auto &arg : args) {
            newArgs.push_back(arg->instantiateArrays());
        }
        return make_shared<Op>(opName, newArgs);
    }
}

SMTRef FunDef::instantiateArrays() const {
    return make_shared<FunDef>(funName, args, outType,
                               body->instantiateArrays());
}

SMTRef FunDecl::instantiateArrays() const {
    std::vector<string> newInTypes;
    for (const string &type : inTypes) {
        if (type == "(Array Int Int)") {
            newInTypes.push_back("Int");
            newInTypes.push_back("Int");
        } else {
            newInTypes.push_back("Int");
        }
    }
    return make_shared<FunDecl>(funName, newInTypes, outType);
}

shared_ptr<const HeapInfo> SMTExpr::heapInfo() const { return nullptr; }

template <> shared_ptr<const HeapInfo> Primitive<string>::heapInfo() const {
    std::smatch matchResult;
    if (std::regex_match(val, matchResult, HEAP_REGEX)) {
        return make_shared<HeapInfo>(matchResult[1], matchResult[2],
                                     matchResult[3]);
    }
    return nullptr;
}

SMTRef nestLets(SMTRef clause, std::vector<Assignment> defs) {
    SMTRef lets = clause;
    set<string> uses;
    std::vector<Assignment> defsAccum;
    for (auto i = defs.rbegin(), e = defs.rend(); i != e; ++i) {
        if (uses.find(i->first) != uses.end()) {
            lets = llvm::make_unique<const Let>(defsAccum, lets);
            uses = set<string>();
            defsAccum = std::vector<Assignment>();
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

std::shared_ptr<Op> makeBinOp(std::string opName, std::string arg1,
                              std::string arg2) {
    std::vector<SMTRef> args;
    args.push_back(name(arg1));
    args.push_back(name(arg2));
    return llvm::make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeBinOp(std::string opName, SMTRef arg1, SMTRef arg2) {
    std::vector<SMTRef> args;
    args.push_back(arg1);
    args.push_back(arg2);
    return llvm::make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeUnaryOp(std::string opName, std::string arg) {
    std::vector<SMTRef> args;
    args.push_back(name(arg));
    return llvm::make_unique<Op>(opName, args);
}

std::shared_ptr<Op> makeUnaryOp(std::string opName, SMTRef arg) {
    std::vector<SMTRef> args;
    args.push_back(arg);
    return llvm::make_unique<Op>(opName, args);
}

SMTRef name(std::string name) {
    return llvm::make_unique<Primitive<std::string>>(name);
}

SMTRef makeOp(std::string opName, std::vector<std::string> args) {
    std::vector<SMTRef> smtArgs;
    for (auto arg : args) {
        smtArgs.push_back(name(arg));
    }
    return llvm::make_unique<Op>(opName, smtArgs);
}

shared_ptr<Assignment> makeAssignment(string name, SMTRef val) {
    return make_shared<Assignment>(name, val);
}
}
