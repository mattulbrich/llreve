/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SMT.h"

#include "Compat.h"
#include "Helper.h"
#include "Memory.h"
#include "Opts.h"

#include <iostream>

namespace smt {
using std::map;
using std::make_shared;
using std::make_unique;
using std::shared_ptr;
using std::unique_ptr;
using sexpr::Apply;
using sexpr::Value;
using sexpr::List;
using std::set;
using std::string;
using std::vector;

// Implementations of toSExpr()

SExprRef TypedVariable::toSExpr() const { return sexprFromString(name); }

SExprRef ConstantFP::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Bitvector representation of floating points is not yet "
                 "implemented\n");
        exit(1);
    } else {
        // 4 is chosen arbitrarily
        llvm::SmallVector<char, 4> stringVec;
        // 500 is large enough to never use scientific notation
        this->value.toString(stringVec, 0, 500);
        string stringRepr(stringVec.begin(), stringVec.end());
        return sexprFromString(stringRepr);
    }
}

SExprRef ConstantInt::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        // TODO we should use the sexpr machinery instead of appending strings
        unsigned bitWidth = value.getBitWidth();
        if (value.isNegative()) {
            return smt::makeOp("bvneg",
                               smt::makeOp("_",
                                           "bv" + (-value).toString(10, true),
                                           std::to_string(bitWidth)))
                ->toSExpr();

        } else {
            return sexprFromString("(_ bv" + value.toString(10, true) + " " +
                                   std::to_string(bitWidth) + ")");
        }
    } else {
        if (value.isNegative()) {
            vector<SExprRef> args;
            args.push_back(sexprFromString((-value).toString(10, true)));
            return make_unique<Apply>("-", std::move(args));
        } else {
            return sexprFromString(value.toString(10, true));
        }
    }
}

SExprRef ConstantBool::toSExpr() const {
    if (value) {
        return sexprFromString("true");
    } else {
        return sexprFromString("false");
    }
}

SExprRef ConstantString::toSExpr() const { return sexprFromString(value); }

SExprRef SetLogic::toSExpr() const {
    std::vector<SExprRef> args;
    SExprRef logicPtr = make_unique<Value>(logic);

    args.push_back(std::move(logicPtr));
    return make_unique<Apply>("set-logic", std::move(args));
}

SExprRef CheckSat::toSExpr() const {
    std::vector<SExprRef> args;
    return make_unique<Apply>("check-sat", std::move(args));
}

SExprRef Query::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(make_unique<Value>(queryName));
    args.push_back(make_unique<Value>(":print-certificate"));
    args.push_back(make_unique<Value>("true"));
    return make_unique<Apply>("query", std::move(args));
}

SExprRef GetModel::toSExpr() const {
    std::vector<SExprRef> args;
    return make_unique<Apply>("get-model", std::move(args));
}

SExprRef Assert::toSExpr() const {
    std::vector<SExprRef> args;
    args.push_back(expr->toSExpr());
    const string keyword =
        SMTGenerationOpts::getInstance().MuZ ? "rule" : "assert";
    return make_unique<Apply>(keyword, std::move(args));
}

SExprRef Forall::toSExpr() const {
    if (vars.empty()) {
        return expr->toSExpr();
    }
    std::vector<SExprRef> args;
    std::vector<SExprRef> sortedVars;
    for (auto &sortedVar : vars) {
        sortedVars.push_back(sortedVar.toSExpr());
    }
    args.push_back(make_unique<List>(std::move(sortedVars)));
    args.push_back(expr->toSExpr());
    return make_unique<Apply>("forall", std::move(args));
}

SExprRef SortedVar::toSExpr() const {
    std::vector<SExprRef> typeSExpr;
    typeSExpr.push_back(type->toSExpr());
    return make_unique<Apply>(name, std::move(typeSExpr));
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> args;
    std::vector<SExprRef> defSExprs;
    for (auto &def : defs) {
        std::vector<SExprRef> argSExprs;
        argSExprs.push_back(def.second->toSExpr());
        defSExprs.push_back(
            make_unique<Apply>(def.first, std::move(argSExprs)));
    }
    args.push_back(make_unique<List>(std::move(defSExprs)));
    args.push_back(expr->toSExpr());
    return make_unique<Apply>("let", std::move(args));
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    // Special case for emty and
    if (opName == "and" && args.empty()) {
        return make_unique<Value>("true");
    }
    for (auto &arg : args) {
        argSExprs.push_back(arg->toSExpr());
    }
    return make_unique<Apply>(opName, std::move(argSExprs));
}

SExprRef FunDecl::toSExpr() const {
    std::vector<SExprRef> inTypeSExprs;
    for (const auto &inType : inTypes) {
        inTypeSExprs.push_back(inType->toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(stringExpr(funName)->toSExpr());
    args.push_back(make_unique<List>(std::move(inTypeSExprs)));
    if (!SMTGenerationOpts::getInstance().MuZ) {
        args.push_back(outType->toSExpr());
    }
    const string keyword =
        SMTGenerationOpts::getInstance().MuZ ? "declare-rel" : "declare-fun";
    return make_unique<Apply>(keyword, std::move(args));
}

SExprRef FunDef::toSExpr() const {
    std::vector<SExprRef> argSExprs;
    for (auto arg : args) {
        argSExprs.push_back(arg.toSExpr());
    }
    std::vector<SExprRef> args;
    args.push_back(stringExpr(funName)->toSExpr());
    args.push_back(make_unique<List>(std::move(argSExprs)));
    args.push_back(outType->toSExpr());
    args.push_back(body->toSExpr());
    return make_unique<Apply>("define-fun", std::move(args));
}

SExprRef Comment::toSExpr() const {
    return make_unique<class sexpr::Comment>(val);
}

SExprRef VarDecl::toSExpr() const {
    vector<SExprRef> args;
    args.push_back(stringExpr(var.name)->toSExpr());
    args.push_back(var.type->toSExpr());
    return make_unique<Apply>("declare-var", std::move(args));
}

SExprRef FPCmp::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Floating point predicates for bitvectors are not yet "
                 "impleneted\n");
        exit(1);
    } else {
        vector<SExprRef> args;
        args.push_back(op0->toSExpr());
        args.push_back(op1->toSExpr());
        switch (this->op) {
        case Predicate::False:
            return sexprFromString("false");
        case Predicate::True:
            return sexprFromString("true");
        case Predicate::OEQ:
        case Predicate::UEQ:
            return make_unique<Apply>("=", std::move(args));
        case Predicate::OGT:
        case Predicate::UGT:
            return make_unique<Apply>(">", std::move(args));
        case Predicate::OGE:
        case Predicate::UGE:
            return make_unique<Apply>(">=", std::move(args));
        case Predicate::OLT:
        case Predicate::ULT:
            return make_unique<Apply>("<", std::move(args));
        case Predicate::OLE:
        case Predicate::ULE:
            return make_unique<Apply>("<=", std::move(args));
        case Predicate::ONE:
        case Predicate::UNE:
            return make_unique<Apply>("distinct", std::move(args));
        case Predicate::ORD:
        case Predicate::UNO:
            logError("Cannot check reals for orderedness\n");
            exit(1);
        }
    }
}

SExprRef BinaryFPOperator::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Floating point binary operators for bitvectors are not yet "
                 "implemented\n");
        exit(1);
    } else {
        vector<SExprRef> args;
        args.push_back(op0->toSExpr());
        args.push_back(op1->toSExpr());
        switch (this->op) {
        case Opcode::FAdd:
            return make_unique<Apply>("+", std::move(args));
        case Opcode::FSub:
            return make_unique<Apply>("-", std::move(args));
        case Opcode::FMul:
            return make_unique<Apply>("*", std::move(args));
        case Opcode::FDiv:
            return make_unique<Apply>("/", std::move(args));
        case Opcode::FRem:
            logError("SMT reals don’t support a remainder operation\n");
            exit(1);
        }
    }
}

// Implementations of uses()

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

set<string> FPCmp::uses() const {
    set<string> uses;
    for (auto use : op0->uses()) {
        uses.insert(use);
    }
    for (auto use : op1->uses()) {
        uses.insert(use);
    }
    return uses;
}

set<string> BinaryFPOperator::uses() const {
    set<string> uses;
    for (auto use : op0->uses()) {
        uses.insert(use);
    }
    for (auto use : op1->uses()) {
        uses.insert(use);
    }
    return uses;
}

set<string> ConstantString::uses() const { return {value}; }

set<string> TypedVariable::uses() const { return {name}; }

// Implementations of compressLets

SharedSMTRef SMTExpr::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef Assert::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    unused(defs);
    return make_shared<Assert>(expr->compressLets());
}

SharedSMTRef Forall::compressLets(std::vector<Assignment> defs) const {
    return nestLets(make_shared<Forall>(vars, expr->compressLets()), defs);
}

SharedSMTRef CheckSat::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef GetModel::compressLets(std::vector<Assignment> defs) const {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef Let::compressLets(std::vector<Assignment> passedDefs) const {
    passedDefs.insert(passedDefs.end(), defs.begin(), defs.end());
    return expr->compressLets(passedDefs);
}

SharedSMTRef Op::compressLets(std::vector<Assignment> defs) const {
    std::vector<SharedSMTRef> compressedArgs;
    for (auto arg : args) {
        compressedArgs.push_back(arg->compressLets());
    }
    return nestLets(make_shared<Op>(opName, compressedArgs, instantiate), defs);
}

SharedSMTRef ConstantString::compressLets(std::vector<Assignment> defs) const {
    return nestLets(shared_from_this(), defs);
}

SharedSMTRef ConstantBool::compressLets(std::vector<Assignment> defs) const {
    return nestLets(shared_from_this(), defs);
}

// Implementations of renameAssignments

SharedSMTRef SMTExpr::renameAssignments(map<string, int> variableMap) const {
    return shared_from_this();
}

SharedSMTRef
ConstantString::renameAssignments(map<string, int> variableMap) const {
    if (value.at(0) == '(') {
        return shared_from_this();
    } else {
        string name = value;
        if (variableMap.find(value) != variableMap.end()) {
            name += "_" + std::to_string(variableMap.at(value));
        }
        return make_shared<ConstantString>(name);
    }
}

SharedSMTRef
TypedVariable::renameAssignments(map<string, int> variableMap) const {
    string newName = name;
    if (variableMap.find(newName) != variableMap.end()) {
        newName += "_" + std::to_string(variableMap.at(newName));
    }
    return make_unique<TypedVariable>(newName, type->copy());
}

SharedSMTRef Assert::renameAssignments(map<string, int> variableMap) const {
    assert(variableMap.empty());
    return make_shared<Assert>(expr->renameAssignments(variableMap));
}

SharedSMTRef Let::renameAssignments(map<string, int> variableMap) const {
    vector<Assignment> newDefs;
    auto newVariableMap = variableMap;
    for (auto assgn : defs) {
        int newIndex = ++newVariableMap[assgn.first];
        newDefs.push_back({assgn.first + "_" + std::to_string(newIndex),
                           assgn.second->renameAssignments(variableMap)});
    }
    return make_shared<Let>(newDefs, expr->renameAssignments(newVariableMap));
}

SharedSMTRef Op::renameAssignments(map<string, int> variableMap) const {
    vector<SharedSMTRef> newArgs;
    for (const auto &arg : this->args) {
        newArgs.push_back(arg->renameAssignments(variableMap));
    }
    return make_shared<Op>(opName, newArgs, instantiate);
}

SharedSMTRef FPCmp::renameAssignments(map<string, int> variableMap) const {
    auto newOp0 = op0->renameAssignments(variableMap);
    auto newOp1 = op1->renameAssignments(variableMap);
    return make_shared<FPCmp>(op, type->copy(), newOp0, newOp1);
}

SharedSMTRef
BinaryFPOperator::renameAssignments(map<string, int> variableMap) const {
    auto newOp0 = op0->renameAssignments(variableMap);
    auto newOp1 = op1->renameAssignments(variableMap);
    return make_shared<BinaryFPOperator>(op, type->copy(), newOp0, newOp1);
}

SharedSMTRef Forall::renameAssignments(map<string, int> variableMap) const {
    vector<SortedVar> newVars;
    for (auto var : this->vars) {
        variableMap[var.name]++;
        newVars.push_back(
            {var.name + "_" + std::to_string(variableMap.at(var.name)),
             std::move(var.type)});
    }
    return make_shared<Forall>(newVars, expr->renameAssignments(variableMap));
}

// Implementations of mergeImplications

SharedSMTRef
SMTExpr::mergeImplications(std::vector<SharedSMTRef> conditions) const {
    if (conditions.empty()) {
        return shared_from_this();
    } else {
        return makeOp("=>", make_shared<Op>("and", conditions),
                      shared_from_this());
    }
}

SharedSMTRef
Assert::mergeImplications(std::vector<SharedSMTRef> conditions) const {
    assert(conditions.empty());
    return make_shared<Assert>(expr->mergeImplications(conditions));
}

SharedSMTRef
Let::mergeImplications(std::vector<SharedSMTRef> conditions) const {
    return make_shared<Let>(defs, expr->mergeImplications(conditions));
}

SharedSMTRef Op::mergeImplications(std::vector<SharedSMTRef> conditions) const {
    if (opName == "=>") {
        assert(args.size() == 2);
        conditions.push_back(args.at(0));
        return args.at(1)->mergeImplications(conditions);
    } else {
        return makeOp("=>", make_shared<Op>("and", conditions),
                      shared_from_this());
    }
}

SharedSMTRef
Forall::mergeImplications(std::vector<SharedSMTRef> conditions) const {
    return std::make_shared<Forall>(vars, expr->mergeImplications(conditions));
}

// Implementations of splitConjunctions()

vector<SharedSMTRef> SMTExpr::splitConjunctions() const {
    return {shared_from_this()};
}

vector<SharedSMTRef> Assert::splitConjunctions() const {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Assert>(std::move(expr));
    }
    return smtExprs;
}

vector<SharedSMTRef> Let::splitConjunctions() const {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Let>(defs, std::move(expr));
    }
    return smtExprs;
}

vector<SharedSMTRef> Op::splitConjunctions() const {
    if (opName == "=>") {
        assert(args.size() == 2);
        vector<SharedSMTRef> smtExprs = args.at(1)->splitConjunctions();
        for (auto &expr : smtExprs) {
            expr = makeOp("=>", args.at(0), std::move(expr));
        }
        return smtExprs;
    } else if (opName == "and") {
        vector<SharedSMTRef> smtExprs;
        for (const auto &expr : args) {
            vector<SharedSMTRef> exprs = expr->splitConjunctions();
            smtExprs.insert(smtExprs.end(), exprs.begin(), exprs.end());
        }
        return smtExprs;
    } else {
        return {shared_from_this()};
    }
}

vector<SharedSMTRef> Forall::splitConjunctions() const {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Forall>(vars, std::move(expr));
    }
    return smtExprs;
}

// Implementations of instantiateArrays

SharedSMTRef SMTExpr::instantiateArrays() const { return shared_from_this(); }

SharedSMTRef Assert::instantiateArrays() const {
    return make_shared<Assert>(expr->instantiateArrays());
}

SharedSMTRef Forall::instantiateArrays() const {
    return make_shared<Forall>(vars, expr->instantiateArrays());
}

SharedSMTRef Let::instantiateArrays() const {
    return make_shared<Let>(defs, expr->instantiateArrays());
}

SharedSMTRef Op::instantiateArrays() const {
    if (opName.compare(0, 4, "INV_") == 0 || opName == "INIT") {
        std::vector<SortedVar> indices;
        std::vector<SharedSMTRef> newArgs;
        for (const auto &arg : args) {
            if (auto array = arg->heapInfo()) {
                if (instantiate) {
                    string index = "i" + array->index + array->suffix;
                    newArgs.push_back(stringExpr(index));
                    newArgs.push_back(makeOp("select", arg, stringExpr(index)));
                    indices.push_back({index, pointerType()});
                } else {
                    newArgs.push_back(arg);
                }
            } else {
                newArgs.push_back(arg);
            }
        }
        return make_shared<Forall>(indices, make_shared<Op>(opName, newArgs));
    } else if (opName == "=" && args.size() == 2 && args.at(0)->heapInfo()) {
        std::vector<SortedVar> indices = {{"i", pointerType()}};
        return make_shared<Forall>(
            indices, makeOp("=", makeOp("select", args.at(0), "i"),
                            makeOp("select", args.at(1), "i")));
    } else {
        std::vector<SharedSMTRef> newArgs;
        for (const auto &arg : args) {
            newArgs.push_back(arg->instantiateArrays());
        }
        return make_shared<Op>(opName, newArgs);
    }
}

SharedSMTRef FunDef::instantiateArrays() const {
    return make_shared<FunDef>(funName, args, outType->copy(),
                               body->instantiateArrays());
}

SharedSMTRef FunDecl::instantiateArrays() const {
    std::vector<unique_ptr<Type>> newInTypes;
    for (const auto &type : inTypes) {
        if (isArray(*type)) {
            newInTypes.push_back(int64Type());
            newInTypes.push_back(make_unique<IntType>(8));
        } else {
            newInTypes.push_back(type->copy());
        }
    }
    return make_shared<FunDecl>(funName, std::move(newInTypes),
                                outType->copy());
}

// Implementations of heapInfo

unique_ptr<const HeapInfo> SMTExpr::heapInfo() const { return nullptr; }

unique_ptr<const HeapInfo> TypedVariable::heapInfo() const {
    std::smatch matchResult;
    if (std::regex_match(name, matchResult, HEAP_REGEX)) {
        return make_unique<HeapInfo>(matchResult[1], matchResult[2],
                                     matchResult[3]);
    }
    return nullptr;
}

// Implementations of removeForalls

SharedSMTRef SMTExpr::removeForalls(set<SortedVar> &introducedVariables) const {
    return shared_from_this();
}
SharedSMTRef Assert::removeForalls(set<SortedVar> &introducedVariables) const {
    return make_shared<Assert>(expr->removeForalls(introducedVariables));
}
SharedSMTRef Forall::removeForalls(set<SortedVar> &introducedVariables) const {
    for (const auto &var : vars) {
        introducedVariables.insert(var);
    }
    return expr->removeForalls(introducedVariables);
}
SharedSMTRef Op::removeForalls(set<SortedVar> &introducedVariables) const {
    vector<SharedSMTRef> newArgs;
    for (const auto &arg : args) {
        newArgs.push_back(arg->removeForalls(introducedVariables));
    }
    return make_shared<Op>(opName, newArgs, instantiate);
}
SharedSMTRef Let::removeForalls(set<SortedVar> &introducedVariables) const {
    return make_shared<Let>(defs, expr->removeForalls(introducedVariables));
}

// Implementations for using the z3 API

void VarDecl::toZ3(z3::context &cxt, z3::solver & /* unused */,
                   std::map<std::string, z3::expr> &nameMap,
                   std::map<std::string, Z3DefineFun> & /* unused */) const {
    if (var.type->getTag() == TypeTag::Int) {
        z3::expr c = cxt.int_const(var.name.c_str());
        auto it = nameMap.insert({var.name, c});
        if (!it.second) {
            it.first->second = c;
        }
    } else if (var.type->getTag() == TypeTag::Array) {
        z3::sort intArraySort = cxt.array_sort(cxt.int_sort(), cxt.int_sort());
        z3::expr c = cxt.constant(var.name.c_str(), intArraySort);
        auto it = nameMap.insert({var.name, c});
        if (!it.second) {
            it.first->second = c;
        }
    } else {
        std::cerr << "Unsupported type\n";
        exit(1);
    }
}

void Assert::toZ3(z3::context &cxt, z3::solver &solver,
                  std::map<std::string, z3::expr> &nameMap,
                  std::map<std::string, Z3DefineFun> &defineFunMap) const {
    solver.add(expr->toZ3Expr(cxt, nameMap, defineFunMap));
}

void CheckSat::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                    std::map<std::string, z3::expr> & /* unused */,
                    std::map<std::string, Z3DefineFun> & /* unused */) const {
    /* noop */
}

void GetModel::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                    std::map<std::string, z3::expr> & /* unused */,
                    std::map<std::string, Z3DefineFun> & /* unused */) const {
    /* noop */
}

void SMTExpr::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                   std::map<std::string, z3::expr> & /* unused */,
                   std::map<std::string, Z3DefineFun> &
                   /* unused */) const {
    std::cerr << "Unsupported smt toplevel\n";
    std::cerr << *toSExpr();
    exit(1);
}

z3::expr SMTExpr::toZ3Expr(
    z3::context & /* unused */, std::map<std::string, z3::expr> & /* unused */,
    const std::map<std::string, Z3DefineFun> & /* unused */) const {
    std::cerr << "Unsupported smt expr\n";
    std::cerr << *toSExpr();
    exit(1);
}

z3::expr ConstantString::toZ3Expr(
    z3::context &cxt, std::map<std::string, z3::expr> &nameMap,
    const std::map<std::string, Z3DefineFun> & /* unused */) const {
    if (nameMap.count(value) == 0) {
        std::cerr << "Couldn’t find " << value << "\n";
        exit(1);
    } else {
        return nameMap.at(value);
    }
}

z3::expr
Let::toZ3Expr(z3::context &cxt, std::map<std::string, z3::expr> &nameMap,
              const std::map<std::string, Z3DefineFun> &defineFunMap) const {
    for (const auto &assgn : defs) {
        auto e = assgn.second->toZ3Expr(cxt, nameMap, defineFunMap);
        auto it = nameMap.insert({assgn.first, e});
        if (!it.second) {
            it.first->second = e;
        }
    }
    return expr->toZ3Expr(cxt, nameMap, defineFunMap);
}

z3::expr
Op::toZ3Expr(z3::context &cxt, std::map<std::string, z3::expr> &nameMap,
             const std::map<std::string, Z3DefineFun> &defineFunMap) const {
    if (defineFunMap.count(opName) > 0) {
        auto fun = defineFunMap.at(opName);
        z3::expr_vector src = fun.vars;
        z3::expr_vector dst(cxt);
        for (const auto &arg : args) {
            dst.push_back(arg->toZ3Expr(cxt, nameMap, defineFunMap));
        }
        assert(src.size() == dst.size());
        return fun.e.substitute(src, dst);
    } else {
        if (opName == "and") {
            z3::expr result =
                args.front()->toZ3Expr(cxt, nameMap, defineFunMap);
            for (size_t i = 1; i < args.size(); ++i) {
                result =
                    result && args.at(i)->toZ3Expr(cxt, nameMap, defineFunMap);
            }
            return result;
        } else if (opName == "or") {
            z3::expr result =
                args.front()->toZ3Expr(cxt, nameMap, defineFunMap);
            for (size_t i = 1; i < args.size(); ++i) {
                result =
                    result || args.at(i)->toZ3Expr(cxt, nameMap, defineFunMap);
            }
            return result;
        } else if (opName == "+") {
            z3::expr result =
                args.front()->toZ3Expr(cxt, nameMap, defineFunMap);
            for (size_t i = 1; i < args.size(); ++i) {
                result =
                    result + args.at(i)->toZ3Expr(cxt, nameMap, defineFunMap);
            }
            return result;
        } else if (opName == "*") {
            z3::expr result =
                args.front()->toZ3Expr(cxt, nameMap, defineFunMap);
            for (size_t i = 1; i < args.size(); ++i) {
                result =
                    result * args.at(i)->toZ3Expr(cxt, nameMap, defineFunMap);
            }
            return result;
        } else if (opName == "distinct") {
            z3::expr_vector z3Args(cxt);
            for (const auto &arg : args) {
                z3Args.push_back(arg->toZ3Expr(cxt, nameMap, defineFunMap));
            }
            return z3::distinct(z3Args);
        } else if (opName == "not") {
            assert(args.size() == 1);
            z3::expr e = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            return !e;
        } else if (opName == "-") {
            if (args.size() == 1) {
                z3::expr e = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
                return -e;
            } else if (args.size() == 2) {
                z3::expr firstArg =
                    args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
                z3::expr secondArg =
                    args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
                return firstArg - secondArg;
            } else {
                std::cerr << "Cannot subtract more than two arguments\n";
                exit(1);
            }
        } else if (opName == "ite") {
            assert(args.size() == 3);
            z3::expr cond = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr ifTrue = args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr ifFalse = args.at(2)->toZ3Expr(cxt, nameMap, defineFunMap);
            return z3::ite(cond, ifTrue, ifFalse);
        } else if (opName == "store") {
            z3::expr array = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr index = args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr val = args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
            return z3::store(array, index, val);
        } else {
            if (args.size() != 2) {
                std::cerr << "Unsupported opname " << opName << "\n";
                exit(1);
            }
            z3::expr firstArg =
                args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr secondArg =
                args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
            if (opName == "=") {
                return firstArg == secondArg;
            } else if (opName == ">=") {
                return firstArg >= secondArg;
            } else if (opName == ">") {
                return firstArg > secondArg;
            } else if (opName == "<=") {
                return firstArg <= secondArg;
            } else if (opName == "<") {
                return firstArg < secondArg;
            } else if (opName == "=>") {
                return z3::implies(firstArg, secondArg);
            } else if (opName == "div") {
                return firstArg / secondArg;
            } else if (opName == "select") {
                return z3::select(firstArg, secondArg);
            } else {
                std::cerr << "Unsupported opname " << opName << "\n";
                exit(1);
            }
        }
    }
}

void FunDef::toZ3(z3::context &cxt, z3::solver & /* unused */,
                  std::map<std::string, z3::expr> &nameMap,
                  std::map<std::string, Z3DefineFun> &defineFunMap) const {
    z3::expr_vector vars(cxt);
    for (const auto &arg : args) {
        if (arg.type->getTag() == TypeTag::Int) {
            z3::expr c = cxt.int_const(arg.name.c_str());
            vars.push_back(c);
            auto it = nameMap.insert({arg.name, c});
            if (!it.second) {
                it.first->second = c;
            }
        } else if (arg.type->getTag() == TypeTag::Array) {
            z3::sort intArraySort =
                cxt.array_sort(cxt.int_sort(), cxt.int_sort());
            z3::expr c = cxt.constant(arg.name.c_str(), intArraySort);
            vars.push_back(c);
            auto it = nameMap.insert({arg.name, c});
            if (!it.second) {
                it.first->second = c;
            }
        } else {
            std::cerr << "Unknown argument type: " << *arg.type->toSExpr()
                      << "\n";
            exit(1);
        }
    }
    z3::expr z3Body = body->toZ3Expr(cxt, nameMap, defineFunMap);
    defineFunMap.insert({funName, {vars, z3Body}});
}

SharedSMTRef nestLets(SharedSMTRef clause, std::vector<Assignment> defs) {
    SharedSMTRef lets = clause;
    set<string> uses;
    std::vector<Assignment> defsAccum;
    for (auto i = defs.rbegin(), e = defs.rend(); i != e; ++i) {
        if (uses.find(i->first) != uses.end()) {
            lets = make_unique<Let>(defsAccum, lets);
            uses = set<string>();
            defsAccum = std::vector<Assignment>();
        }
        defsAccum.insert(defsAccum.begin(), *i);
        for (auto use : i->second->uses()) {
            uses.insert(use);
        }
    }
    if (!defsAccum.empty()) {
        lets = make_unique<Let>(defsAccum, lets);
    }
    return lets;
}

SharedSMTRef makeSMTRef(SharedSMTRef arg) { return arg; }
SharedSMTRef makeSMTRef(std::string arg) { return stringExpr(arg); }

unique_ptr<ConstantString> stringExpr(std::string name) {
    return make_unique<ConstantString>(name);
}

unique_ptr<const Op> makeOp(std::string opName, std::vector<std::string> args) {
    std::vector<SharedSMTRef> smtArgs;
    for (auto arg : args) {
        smtArgs.push_back(stringExpr(arg));
    }
    return make_unique<Op>(opName, smtArgs);
}

unique_ptr<const Assignment> makeAssignment(string name, SharedSMTRef val) {
    return make_unique<Assignment>(name, val);
}
bool isArray(const Type &type) { return type.getTag() == TypeTag::Array; }

unique_ptr<SMTExpr> memoryVariable(string name) {
    return make_unique<TypedVariable>(name, memoryType());
}
}
