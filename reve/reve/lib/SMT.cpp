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
using std::set;
using std::string;
using std::vector;

using namespace llreve::opts;
using namespace sexpr;

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
        if (this->value.isInteger()) {
            // We need to make the literal a decimal, otherwise it will be
            // interpreted as an Int instead of a Real
            stringRepr = stringRepr + ".0";
        }
        return sexprFromString(stringRepr);
    }
}

SExprRef ConstantInt::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        unsigned bitWidth = value.getBitWidth();
        unsigned hexWidth = bitWidth / 4;
        string hexValue = value.toString(16, false);
        unsigned unpaddedHexWidth = hexValue.size();
        // Pad the string with 0s
        for (int i = 0; i < hexWidth - unpaddedHexWidth; ++i) {
            hexValue = '0' + hexValue;
        }
        assert(bitWidth == 4 * hexValue.size());
        return sexprFromString("#x" + hexValue);
    } else {
        if (value.isNegative()) {
            SExprVec args;
            args.push_back(sexprFromString((-value).toString(10, true)));
            return std::make_unique<Apply>("-", std::move(args));
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
    SExprVec args;
    SExprRef logicPtr = make_unique<Value>(logic);

    args.push_back(std::move(logicPtr));
    return std::make_unique<Apply>("set-logic", std::move(args));
}

SExprRef CheckSat::toSExpr() const {
    SExprVec args;
    return std::make_unique<Apply>("check-sat", std::move(args));
}

SExprRef Query::toSExpr() const {
    SExprVec args;
    args.push_back(make_unique<Value>(queryName));
    args.push_back(make_unique<Value>(":print-certificate"));
    args.push_back(make_unique<Value>("true"));
    return std::make_unique<Apply>("query", std::move(args));
}

SExprRef GetModel::toSExpr() const {
    SExprVec args;
    return std::make_unique<Apply>("get-model", std::move(args));
}

SExprRef Assert::toSExpr() const {
    SExprVec args;
    args.push_back(expr->toSExpr());
    const string keyword =
        SMTGenerationOpts::getInstance().OutputFormat == SMTFormat::Z3
            ? "rule"
            : "assert";
    return std::make_unique<Apply>(keyword, std::move(args));
}

SExprRef Forall::toSExpr() const {
    if (vars.empty()) {
        return expr->toSExpr();
    }
    SExprVec args;
    SExprVec sortedVars;
    for (auto &sortedVar : vars) {
        sortedVars.push_back(sortedVar.toSExpr());
    }
    args.push_back(std::make_unique<List>(std::move(sortedVars)));
    args.push_back(expr->toSExpr());
    return std::make_unique<Apply>("forall", std::move(args));
}

SExprRef SortedVar::toSExpr() const {
    SExprVec typeSExpr;
    typeSExpr.push_back(type->toSExpr());
    return std::make_unique<Apply>(name, std::move(typeSExpr));
}

SExprRef Let::toSExpr() const {
    SExprVec defSExprs;
    for (const auto &def : defs) {
        SExprVec argSExprs;
        argSExprs.push_back(def.second->toSExpr());
        defSExprs.push_back(
            std::make_unique<Apply>(def.first, std::move(argSExprs)));
    }
    SExprVec args;
    args.push_back(std::make_unique<List>(std::move(defSExprs)));
    args.push_back(expr->toSExpr());
    return std::make_unique<Apply>("let", std::move(args));
}

SExprRef Op::toSExpr() const {
    SExprVec argSExprs;
    // Special case for emty and
    if (opName == "and" && args.empty()) {
        return make_unique<Value>("true");
    }
    if (opName == "and" && args.size() == 1) {
        return args.front()->toSExpr();
    }
    if (opName == "=>" && args.at(1)->isConstantFalse()) {
        return makeOp("not", args.at(0))->toSExpr();
    }
    for (auto &arg : args) {
        argSExprs.push_back(arg->toSExpr());
    }
    return std::make_unique<Apply>(opName, std::move(argSExprs));
}

SExprRef FunDecl::toSExpr() const {
    SExprVec inTypeSExprs;
    for (const auto &inType : inTypes) {
        inTypeSExprs.push_back(inType->toSExpr());
    }
    SExprVec args;
    args.push_back(stringExpr(funName)->toSExpr());
    args.push_back(std::make_unique<List>(std::move(inTypeSExprs)));
    if (SMTGenerationOpts::getInstance().OutputFormat == SMTFormat::SMTHorn) {
        args.push_back(outType->toSExpr());
    }
    const string keyword =
        SMTGenerationOpts::getInstance().OutputFormat == SMTFormat::Z3
            ? "declare-rel"
            : "declare-fun";
    return std::make_unique<Apply>(keyword, std::move(args));
}

SExprRef FunDef::toSExpr() const {
    SExprVec argSExprs;
    for (auto arg : args) {
        argSExprs.push_back(arg.toSExpr());
    }
    SExprVec args;
    args.push_back(stringExpr(funName)->toSExpr());
    args.push_back(std::make_unique<List>(std::move(argSExprs)));
    args.push_back(outType->toSExpr());
    args.push_back(body->toSExpr());
    return std::make_unique<Apply>("define-fun", std::move(args));
}

SExprRef Comment::toSExpr() const {
    return make_unique<class sexpr::Comment>(val);
}

SExprRef VarDecl::toSExpr() const {
    SExprVec args;
    args.push_back(stringExpr(var.name)->toSExpr());
    args.push_back(var.type->toSExpr());
    return std::make_unique<Apply>("declare-var", std::move(args));
}

SExprRef FPCmp::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Floating point predicates for bitvectors are not yet "
                 "impleneted\n");
        exit(1);
    } else {
        SExprVec args;
        args.push_back(op0->toSExpr());
        args.push_back(op1->toSExpr());
        switch (this->op) {
        case Predicate::False:
            return sexprFromString("false");
        case Predicate::True:
            return sexprFromString("true");
        case Predicate::OEQ:
        case Predicate::UEQ:
            return std::make_unique<Apply>("=", std::move(args));
        case Predicate::OGT:
        case Predicate::UGT:
            return std::make_unique<Apply>(">", std::move(args));
        case Predicate::OGE:
        case Predicate::UGE:
            return std::make_unique<Apply>(">=", std::move(args));
        case Predicate::OLT:
        case Predicate::ULT:
            return std::make_unique<Apply>("<", std::move(args));
        case Predicate::OLE:
        case Predicate::ULE:
            return std::make_unique<Apply>("<=", std::move(args));
        case Predicate::ONE:
        case Predicate::UNE:
            return std::make_unique<Apply>("distinct", std::move(args));
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
        SExprVec args;
        args.push_back(op0->toSExpr());
        args.push_back(op1->toSExpr());
        switch (this->op) {
        case Opcode::FAdd:
            return std::make_unique<Apply>("+", std::move(args));
        case Opcode::FSub:
            return std::make_unique<Apply>("-", std::move(args));
        case Opcode::FMul:
            return std::make_unique<Apply>("*", std::move(args));
        case Opcode::FDiv:
            return std::make_unique<Apply>("/", std::move(args));
        case Opcode::FRem:
            logError("SMT reals don’t support a remainder operation\n");
            exit(1);
        }
    }
}

SExprRef TypeCast::toSExpr() const {
    // Extending 1bit integers (i.e. booleans) to integers is an SMT type
    // conversion and we have to deal with it separately
    if (destType->getTag() == TypeTag::Int &&
        static_cast<IntType &>(*destType).bitWidth > 1 &&
        sourceType->getTag() == TypeTag::Int &&
        static_cast<IntType &>(*sourceType).bitWidth == 1) {
        unsigned destBitWidth = static_cast<IntType &>(*destType).bitWidth;
        vector<SharedSMTRef> args = {
            operand,
            std::make_unique<ConstantInt>(llvm::APInt(destBitWidth, 1)),
            std::make_unique<ConstantInt>(llvm::APInt(destBitWidth, 0))};
        return Op("ite", std::move(args)).toSExpr();
    }
    if (SMTGenerationOpts::getInstance().BitVect) {
        SExprVec args;
        args.push_back(operand->toSExpr());
        switch (this->op) {
        case llvm::Instruction::Trunc: {
            assert(destType->getTag() == TypeTag::Int);
            IntType intDestType = static_cast<IntType &>(*destType);
            unsigned bitWidth = intDestType.bitWidth;
            string opName =
                "(_ extract " + std::to_string(bitWidth - 1) + " 0)";
            return std::make_unique<Apply>(opName, std::move(args));
        }
        case llvm::Instruction::ZExt: {
            unsigned destBitWidth = static_cast<IntType &>(*destType).bitWidth;
            unsigned sourceBitWidth =
                static_cast<IntType &>(*sourceType).bitWidth;
            string opName = "(_ zero_extend " +
                            std::to_string(destBitWidth - sourceBitWidth) + ")";
            return std::make_unique<Apply>(opName, std::move(args));
        }
        case llvm::Instruction::SExt: {
            unsigned destBitWidth = static_cast<IntType &>(*destType).bitWidth;
            unsigned sourceBitWidth =
                static_cast<IntType &>(*sourceType).bitWidth;
            string opName = "(_ sign_extend " +
                            std::to_string(destBitWidth - sourceBitWidth) + ")";
            return std::make_unique<Apply>(opName, std::move(args));
        }
        default:
            logError("Unsupported cast operation in bitvector mode: " +
                     std::to_string(this->op) + "\n");
            exit(1);
        }
    } else {
        SExprVec args;
        args.push_back(operand->toSExpr());
        switch (this->op) {
        case llvm::Instruction::SExt:
        case llvm::Instruction::ZExt:
        case llvm::Instruction::Trunc:
        case llvm::Instruction::BitCast:
            return operand->toSExpr();
        case llvm::Instruction::SIToFP:
            return std::make_unique<Apply>("to_real", std::move(args));
        default:
            logError("Unsupported opcode: " + std::to_string(this->op) + "\n");
            exit(1);
        }
    }
}

struct CollectUsesVisitor : BottomUpVisitor {
    llvm::StringSet<> uses;
    void dispatch(ConstantString &str) override { uses.insert(str.value); }
    void dispatch(TypedVariable &var) override { uses.insert(var.name); }
};

static llvm::StringSet<> collectUses(SMTExpr &expr) {
    CollectUsesVisitor usesVisitor;
    expr.accept(usesVisitor);
    return usesVisitor.uses;
}

// Implementations of compressLets

SharedSMTRef SMTExpr::compressLets(AssignmentVec defs) {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef Assert::compressLets(AssignmentVec defs) {
    assert(defs.empty());
    unused(defs);
    return make_shared<Assert>(expr->compressLets());
}

SharedSMTRef Forall::compressLets(AssignmentVec defs) {
    return nestLets(make_shared<Forall>(vars, expr->compressLets()), defs);
}

SharedSMTRef CheckSat::compressLets(AssignmentVec defs) {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef GetModel::compressLets(AssignmentVec defs) {
    assert(defs.empty());
    unused(defs);
    return shared_from_this();
}

SharedSMTRef Let::compressLets(AssignmentVec passedDefs) {
    passedDefs.insert(passedDefs.end(), defs.begin(), defs.end());
    return expr->compressLets(std::move(passedDefs));
}

SharedSMTRef Op::compressLets(AssignmentVec defs) {
    std::vector<SharedSMTRef> compressedArgs(args.size());
    for (size_t i = 0; i < args.size(); ++i) {
        compressedArgs.at(i) = args.at(i)->compressLets();
    }
    return nestLets(
        make_shared<Op>(opName, std::move(compressedArgs), instantiate), defs);
}

SharedSMTRef ConstantString::compressLets(AssignmentVec defs) {
    return nestLets(shared_from_this(), defs);
}

SharedSMTRef ConstantBool::compressLets(AssignmentVec defs) {
    return nestLets(shared_from_this(), defs);
}

// Implementations of renameAssignments

SharedSMTRef SMTExpr::renameAssignments(map<string, int> variableMap) {
    return shared_from_this();
}

SharedSMTRef ConstantString::renameAssignments(map<string, int> variableMap) {
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

SharedSMTRef TypedVariable::renameAssignments(map<string, int> variableMap) {
    string newName = name;
    if (variableMap.find(newName) != variableMap.end()) {
        newName += "_" + std::to_string(variableMap.at(newName));
    }
    return make_unique<TypedVariable>(newName, type->copy());
}

SharedSMTRef Assert::renameAssignments(map<string, int> variableMap) {
    assert(variableMap.empty());
    return make_shared<Assert>(expr->renameAssignments(variableMap));
}

SharedSMTRef Let::renameAssignments(map<string, int> variableMap) {
    AssignmentVec newDefs;
    auto newVariableMap = variableMap;
    for (const auto &assgn : defs) {
        int newIndex = ++newVariableMap[assgn.first];
        newDefs.push_back({assgn.first + "_" + std::to_string(newIndex),
                           assgn.second->renameAssignments(variableMap)});
    }
    return make_shared<Let>(newDefs, expr->renameAssignments(newVariableMap));
}

SharedSMTRef Op::renameAssignments(map<string, int> variableMap) {
    vector<SharedSMTRef> newArgs;
    for (const auto &arg : this->args) {
        newArgs.push_back(arg->renameAssignments(variableMap));
    }
    return make_shared<Op>(opName, newArgs, instantiate);
}

SharedSMTRef FPCmp::renameAssignments(map<string, int> variableMap) {
    auto newOp0 = op0->renameAssignments(variableMap);
    auto newOp1 = op1->renameAssignments(variableMap);
    return make_shared<FPCmp>(op, type->copy(), newOp0, newOp1);
}

SharedSMTRef BinaryFPOperator::renameAssignments(map<string, int> variableMap) {
    auto newOp0 = op0->renameAssignments(variableMap);
    auto newOp1 = op1->renameAssignments(variableMap);
    return make_shared<BinaryFPOperator>(op, type->copy(), newOp0, newOp1);
}

SharedSMTRef TypeCast::renameAssignments(map<string, int> variableMap) {
    return std::make_unique<TypeCast>(op, sourceType->copy(), destType->copy(),
                                      operand->renameAssignments(variableMap));
}

SharedSMTRef Forall::renameAssignments(map<string, int> variableMap) {
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

SharedSMTRef SMTExpr::mergeImplications(std::vector<SharedSMTRef> conditions) {
    if (conditions.empty()) {
        return shared_from_this();
    } else {
        return makeOp("=>", make_shared<Op>("and", conditions),
                      shared_from_this());
    }
}

SharedSMTRef Assert::mergeImplications(std::vector<SharedSMTRef> conditions) {
    assert(conditions.empty());
    return make_shared<Assert>(expr->mergeImplications(std::move(conditions)));
}

SharedSMTRef Let::mergeImplications(std::vector<SharedSMTRef> conditions) {
    return make_shared<Let>(defs,
                            expr->mergeImplications(std::move(conditions)));
}

SharedSMTRef Op::mergeImplications(std::vector<SharedSMTRef> conditions) {
    if (opName == "=>") {
        assert(args.size() == 2);
        conditions.push_back(args.at(0));
        return args.at(1)->mergeImplications(std::move(conditions));
    } else {
        return makeOp("=>", make_shared<Op>("and", conditions),
                      shared_from_this());
    }
}

SharedSMTRef Forall::mergeImplications(std::vector<SharedSMTRef> conditions) {
    return std::make_shared<Forall>(
        vars, expr->mergeImplications(std::move(conditions)));
}

// Implementations of splitConjunctions()

vector<SharedSMTRef> SMTExpr::splitConjunctions() {
    return {shared_from_this()};
}

vector<SharedSMTRef> Assert::splitConjunctions() {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Assert>(std::move(expr));
    }
    return smtExprs;
}

vector<SharedSMTRef> Let::splitConjunctions() {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Let>(defs, std::move(expr));
    }
    return smtExprs;
}

vector<SharedSMTRef> Op::splitConjunctions() {
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

vector<SharedSMTRef> Forall::splitConjunctions() {
    vector<SharedSMTRef> smtExprs = expr->splitConjunctions();
    for (auto &expr : smtExprs) {
        expr = make_shared<Forall>(vars, std::move(expr));
    }
    return smtExprs;
}

// Implementations of instantiateArrays

SharedSMTRef SMTExpr::instantiateArrays() { return shared_from_this(); }

SharedSMTRef Assert::instantiateArrays() {
    return make_shared<Assert>(expr->instantiateArrays());
}

SharedSMTRef Forall::instantiateArrays() {
    return make_shared<Forall>(vars, expr->instantiateArrays());
}

SharedSMTRef Let::instantiateArrays() {
    return make_shared<Let>(defs, expr->instantiateArrays());
}

SharedSMTRef Op::instantiateArrays() {
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

SharedSMTRef FunDef::instantiateArrays() {
    return make_shared<FunDef>(funName, args, outType->copy(),
                               body->instantiateArrays());
}

SharedSMTRef FunDecl::instantiateArrays() {
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
        // The actual match counts too
        assert(matchResult.size() == 3 || matchResult.size() == 4);
        return make_unique<HeapInfo>(matchResult[1], matchResult[2],
                                     matchResult[3]);
    }
    return nullptr;
}

// Implementations of removeForalls

SharedSMTRef SMTExpr::removeForalls(set<SortedVar> &introducedVariables) {
    return shared_from_this();
}
SharedSMTRef Assert::removeForalls(set<SortedVar> &introducedVariables) {
    return make_shared<Assert>(expr->removeForalls(introducedVariables));
}
SharedSMTRef Forall::removeForalls(set<SortedVar> &introducedVariables) {
    for (const auto &var : vars) {
        introducedVariables.insert(var);
    }
    return expr->removeForalls(introducedVariables);
}
SharedSMTRef Op::removeForalls(set<SortedVar> &introducedVariables) {
    vector<SharedSMTRef> newArgs(args.size());
    for (size_t i = 0; i < args.size(); ++i) {
        newArgs[i] = args[i]->removeForalls(introducedVariables);
    }
    return make_shared<Op>(opName, std::move(newArgs), instantiate);
}
SharedSMTRef Let::removeForalls(set<SortedVar> &introducedVariables) {
    return make_shared<Let>(defs, expr->removeForalls(introducedVariables));
}

// Implementations of inlineLets

SharedSMTRef SMTExpr::inlineLets(map<string, SharedSMTRef> assignments) {
    return shared_from_this();
}

SharedSMTRef Assert::inlineLets(map<string, SharedSMTRef> assignments) {
    return make_unique<Assert>(expr->inlineLets(assignments));
}

SharedSMTRef Let::inlineLets(map<string, SharedSMTRef> assignments) {
    for (const auto &def : defs) {
        assignments[def.first] = def.second->inlineLets(assignments);
    }
    return expr->inlineLets(assignments);
}

SharedSMTRef Forall::inlineLets(map<string, SharedSMTRef> assignments) {
    for (const auto &var : vars) {
        assignments.erase(var.name);
    }
    return make_unique<Forall>(vars, expr->inlineLets(assignments));
}

SharedSMTRef Op::inlineLets(map<string, SharedSMTRef> assignments) {
    vector<SharedSMTRef> newArgs;
    for (const auto &arg : args) {
        newArgs.push_back(arg->inlineLets(assignments));
    }
    return make_unique<Op>(opName, newArgs);
}

SharedSMTRef TypedVariable::inlineLets(map<string, SharedSMTRef> assignments) {
    auto mapIt = assignments.find(name);
    if (mapIt == assignments.end()) {
        return shared_from_this();
    }
    return mapIt->second;
}

SharedSMTRef ConstantString::inlineLets(map<string, SharedSMTRef> assignments) {
    auto mapIt = assignments.find(value);
    if (mapIt == assignments.end()) {
        return shared_from_this();
    }
    return mapIt->second;
}

SharedSMTRef TypeCast::inlineLets(map<string, SharedSMTRef> assignments) {
    return std::make_unique<TypeCast>(op, sourceType->copy(), destType->copy(),
                                      operand->inlineLets(assignments));
}

SharedSMTRef
BinaryFPOperator::inlineLets(map<string, SharedSMTRef> assignments) {
    return make_unique<BinaryFPOperator>(op, type->copy(),
                                         op0->inlineLets(assignments),
                                         op1->inlineLets(assignments));
}

SharedSMTRef FPCmp::inlineLets(map<string, SharedSMTRef> assignments) {
    return make_unique<FPCmp>(op, type->copy(), op0->inlineLets(assignments),
                              op1->inlineLets(assignments));
}

// Implementations for using the z3 API

void VarDecl::toZ3(z3::context &cxt, z3::solver & /* unused */,
                   llvm::StringMap<z3::expr> &nameMap,
                   llvm::StringMap<Z3DefineFun> & /* unused */) const {
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
    } else if (var.type->getTag() == TypeTag::Bool) {
        z3::expr c = cxt.bool_const(var.name.c_str());
        auto it = nameMap.insert({var.name, c});
        if (!it.second) {
            it.first->second = c;
        }
    } else {
        logError("Unsupported type\n");
        exit(1);
    }
}

void Assert::toZ3(z3::context &cxt, z3::solver &solver,
                  llvm::StringMap<z3::expr> &nameMap,
                  llvm::StringMap<Z3DefineFun> &defineFunMap) const {
    solver.add(expr->toZ3Expr(cxt, nameMap, defineFunMap));
}

void CheckSat::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                    llvm::StringMap<z3::expr> & /* unused */,
                    llvm::StringMap<Z3DefineFun> & /* unused */) const {
    /* noop */
}

void GetModel::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                    llvm::StringMap<z3::expr> & /* unused */,
                    llvm::StringMap<Z3DefineFun> & /* unused */) const {
    /* noop */
}

void SMTExpr::toZ3(z3::context & /* unused */, z3::solver & /* unused */,
                   llvm::StringMap<z3::expr> & /* unused */,
                   llvm::StringMap<Z3DefineFun> &
                   /* unused */) const {
    logError("Unsupported smt toplevel\n");
    std::cerr << *toSExpr();
    exit(1);
}

z3::expr
SMTExpr::toZ3Expr(z3::context & /* unused */,
                  llvm::StringMap<z3::expr> & /* unused */,
                  const llvm::StringMap<Z3DefineFun> & /* unused */) const {
    logError("Unsupported smtexpr\n");
    std::cerr << *toSExpr();
    exit(1);
}

z3::expr TypeCast::toZ3Expr(z3::context &cxt,
                            llvm::StringMap<z3::expr> &nameMap,
                            const llvm::StringMap<Z3DefineFun> &funMap) const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Bitvector mode not implemented for using the Z3 API for "
                 "typecasts\n");
        exit(1);
    } else {
        return operand->toZ3Expr(cxt, nameMap, funMap);
    }
}

z3::expr TypedVariable::toZ3Expr(
    z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
    const llvm::StringMap<Z3DefineFun> & /* unused */) const {
    if (nameMap.count(name) == 0) {
        std::cerr << "Z3 serialization error: '" << name
                  << "' not in variable map\n";
        exit(1);
    } else {
        return nameMap.find(name)->second;
    }
}

z3::expr ConstantString::toZ3Expr(
    z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
    const llvm::StringMap<Z3DefineFun> & /* unused */) const {
    if (nameMap.count(value) == 0) {
        std::cerr << "Z3 serialization error: '" << value
                  << "' not in variable map\n";
        exit(1);
    } else {
        return nameMap.find(value)->second;
    }
}

z3::expr ConstantBool::toZ3Expr(
    z3::context &cxt, llvm::StringMap<z3::expr> & /* unused */,
    const llvm::StringMap<Z3DefineFun> & /* unused */) const {
    return cxt.bool_val(value);
}

z3::expr
ConstantInt::toZ3Expr(z3::context &cxt,
                      llvm::StringMap<z3::expr> & /* unused */,
                      const llvm::StringMap<Z3DefineFun> & /* unused */) const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        logError("Bitvector serialization for z3 is not yet implemented\n");
        exit(1);
    } else {
        return cxt.int_val(static_cast<__int64>(value.getSExtValue()));
    }
}

z3::expr Let::toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
                       const llvm::StringMap<Z3DefineFun> &defineFunMap) const {
    for (const auto &assgn : defs) {
        auto e = assgn.second->toZ3Expr(cxt, nameMap, defineFunMap);
        auto it = nameMap.insert({assgn.first, e});
        if (!it.second) {
            it.first->second = e;
        }
    }
    return expr->toZ3Expr(cxt, nameMap, defineFunMap);
}

z3::expr Op::toZ3Expr(z3::context &cxt, llvm::StringMap<z3::expr> &nameMap,
                      const llvm::StringMap<Z3DefineFun> &defineFunMap) const {
    if (defineFunMap.count(opName) > 0) {
        auto fun = defineFunMap.find(opName)->second;
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
            assert(args.size() == 3);
            z3::expr array = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr index = args.at(1)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr val = args.at(2)->toZ3Expr(cxt, nameMap, defineFunMap);
            return z3::store(array, index, val);
        } else if (opName == "abs") {
            assert(args.size() == 1);
            z3::expr val = args.at(0)->toZ3Expr(cxt, nameMap, defineFunMap);
            z3::expr cond = val >= 0;
            return z3::ite(cond, val, -val);
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
            } else if (opName == "mod") {
                return z3::expr(cxt, Z3_mk_mod(cxt, firstArg, secondArg));
            } else if (opName == "select") {
                return z3::select(firstArg, secondArg);
            } else if (opName == "xor") {
                return z3::expr(cxt, Z3_mk_xor(cxt, firstArg, secondArg));
            } else {
                std::cerr << "Unsupported opname " << opName << "\n";
                exit(1);
            }
        }
    }
}

void FunDef::toZ3(z3::context &cxt, z3::solver & /* unused */,
                  llvm::StringMap<z3::expr> &nameMap,
                  llvm::StringMap<Z3DefineFun> &defineFunMap) const {
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

SharedSMTRef fastNestLets(SharedSMTRef clause,
                          llvm::ArrayRef<Assignment> defs) {
    for (auto i = defs.rbegin(); i != defs.rend(); ++i) {
        clause = std::make_unique<Let>(AssignmentVec({std::move(*i)}),
                                       std::move(clause));
    }
    return clause;
}

SharedSMTRef nestLets(SharedSMTRef clause, llvm::ArrayRef<Assignment> defs) {
    SharedSMTRef lets = std::move(clause);
    llvm::StringSet<> uses;
    AssignmentVec defsAccum;
    for (auto i = defs.rbegin(), e = defs.rend(); i != e; ++i) {
        if (uses.find(i->first) != uses.end()) {
            std::reverse(defsAccum.begin(), defsAccum.end());
            lets = std::make_unique<Let>(std::move(defsAccum), std::move(lets));
            uses = llvm::StringSet<>();
            defsAccum.clear();
        }
        defsAccum.push_back(*i);
        llvm::StringSet<> usesForExpr = collectUses(*i->second);
        for (const auto &use : usesForExpr) {
            uses.insert(use.getKey());
        }
    }
    if (!defsAccum.empty()) {
        std::reverse(defsAccum.begin(), defsAccum.end());
        lets = std::make_unique<Let>(defsAccum, std::move(lets));
    }
    return lets;
}

SharedSMTRef makeSMTRef(SharedSMTRef arg) { return arg; }
SharedSMTRef makeSMTRef(std::string arg) { return stringExpr(arg); }

unique_ptr<ConstantString> stringExpr(llvm::StringRef name) {
    return std::make_unique<ConstantString>(name);
}

unique_ptr<Op> makeOp(std::string opName,
                      const std::vector<std::string> &args) {
    std::vector<SharedSMTRef> smtArgs;
    for (const auto &arg : args) {
        smtArgs.push_back(stringExpr(arg));
    }
    return make_unique<Op>(opName, smtArgs);
}

unique_ptr<Assignment> makeAssignment(string name, SharedSMTRef val) {
    return make_unique<Assignment>(name, val);
}
bool isArray(const Type &type) { return type.getTag() == TypeTag::Array; }

unique_ptr<SMTExpr> memoryVariable(string name) {
    return make_unique<TypedVariable>(name, memoryType());
}

unique_ptr<TypedVariable> typedVariableFromSortedVar(const SortedVar &var) {
    return make_unique<TypedVariable>(var.name, var.type->copy());
}

SortedVar typedVariableFromSortedVar(const TypedVariable &var) {
    return {var.name, var.type->copy()};
}

void SetLogic::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void Assert::accept(BottomUpVisitor &visitor) {
    expr->accept(visitor);
    visitor.dispatch(*this);
}
void TypedVariable::accept(BottomUpVisitor &visitor) {
    visitor.dispatch(*this);
}
void Forall::accept(BottomUpVisitor &visitor) {
    expr->accept(visitor);
    visitor.dispatch(*this);
}
void CheckSat::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void GetModel::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void Let::accept(BottomUpVisitor &visitor) {
    expr->accept(visitor);
    for (auto &def : defs) {
        def.second->accept(visitor);
    }
    visitor.dispatch(*this);
}
void ConstantFP::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void ConstantInt::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void ConstantBool::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void ConstantString::accept(BottomUpVisitor &visitor) {
    visitor.dispatch(*this);
}
void Op::accept(BottomUpVisitor &visitor) {
    for (auto &arg : args) {
        arg->accept(visitor);
    }
    visitor.dispatch(*this);
}
void FPCmp::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void BinaryFPOperator::accept(BottomUpVisitor &visitor) {
    op0->accept(visitor);
    op1->accept(visitor);
    visitor.dispatch(*this);
}
void TypeCast::accept(BottomUpVisitor &visitor) {
    operand->accept(visitor);
    visitor.dispatch(*this);
}
void Query::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void FunDecl::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void FunDef::accept(BottomUpVisitor &visitor) {
    body->accept(visitor);
    visitor.dispatch(*this);
}
void Comment::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }
void VarDecl::accept(BottomUpVisitor &visitor) { visitor.dispatch(*this); }

void SetLogic::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void Assert::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
    expr->accept(visitor);
}
void TypedVariable::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void Forall::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
    expr->accept(visitor);
}
void CheckSat::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void GetModel::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void Let::accept(TopDownVisitor &visitor) {
    // It is slightly unclear if bindings should be traversed before or after
    // the let itself. However let statements cannot be recursive and it thus
    // makes sense to traverse them first.
    for (auto &def : defs) {
        def.second->accept(visitor);
    }
    visitor.dispatch(*this);
    expr->accept(visitor);
}
void ConstantFP::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void ConstantInt::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void ConstantBool::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void ConstantString::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
}
void Op::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
    for (auto &arg : args) {
        arg->accept(visitor);
    }
}
void FPCmp::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void BinaryFPOperator::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
    op0->accept(visitor);
    op1->accept(visitor);
}
void TypeCast::accept(TopDownVisitor &visitor) {
    operand->accept(visitor);
    visitor.dispatch(*this);
}
void Query::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void FunDecl::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void FunDef::accept(TopDownVisitor &visitor) {
    visitor.dispatch(*this);
    body->accept(visitor);
}
void Comment::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
void VarDecl::accept(TopDownVisitor &visitor) { visitor.dispatch(*this); }
}

static size_t lexerOffset;
static const char *lexerInput;
void setSMTLexerInput(const char *input) {
    lexerOffset = 0;
    lexerInput = input;
}
int readInputForLexer(char *buffer, int *numBytesRead, int maxBytesToRead) {
    int numBytesToRead = maxBytesToRead;
    int bytesRemaining = strlen(lexerInput) - lexerOffset;
    if (numBytesToRead > bytesRemaining) {
        numBytesToRead = bytesRemaining;
    }
    memcpy(buffer, lexerInput + lexerOffset, numBytesToRead);
    *numBytesRead = numBytesToRead;
    lexerOffset += numBytesToRead;
    return 0;
}
