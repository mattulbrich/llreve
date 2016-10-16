/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Helper.h"

#include "Memory.h"
#include "Opts.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"

using smt::SharedSMTRef;
using smt::SMTRef;
using smt::stringExpr;
using std::set;
using std::string;
using std::unique_ptr;
using std::vector;

SMTRef instrLocation(const llvm::Value *val) {
    if (!val->getName().empty()) {
        return stringExpr(string(val->getName()) + "_OnStack");
    }
    return stringExpr("UnknownLocation");
}

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef instrNameOrVal(const llvm::Value *val, const llvm::Type *ty) {
    if (const auto constInt = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        const auto apInt = constInt->getValue();
        if (apInt.isIntN(1) && ty->isIntegerTy(1)) {
            return stringExpr(apInt.getBoolValue() ? "true" : "false");
        }
        if (apInt.isNegative()) {
            if (SMTGenerationOpts::getInstance().BitVect) {
                return smt::makeOp(
                    "bvneg",
                    smt::makeOp(
                        "_",
                        "bv" + apInt.toString(10, true).substr(1, string::npos),
                        std::to_string(ty->getIntegerBitWidth())));
            } else {
                return makeOp("-", stringExpr(apInt.toString(10, true).substr(
                                       1, string::npos)));
            }
        } else {
            if (SMTGenerationOpts::getInstance().BitVect) {
                if (ty->isVoidTy()) {
                    return smt::makeOp("_", "bv" + apInt.toString(10, true),
                                       std::to_string(apInt.getBitWidth()));
                }
                return smt::makeOp("_", "bv" + apInt.toString(10, true),
                                   std::to_string(ty->getIntegerBitWidth()));
            } else {
                return stringExpr(apInt.toString(10, true));
            }
        }
    }
    if (llvm::isa<llvm::ConstantPointerNull>(val)) {
        if (SMTGenerationOpts::getInstance().BitVect) {
            return smt::makeOp("_", "bv0", "64");
        } else {
            return stringExpr("0");
        }
    }
    if (const auto gep = llvm::dyn_cast<llvm::GEPOperator>(val)) {
        if (!llvm::isa<llvm::Instruction>(val)) {
            return resolveGEP(*gep);
        }
    }

    if (const auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(val)) {
        if (constExpr->getOpcode() == llvm::Instruction::IntToPtr) {
            return instrNameOrVal(constExpr->getOperand(0),
                                  constExpr->getOperand(0)->getType());
        }
    }
    if (llvm::isa<llvm::GlobalValue>(val)) {
        return stringExpr(val->getName());
    }
    if (val->getName().empty()) {
        logErrorData("Unnamed variable\n", *val);
        exit(1);
    }
    return stringExpr(val->getName());
}

int typeSize(llvm::Type *Ty, const llvm::DataLayout &layout) {
    if (!SMTGenerationOpts::getInstance().NoByteHeap) {
        return static_cast<int>(layout.getTypeAllocSize(Ty));
    }
    if (auto IntTy = llvm::dyn_cast<llvm::IntegerType>(Ty)) {
        if (IntTy->getBitWidth() <= 64) {
            return 1;
        }
        logError("Unsupported integer bitwidth: " +
                 std::to_string(IntTy->getBitWidth()) + "\n");
    }
    if (Ty->isDoubleTy()) {
        return 1;
    }
    if (auto structTy = llvm::dyn_cast<llvm::StructType>(Ty)) {
        int size = 0;
        for (auto elTy : structTy->elements()) {
            size += typeSize(elTy, layout);
        }
        return size;
    }
    if (auto arrayTy = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
        return static_cast<int>(arrayTy->getNumElements()) *
               typeSize(arrayTy->getElementType(), layout);
    }
    if (llvm::isa<llvm::PointerType>(Ty)) {
        logWarning("pointer size: " +
                   std::to_string(Ty->getPrimitiveSizeInBits()) + "\n");
        // TODO: This should come from a DataLayout
        return 4;
    }
    logErrorData("Couldn’t calculate size of type\n", *Ty);
    return 0;
}

/// Filter vars to only include the ones from Program
std::vector<smt::SortedVar> filterVars(int program,
                                       std::vector<smt::SortedVar> vars) {
    std::vector<smt::SortedVar> filteredVars;
    for (const auto &var : vars) {
        if (varBelongsTo(var.name, program)) {
            filteredVars.push_back(var);
        }
    }
    return filteredVars;
}

bool varBelongsTo(std::string varName, int program) {
    const std::string programName = std::to_string(program);
    const auto pos = varName.rfind("$");
    return varName.substr(pos + 1, programName.length()) == programName;
}

string argSort(string arg) {
    if (std::regex_match(arg, HEAP_REGEX) || arg == "HEAP$1_res" ||
        arg == "HEAP$2_res") {
        return "(Array Int Int)";
    }
    return "Int";
}

string llvmTypeToSMTSort(const llvm::Type *type) {
    if (!SMTGenerationOpts::getInstance().BitVect) {
        return "Int";
    }
    if (type->isPointerTy()) {
        return "(_ BitVec 64)";
    } else if (type->isIntegerTy()) {
        return "(_ BitVec " + std::to_string(type->getIntegerBitWidth()) + ")";
    } else if (type->isVoidTy()) {
        // Void is always a constant zero
        return "Int";
    } else if (type->isLabelTy()) {
        // These types will never arise in the generated SMT but giving it a
        // dummy type avoids a special case when searching for free variables
        return "LABEL";
    } else {
        logErrorData("Unsupported type\n", *type);
        exit(1);
    }
}

smt::SortedVar llvmValToSortedVar(const llvm::Value *val) {
    return smt::SortedVar(val->getName(), llvmTypeToSMTSort(val->getType()));
}

std::string arrayType() {
    return SMTGenerationOpts::getInstance().BitVect
               ? "(Array (_ BitVec 64) (_ BitVec 8))"
               : "(Array Int Int)";
}

std::string stackPointerType() { return "Int"; }

smt::SortedVar toSMTSortedVar(smt::SortedVar var) {
    return smt::SortedVar(var.name, getSMTType(var.type));
}

std::string heapName(int progIndex) {
    return "HEAP$" + std::to_string(progIndex);
}

std::string stackName(int progIndex) {
    return "STACK$" + std::to_string(progIndex);
}

std::string stackPointerName(int progIndex) {
    return "SP$" + std::to_string(progIndex);
}

std::vector<std::string> &split(const std::string &s, char delim,
                                std::vector<std::string> &elems) {
    std::stringstream ss(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        elems.push_back(item);
    }
    return elems;
}

std::vector<std::string> split(const std::string &s, char delim) {
    std::vector<std::string> elems;
    split(s, delim, elems);
    return elems;
}

vector<smt::SortedVar> functionArgs(const llvm::Function &fun) {
    vector<smt::SortedVar> args;
    for (auto &arg : fun.args()) {
        auto sVar = llvmValToSortedVar(&arg);
        args.push_back(sVar);
        if (SMTGenerationOpts::getInstance().Stack &&
            arg.getType()->isPointerTy()) {
            args.push_back({sVar.name + "_OnStack", "Bool"});
        }
    }
    return args;
}

auto callsTransitively(const llvm::Function &caller,
                       const llvm::Function &callee) -> bool {
    set<const llvm::Function *> visited;
    set<const llvm::Function *> toProcess;
    toProcess.insert(&caller);
    while (!toProcess.empty()) {
        const auto called = calledFunctions(**toProcess.begin());

        if (called.find(&callee) != called.end()) {
            return true;
        }

        visited.insert(*toProcess.begin());
        toProcess.erase(toProcess.begin());
        std::set_difference(called.begin(), called.end(), visited.begin(),
                            visited.end(),
                            std::inserter(toProcess, toProcess.begin()));
    }
    return false;
}
auto calledFunctions(const llvm::Function &f) -> set<const llvm::Function *> {
    set<const llvm::Function *> called;
    for (const auto &bb : f) {
        for (const auto &instr : bb) {
            if (auto call = llvm::dyn_cast<llvm::CallInst>(&instr)) {
                called.insert(call->getCalledFunction());
            }
        }
    }
    return called;
}
