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

#include "Logging.h"
#include "Opts.h"
#include "SMT.h"

#include <string>

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

auto instrLocation(const llvm::Value *val) -> std::unique_ptr<smt::SMTExpr>;
// convenience wrapper that uses the type of the passed value
auto instrNameOrVal(const llvm::Value *val) -> std::unique_ptr<smt::SMTExpr>;
auto instrNameOrVal(const llvm::Value *val, const llvm::Type *ty)
    -> std::unique_ptr<smt::SMTExpr>;
auto typeSize(llvm::Type *ty, const llvm::DataLayout &layout) -> int;
template <typename T> std::unique_ptr<smt::SMTExpr> resolveGEP(T &gep) {
    std::vector<smt::SharedSMTRef> args;
    args.push_back(instrNameOrVal(gep.getPointerOperand()));
    const auto type = gep.getSourceElementType();
    std::vector<llvm::Value *> indices;
    for (auto ix = gep.idx_begin(), e = gep.idx_end(); ix != e; ++ix) {
        // Try several ways of finding the module
        const llvm::Module *mod = nullptr;
        if (auto instr = llvm::dyn_cast<llvm::Instruction>(&gep)) {
            mod = instr->getModule();
        }
        if (auto global =
                llvm::dyn_cast<llvm::GlobalValue>(gep.getPointerOperand())) {
            mod = global->getParent();
        }
        if (mod == nullptr) {
            logErrorData("Couldn’t cast gep to an instruction:\n", gep);
        }
        indices.push_back(*ix);
        const auto indexedType = llvm::GetElementPtrInst::getIndexedType(
            type, llvm::ArrayRef<llvm::Value *>(indices));
        const auto size = typeSize(indexedType, mod->getDataLayout());
        auto smtIx = instrNameOrVal(*ix);
        if (llreve::opts::SMTGenerationOpts::getInstance().BitVect) {
            smtIx = smt::makeOp(
                "(_ sign_extend " +
                    std::to_string(64 -
                                   (*ix)->getType()->getIntegerBitWidth()) +
                    ")",
                std::move(smtIx));
        }
        if (size == 1) {
            args.push_back(std::move(smtIx));
        } else {
            if (llreve::opts::SMTGenerationOpts::getInstance().BitVect) {
                args.push_back(smt::makeOp(
                    "bvmul",
                    smt::stringExpr("(_ bv" + std::to_string(size) + " 64)"),
                    std::move(smtIx)));
            } else {
                args.push_back(smt::makeOp(
                    "*",
                    std::make_unique<smt::ConstantInt>(llvm::APInt(64, size)),
                    std::move(smtIx)));
            }
        }
    }
    if (llreve::opts::SMTGenerationOpts::getInstance().BitVect) {
        return std::make_unique<smt::Op>("bvadd", args);
    } else {
        return std::make_unique<smt::Op>("+", args);
    }
}

template <typename Key, typename Val>
auto unionWith(std::map<Key, Val> mapA, std::map<Key, Val> mapB,
               std::function<Val(Val, Val)> combine) -> std::map<Key, Val> {
    for (auto &pair : mapB) {
        if (mapA.find(pair.first) == mapA.end()) {
            mapA.emplace(pair.first, std::move(pair.second));
        } else {
            mapA.at(pair.first) =
                combine(std::move(mapA.at(pair.first)), std::move(pair.second));
        }
    }
    return mapA;
}

template <typename KeyA, typename KeyB, typename Val>
auto transpose(std::map<KeyA, std::map<KeyB, Val>> map)
    -> std::map<KeyB, std::map<KeyA, Val>> {
    std::map<KeyB, std::map<KeyA, Val>> mapResult;
    for (auto it : map) {
        for (auto innerIt : it.second) {
            mapResult[innerIt.first][it.first] = innerIt.second;
        }
    }
    return mapResult;
}

template <typename T>
auto setUnion(std::set<T> a, std::set<T> b) -> std::set<T> {
    for (const auto &x : b) {
        a.insert(x);
    }
    return a;
}
template <typename K, typename V>
auto mergeVectorMaps(std::map<K, std::vector<V>> a,
                     std::map<K, std::vector<V>> b)
    -> std::map<K, std::vector<V>> {
    return unionWith<K, std::vector<V>>(std::move(a), std::move(b),
                                        [](std::vector<V> a, std::vector<V> b) {
                                            for (auto &x : b) {
                                                a.push_back(std::move(x));
                                            }
                                            return a;
                                        });
}
template <typename K1, typename K2, typename V>
auto mergeNestedVectorMaps(std::map<K1, std::map<K2, std::vector<V>>> a,
                           std::map<K1, std::map<K2, std::vector<V>>> b)
    -> std::map<K1, std::map<K2, std::vector<V>>> {
    return unionWith<K1, std::map<K2, std::vector<V>>>(
        a, b,
        [](std::map<K1, std::vector<V>> a, std::map<K1, std::vector<V>> b) {
            return unionWith<K2, std::vector<V>>(
                a, b, [](std::vector<V> a, std::vector<V> b) {
                    a.insert(a.end(), b.begin(), b.end());
                    return a;
                });
        });
}

auto filterVars(int program, const std::vector<smt::SortedVar> &vars)
    -> std::vector<smt::SortedVar>;

auto llvmValToSortedVar(const llvm::Value *val) -> smt::SortedVar;
bool varBelongsTo(std::string varName, int program);

auto heapName(Program prog) -> std::string;
auto heapName(int progIndex) -> std::string;
auto heapResultName(Program prog) -> std::string;
auto stackName(Program progIndex) -> std::string;
auto stackName(int progIndex) -> std::string;
auto stackResultName(Program prog) -> std::string;
auto stackPointerName(Program prog) -> std::string;
auto stackPointerName(int progIndex) -> std::string;

std::vector<std::string> &split(const std::string &s, char delim,
                                std::vector<std::string> &elems);
std::vector<std::string> split(const std::string &s, char delim);

auto functionArgs(const llvm::Function &fun) -> std::vector<smt::SortedVar>;
auto getMutualResultValues(const llvm::StringRef assignedTo1,
                           const llvm::Function &function1,
                           const llvm::StringRef assignedTo2,
                           const llvm::Function &function2)
    -> std::vector<smt::SortedVar>;
auto getResultValues(Program prog, const llvm::StringRef assignedTo,
                     const llvm::Function &function)
    -> std::vector<smt::SortedVar>;

auto callsTransitively(const llvm::Function &caller,
                       const llvm::Function &callee) -> bool;
auto calledFunctions(const llvm::Function &f)
    -> std::set<const llvm::Function *>;

auto dropSuffixFromName(std::string) -> std::string;

template <typename U, typename... T> bool oneOf(U &&u, T &&... t) {
    bool match = false;
    (void)std::initializer_list<bool>{(match = match || u == t)...};
    return match;
}

template <typename U, typename... T> bool noneOf(U &&u, T &&... t) {
    bool match = true;
    (void)std::initializer_list<bool>{(match = match && u != t)...};
    return match;
}

template <typename K1, typename K2, typename V>
void nestedLookup(
    std::map<K1, std::map<K2, V>> map, const K1 &key1, const K2 &key2,
    std::function<void(typename std::map<K2, V>::iterator)> ifTrue,
    std::function<void(void)> ifFalse) {
    auto outerFound = map.find(key1);
    if (outerFound == map.end()) {
        return ifFalse();
    } else {
        auto innerFound = outerFound->second.find(key2);
        if (innerFound == outerFound->second.end()) {
            return ifFalse();
        } else {
            return ifTrue(innerFound);
        }
    }
}

template <typename K1, typename K2, typename V, typename R>
void nestedLookup(std::map<K1, std::map<K2, V>> map, const K1 &key1,
                  const K2 &key2,
                  std::function<R(typename std::map<K2, V>::iterator)> ifTrue,
                  std::function<R(void)> ifFalse) {
    auto outerFound = map.find(key1);
    if (outerFound == map.end()) {
        return ifFalse();
    } else {
        auto innerFound = outerFound->second.find(key2);
        if (innerFound == outerFound->second.end()) {
            return ifFalse();
        } else {
            return ifTrue(innerFound);
        }
    }
}

// This function exists only because initializer lists don’t work for
// unique_ptrs
template <typename V> auto vecSingleton(V x) -> llvm::SmallVector<V, 1> {
    llvm::SmallVector<V, 1> result;
    result.push_back(std::move(x));
    return result;
}

// This should eventually be removed but it’s useful for transitioning from
// shared_ptrs to unique_ptrs
template <typename T>
std::vector<std::shared_ptr<T>>
toVecOfSharedPtr(std::vector<std::unique_ptr<T>> vec) {
    std::vector<std::shared_ptr<T>> result(vec.size());
    for (size_t i = 0; i < vec.size(); ++i) {
        result[i] = std::move(vec[i]);
    }
    return result;
}
