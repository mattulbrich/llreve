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

#include "Opts.h"
#include "SMT.h"

#include <string>
#ifndef _WIN32
#include <unistd.h>
#endif

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#define logError(Message) logError_(Message, __FILE__, __LINE__)
#define logWarning(Message) logWarning_(Message, __FILE__, __LINE__)
#define logErrorData(Message, El) logErrorData_(Message, El, __FILE__, __LINE__)
#define logWarningData(Message, El)                                            \
    logWarningData_(Message, El, __FILE__, __LINE__)

template <typename Str>
auto logError_(Str message, const char *file, int line) -> void {
    bool colors = false;
#ifndef _WIN32
    colors = isatty(fileno(stderr));
#endif
    if (colors) {
        llvm::errs() << "\x1b[31;1mERROR\x1b[0m\x1b[1m (" << file << ":" << line
                     << "): " << message << "\x1b[0m";
    } else {
        llvm::errs() << "ERROR: " << message;
    }
}

template <typename Str>
auto logWarning_(Str message, const char *file, int line) -> void {
    bool colors = false;
#ifndef _WIN32
    colors = isatty(fileno(stderr));
#endif
    if (colors) {
        llvm::errs() << "\x1b[33;1mWARNING\x1b[0m\x1b[1m (" << file << ":"
                     << line << "): " << message << "\x1b[0m";
    } else {
        llvm::errs() << "WARNING: " << message;
    }
}

template <typename Str, typename A>
auto logErrorData_(Str message, A &el, const char *file, int line) -> void {
    logError_(message, file, line);
    el.print(llvm::errs());
    llvm::errs() << "\n";
}

template <typename Str, typename A>
auto logWarningData_(Str message, A &el, const char *file, int line) -> void {
    logWarning_(message, file, line);
    el.print(llvm::errs());
    llvm::errs() << "\n";
}

auto instrLocation(const llvm::Value *val)
    -> std::unique_ptr<const smt::SMTExpr>;
auto instrNameOrVal(const llvm::Value *val, const llvm::Type *ty)
    -> std::unique_ptr<const smt::SMTExpr>;
auto typeSize(llvm::Type *ty, const llvm::DataLayout &layout) -> int;
template <typename T> std::unique_ptr<const smt::SMTExpr> resolveGEP(T &gep) {
    std::vector<smt::SharedSMTRef> args;
    args.push_back(instrNameOrVal(gep.getPointerOperand(),
                                  gep.getPointerOperand()->getType()));
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
        auto smtIx = instrNameOrVal(*ix, (*ix)->getType());
        if (SMTGenerationOpts::getInstance().BitVect) {
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
            if (SMTGenerationOpts::getInstance().BitVect) {
                args.push_back(smt::makeOp(
                    "bvmul",
                    smt::stringExpr("(_ bv" + std::to_string(size) + " 64)"),
                    std::move(smtIx)));
            } else {
                args.push_back(
                    smt::makeOp("*", smt::stringExpr(std::to_string(size)),
                                std::move(smtIx)));
            }
        }
    }
    if (SMTGenerationOpts::getInstance().BitVect) {
        return std::make_unique<smt::Op>("bvadd", args);
    } else {
        return std::make_unique<smt::Op>("+", args);
    }
}

template <typename Key, typename Val>
auto unionWith(std::map<Key, Val> mapA, std::map<Key, Val> mapB,
               std::function<Val(Val, Val)> combine) -> std::map<Key, Val> {
    for (auto pair : mapB) {
        if (mapA.find(pair.first) == mapA.end()) {
            mapA.insert(pair);
        } else {
            mapA.at(pair.first) = combine(mapA.at(pair.first), pair.second);
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
    return unionWith<K, std::vector<V>>(
        a, b, [](std::vector<V> a, std::vector<V> b) {
            a.insert(a.end(), b.begin(), b.end());
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

auto filterVars(int program, std::vector<smt::SortedVar> vars)
    -> std::vector<smt::SortedVar>;

auto llvmValToSortedVar(const llvm::Value *val) -> smt::SortedVar;
bool varBelongsTo(std::string varName, int program);

auto heapName(int progIndex) -> std::string;
auto stackName(int progIndex) -> std::string;
auto stackPointerName(int progIndex) -> std::string;

std::vector<std::string> &split(const std::string &s, char delim,
                                std::vector<std::string> &elems);
std::vector<std::string> split(const std::string &s, char delim);

auto functionArgs(const llvm::Function &fun) -> std::vector<smt::SortedVar>;

auto callsTransitively(const llvm::Function &caller,
                       const llvm::Function &callee) -> bool;
auto calledFunctions(const llvm::Function &f)
    -> std::set<const llvm::Function *>;

auto dropSuffixFromName(std::string) -> std::string;
