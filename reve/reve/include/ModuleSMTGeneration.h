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

#include "Memory.h"
#include "MonoPair.h"
#include "Opts.h"
#include "Preprocess.h"
#include "SMT.h"

#include "llvm/IR/Module.h"

auto generateSMT(MonoPair<std::shared_ptr<llvm::Module>> modules,
                 std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
                 FileOptions fileOpts) -> std::vector<smt::SharedSMTRef>;
auto select_Declaration() -> smt::SMTRef;
auto store_Declaration() -> smt::SMTRef;
auto externDeclarations(llvm::Module &mod1, llvm::Module &mod2,
                        std::vector<smt::SharedSMTRef> &declarations,
                        std::multimap<std::string, std::string> funCondMap)
    -> void;
auto funArgs(llvm::Function &fun, std::string prefix, uint32_t varArgs)
    -> std::vector<smt::SortedVar>;
auto getVarArgs(const llvm::Function &fun) -> std::set<uint32_t>;
auto externFunDecl(llvm::Function &fun, Program program)
    -> std::vector<smt::SharedSMTRef>;
auto equivalentExternDecls(llvm::Function &fun1, llvm::Function &fun2,
                           std::multimap<std::string, std::string> funCondMap)
    -> std::vector<smt::SharedSMTRef>;
auto notEquivalentExternDecls(llvm::Function &fun1, llvm::Function &fun2)
    -> std::vector<smt::SharedSMTRef>;
auto doesNotRecurse(llvm::Function &fun) -> bool;
auto globalDeclarations(llvm::Module &mod1, llvm::Module &mod2)
    -> std::vector<smt::SharedSMTRef>;
auto globalDeclarationsForMod(int globalPointer, llvm::Module &mod,
                              llvm::Module &otherMod, int program)
    -> std::vector<smt::SharedSMTRef>;
auto doesAccessMemory(const llvm::Module &mod) -> bool;
auto stringConstants(const llvm::Module &mod, std::string heap)
    -> std::vector<smt::SharedSMTRef>;
auto inInvariant(MonoPair<const llvm::Function *> funs, smt::SharedSMTRef body,
                 const llvm::Module &mod1, const llvm::Module &mod2,
                 bool strings, bool inInvariant)
    -> std::shared_ptr<smt::FunDef>;
auto outInvariant(MonoPair<std::vector<smt::SortedVar>> funArgs,
                  smt::SharedSMTRef body, const llvm::Type *type)
    -> smt::SharedSMTRef;

smt::SharedSMTRef initPredicate(std::shared_ptr<const smt::FunDef> inInv);
smt::SharedSMTRef
initPredicateComment(std::shared_ptr<const smt::FunDef> inInv);
smt::SharedSMTRef initImplication(std::shared_ptr<const smt::FunDef> funDecl);
