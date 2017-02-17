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

auto generateSMT(MonoPair<const llvm::Module &> modules,
                 const AnalysisResultsMap &analysisResults,
                 llreve::opts::FileOptions fileOpts)
    -> std::vector<smt::SharedSMTRef>;
auto generateSMTForMainFunctions(MonoPair<const llvm::Module &> modules,
                                 const AnalysisResultsMap &analysisResults,
                                 llreve::opts::FileOptions fileOpts,
                                 std::vector<smt::SharedSMTRef> &assertions,
                                 std::vector<smt::SharedSMTRef> &declarations)
    -> void;
auto generateFunctionalAbstractions(
    const llvm::Module &module, const llvm::Function *mainFunction,
    const AnalysisResultsMap &analysisResults, Program prog,
    std::vector<smt::SharedSMTRef> &assertions,
    std::vector<smt::SharedSMTRef> &declarations) -> void;
auto select_Declaration() -> smt::SMTRef;
auto store_Declaration() -> smt::SMTRef;
auto globalDeclarations(const llvm::Module &mod1, const llvm::Module &mod2)
    -> std::vector<smt::SharedSMTRef>;
auto globalDeclarationsForMod(int globalPointer, const llvm::Module &mod,
                              const llvm::Module &otherMod, int program)
    -> std::vector<smt::SharedSMTRef>;
auto stringConstants(const llvm::Module &mod, std::string heap)
    -> std::vector<smt::SharedSMTRef>;
auto inInvariant(MonoPair<const llvm::Function *> funs,
                 const AnalysisResultsMap &analysisResults,
                 smt::SharedSMTRef body, const llvm::Module &mod1,
                 const llvm::Module &mod2, bool strings, bool inInvariant)
    -> std::unique_ptr<smt::FunDef>;
auto outInvariant(MonoPair<std::vector<smt::SortedVar>> funArgs,
                  smt::SharedSMTRef body, const llvm::Type *type)
    -> std::unique_ptr<smt::FunDef>;

smt::SharedSMTRef initPredicate(std::shared_ptr<const smt::FunDef> inInv);
smt::SharedSMTRef
initPredicateComment(std::shared_ptr<const smt::FunDef> inInv);
smt::SharedSMTRef initImplication(std::shared_ptr<const smt::FunDef> funDecl);
