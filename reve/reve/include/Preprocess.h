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

#include "AnalysisResults.h"
#include "MonoPair.h"
#include "Opts.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/ErrorOr.h"

struct PassAnalysisResults {
    BidirBlockMarkMap blockMarkMap;
    PathMap paths;
};

AnalysisResultsMap
preprocessFunctions(MonoPair<std::shared_ptr<llvm::Module>> modules,
                    PreprocessOpts opts);
void runFunctionPasses(
    llvm::Module &module, PreprocessOpts opts,
    std::map<const llvm::Function *, PassAnalysisResults> &passResults,
    Program prog);
auto runFunctionPasses(llvm::Function &fun, Program prog, PreprocessOpts opts)
    -> PassAnalysisResults;
auto runAnalyses(
    const llvm::Module &module, Program prog,
    std::map<const llvm::Function *, PassAnalysisResults> &passResults,
    AnalysisResultsMap &analysisResults) -> void;
auto runAnalyses(
    const llvm::Function &fun, Program prog,
    std::map<const llvm::Function *, PassAnalysisResults> &passResults)
    -> AnalysisResults;

auto doesAccessHeap(const llvm::Module &mod) -> bool;
auto doesAccessStack(const llvm::Module &mod) -> bool;
