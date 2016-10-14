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

AnalysisResultsMap
preprocessFunctions(MonoPair<std::shared_ptr<llvm::Module>> modules,
                    PreprocessOpts opts);
void preprocessFunctions(llvm::Module &module, PreprocessOpts opts,
                         AnalysisResultsMap &preprocessingResults,
                         Program prog);
auto preprocessFunction(llvm::Function &fun, std::string prefix,
                        PreprocessOpts opts) -> AnalysisResults;
