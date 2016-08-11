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

#include "MonoPair.h"
#include "Opts.h"
#include "AnalysisResults.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/ErrorOr.h"

struct PreprocessedFunction {
    llvm::Function *fun;
    AnalysisResults results;
    PreprocessedFunction(llvm::Function *fun,
                         AnalysisResults results)
        : fun(fun), results(results) {}
};

std::vector<MonoPair<PreprocessedFunction>>
preprocessFunctions(MonoPair<std::shared_ptr<llvm::Module>> modules,
                    PreprocessOpts opts);
auto zipFunctions(llvm::Module &mod1, llvm::Module &mod2)
    -> llvm::ErrorOr<std::vector<MonoPair<llvm::Function *>>>;
auto preprocessFunction(llvm::Function &fun, std::string prefix,
                        PreprocessOpts opts)
    -> AnalysisResults;
