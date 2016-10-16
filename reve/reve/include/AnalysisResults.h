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

#include "FreeVariables.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"

struct AnalysisResults {
    BidirBlockMarkMap blockMarkMap;
    PathMap paths;
    std::vector<smt::SortedVar> functionArguments;
    FreeVarsMap freeVariables;
    AnalysisResults(BidirBlockMarkMap marks, PathMap pm,
                    std::vector<smt::SortedVar> funArgs, FreeVarsMap freeVars)
        : blockMarkMap(marks), paths(pm), functionArguments(funArgs),
          freeVariables(freeVars) {}
};

using AnalysisResultsMap = std::map<const llvm::Function *, AnalysisResults>;
MonoPair<PathMap>

getPathMaps(MonoPair<const llvm::Function *> functions,
            const AnalysisResultsMap &analysisResults);
MonoPair<BidirBlockMarkMap>
getBlockMarkMaps(MonoPair<const llvm::Function *> functions,
                 const AnalysisResultsMap &analysisResults);
MonoPair<std::vector<smt::SortedVar>>
getFunctionArguments(MonoPair<const llvm::Function *> functions,
                     const AnalysisResultsMap &analysisResults);
FreeVarsMap getFreeVarsMap(MonoPair<const llvm::Function *> functions,
                           const AnalysisResultsMap &analysisResults);
std::string getFunctionName(MonoPair<const llvm::Function *> functions);
