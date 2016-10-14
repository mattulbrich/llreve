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

#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"

struct AnalysisResults {
    BidirBlockMarkMap blockMarkMap;
    PathMap paths;
    AnalysisResults(BidirBlockMarkMap marks, PathMap pm)
        : blockMarkMap(marks), paths(pm) {}
};

using AnalysisResultsMap = std::map<const llvm::Function *, AnalysisResults>;
MonoPair<PathMap>

getPathMaps(MonoPair<llvm::Function *> functions,
            const AnalysisResultsMap &analysisResults);
MonoPair<BidirBlockMarkMap>
getBlockMarkMaps(MonoPair<llvm::Function *> functions,
                 const AnalysisResultsMap &analysisResults);
std::string getFunctionName(MonoPair<llvm::Function *> functions);
