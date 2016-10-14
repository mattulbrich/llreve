#pragma once

#include "MonoPair.h"
#include "Preprocess.h"

/// Create the mutual assertions for slicing.
/**
This creates complete assertions for slicing.
 */
auto slicingAssertion(MonoPair<llvm::Function *> preprocessedFuns,
                      const AnalysisResultsMap &analysisResults)
    -> std::vector<smt::SharedSMTRef>;
