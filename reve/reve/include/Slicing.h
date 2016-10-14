#pragma once

#include "MonoPair.h"
#include "Preprocess.h"

/// Create the mutual assertions for slicing.
/**
This creates complete assertions for slicing.
 */
auto slicingAssertion(MonoPair<PreprocessedFunction> preprocessedFuns)
    -> std::vector<smt::SharedSMTRef>;
