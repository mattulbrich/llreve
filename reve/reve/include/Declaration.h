#pragma once

#include "AnalysisResults.h"
#include "Preprocess.h"

auto relationalFunctionDeclarations(
    MonoPair<llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults)
    -> std::vector<smt::SharedSMTRef>;
auto functionalFunctionDeclarations(llvm::Function *preprocessedFunction,
                                    const AnalysisResultsMap &analysisResults,
                                    Program program)
    -> std::vector<smt::SharedSMTRef>;
auto relationalIterativeDeclarations(
    MonoPair<llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults)
    -> std::vector<smt::SharedSMTRef>;
