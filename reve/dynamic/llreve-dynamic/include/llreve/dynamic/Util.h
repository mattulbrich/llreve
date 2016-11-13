#pragma once

#include "AnalysisResults.h"
#include "MonoPair.h"
#include "SMT.h"

namespace llreve {
namespace dynamic {
std::vector<smt::SortedVar>
removeHeapVariables(const std::vector<smt::SortedVar> &freeVariables);

std::vector<smt::SortedVar>
getFreeVariablesForMark(MonoPair<const llvm::Function *> functions, Mark mark,
                        const AnalysisResultsMap &analysisResults);
std::vector<smt::SortedVar>
getPrimitiveFreeVariables(MonoPair<const llvm::Function *> functions, Mark mark,
                          const AnalysisResultsMap &analysisResults);
std::vector<smt::SortedVar>
getPrimitiveFreeVariables(const llvm::Function *function, Mark mark,
                          const AnalysisResultsMap &analysisResults);

std::vector<std::vector<std::string>>
polynomialTermsOfDegree(std::vector<smt::SortedVar> variables, size_t degree);
}
}
