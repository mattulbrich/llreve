#pragma once

#include "llreve/dynamic/Invariant.h"
#include "llreve/dynamic/Match.h"

namespace llreve {
namespace dynamic {

void populateEquationsMap(
    IterativeInvariantMap<PolynomialEquations> &equationsMap,
    std::vector<smt::SortedVar> primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex, size_t degree);
void populateEquationsMap(
    RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>> &equationsMap,
    std::vector<smt::SortedVar> primitiveVariables,
    CoupledCallInfo<const llvm::Value *> match, size_t degree);
void populateEquationsMap(FunctionInvariantMap<Matrix<mpq_class>> &equationsMap,
                          std::vector<smt::SortedVar> primitiveVariables,
                          UncoupledCallInfo<const llvm::Value *> match,
                          size_t degree);
}
}
