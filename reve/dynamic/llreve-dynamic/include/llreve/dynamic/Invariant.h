#pragma once

#include "AnalysisResults.h"
#include "FreeVariables.h"

#include "llreve/dynamic/HeapPattern.h"
#include "llreve/dynamic/Linear.h"

#include <gmpxx.h>

namespace llreve {
namespace dynamic {

extern bool ImplicationsFlag;
using ExitIndex = mpz_class;

template <typename T> struct LoopInfoData {
    T left;
    T right;
    T none;
    LoopInfoData() = default;
    LoopInfoData(T left, T right, T none)
        : left(left), right(right), none(none) {}
};

template <typename T> struct Bound {
    T lower;
    T upper;
    Bound(T lower, T upper) : lower(lower), upper(upper) {}
};

template <typename V>
using IterativeInvariantMap = std::map<Mark, std::map<ExitIndex, V>>;
template <typename V>
using RelationalFunctionInvariantMap =
    std::map<MonoPair<const llvm::Function *>, std::map<Mark, V>>;
template <typename V>
using FunctionInvariantMap =
    std::map<const llvm::Function *, std::map<Mark, FunctionInvariant<V>>>;
using PolynomialEquations = LoopInfoData<Matrix<mpq_class>>;
using PolynomialSolutions =
    IterativeInvariantMap<LoopInfoData<Matrix<mpz_class>>>;
using HeapPatternCandidates =
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>;
using HeapPatternCandidatesMap = std::map<
    Mark,
    std::map<ExitIndex, LoopInfoData<llvm::Optional<HeapPatternCandidates>>>>;
using BoundsMap =
    std::map<Mark, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::map<Mark, smt::SharedSMTRef> makeIterativeInvariantDefinitions(
    const IterativeInvariantMap<PolynomialEquations> &equations,
    const HeapPatternCandidatesMap &patterns, const FreeVarsMap &freeVarsMap,
    size_t degree);
RelationalFunctionInvariantMap<FunctionInvariant<smt::SharedSMTRef>>
makeRelationalFunctionInvariantDefinitions(
    const RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>> &equations,
    const AnalysisResultsMap &analysisResults, size_t degree);
FunctionInvariantMap<smt::SharedSMTRef> makeFunctionInvariantDefinitions(
    const llvm::Module &module,
    const FunctionInvariantMap<Matrix<mpq_class>> &equations,
    const AnalysisResultsMap &analysisResults, Program prog, size_t degree);
FunctionInvariantMap<smt::SharedSMTRef> makeFunctionInvariantDefinitions(
    MonoPair<const llvm::Module &> modules,
    const FunctionInvariantMap<Matrix<mpq_class>> &equations,
    const AnalysisResultsMap &analysisResults, size_t degree);
Matrix<mpz_class> findSolutions(Matrix<mpq_class> equations);
PolynomialSolutions
findSolutions(const IterativeInvariantMap<PolynomialEquations> &equationsMap);
smt::SharedSMTRef
makeInvariantDefinition(const std::vector<std::vector<mpz_class>> &solution,
                        const HeapPatternCandidates &candidates,
                        const std::vector<smt::SortedVar> &freeVars,
                        size_t degree);
smt::SharedSMTRef makeEquation(const std::vector<mpz_class> &eq,
                               const std::vector<smt::SortedVar> &freeVars,
                               size_t degree);
smt::SharedSMTRef makeBoundsDefinitions(
    const std::map<std::string, Bound<llvm::Optional<VarIntVal>>> &bounds);
}
}
