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

enum class LoopInfo {
    Left,  // The left call is looping alone
    Right, // The right call is looping alone
    None   // perfect synchronization
};

template <typename T>
auto getDataForLoopInfo(LoopInfoData<T> &data, LoopInfo position) -> T & {
    switch (position) {
    case LoopInfo::Left:
        return data.left;
    case LoopInfo::Right:
        return data.right;
    case LoopInfo::None:
        return data.none;
    }
}

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
// The optional is needed to indicate that we have seen a certain combination of
// mark and exit index but not this loop synchronization
using HeapPatternCandidatesMap =
    IterativeInvariantMap<LoopInfoData<llvm::Optional<HeapPatternCandidates>>>;
using BoundsMap =
    std::map<Mark, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::map<Mark, smt::SharedSMTRef> makeIterativeInvariantDefinitions(
    MonoPair<const llvm::Function *> functions,
    const IterativeInvariantMap<PolynomialEquations> &equations,
    const HeapPatternCandidatesMap &patterns,
    const AnalysisResultsMap &analysisResults, size_t degree);
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
// This can return a nullpointer if the invariant is empty, conceptually this
// represents the invariant "true" but if the invariant consists of multiple
// parts, this needs to be handled separately.
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
