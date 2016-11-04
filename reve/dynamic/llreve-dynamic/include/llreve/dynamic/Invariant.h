#pragma once

#include "FreeVariables.h"

#include "llreve/dynamic/HeapPattern.h"

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
    std::map<MonoPair<const llvm::Function *>, std::map<Mark, V>>;
using PolynomialEquations = LoopInfoData<std::vector<std::vector<mpq_class>>>;
using PolynomialSolutions =
    IterativeInvariantMap<LoopInfoData<std::vector<std::vector<mpz_class>>>>;
using HeapPatternCandidates =
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>;
using HeapPatternCandidatesMap = std::map<
    Mark,
    std::map<ExitIndex, LoopInfoData<llvm::Optional<HeapPatternCandidates>>>>;
using BoundsMap =
    std::map<Mark, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::map<Mark, smt::SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const HeapPatternCandidatesMap &patterns,
                         const FreeVarsMap &freeVarsMap, size_t degree);
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
