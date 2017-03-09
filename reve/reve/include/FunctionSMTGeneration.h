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

#include "Assignment.h"
#include "FreeVariables.h"
#include "Helper.h"
#include "Memory.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Preprocess.h"
#include "Program.h"
#include "SMT.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include <regex>
#include <tuple>

auto dropTypesFreeVars(const FreeVarsMap &map)
    -> std::map<int, std::vector<std::string>>;

enum class InterleaveStep { StepBoth, StepFirst, StepSecond };

struct AssignmentCallBlock {
    std::vector<DefOrCallInfo> definitions;
    smt::SharedSMTRef condition;
    AssignmentCallBlock(std::vector<DefOrCallInfo> definitions,
                        smt::SharedSMTRef condition)
        : definitions(std::move(definitions)), condition(std::move(condition)) {
    }
};

struct AssignmentBlock {
    std::vector<smt::Assignment> definitions;
    smt::SharedSMTRef condition;
    AssignmentBlock(std::vector<smt::Assignment> definitions,
                    smt::SharedSMTRef condition)
        : definitions(std::move(definitions)), condition(std::move(condition)) {
    }
};

/// Create the mutual assertions for the passed function.
/**
This creates complete assertions containing the input and output parameters of
the function. Each jump is modeled as a possibly recursive call.
 */
auto relationalFunctionAssertions(
    MonoPair<const llvm::Function *> preprocessedFuns,
    const AnalysisResultsMap &analysisResults)
    -> std::vector<smt::SharedSMTRef>;
auto functionalFunctionAssertions(
    MonoPair<const llvm::Function *> preprocessedFun,
    const AnalysisResultsMap &analysisResults, Program prog)
    -> std::vector<smt::SharedSMTRef>;

/// Create the assertion for the passed main function.
/**
The main function is special because it is never called so the predicates don’t
need to contain the output parameters. While it’s not necessary to use this
encoding it seems to perform better in some cases.
 */
auto relationalIterativeAssertions(
    MonoPair<const llvm::Function *> preprocessedFuns,
    const AnalysisResultsMap &analysisResults,
    std::vector<smt::SharedSMTRef> &declarations, bool onlyRec)
    -> std::vector<smt::SharedSMTRef>;

/// Get all combinations of paths that have the same start and end mark.
/**
  \return A nested map from start and end marks to a vector of paths. The paths
          are stored as a function to delay the choice of the predicate that
  needs to hold
          at the end mark.
 */
using ReturnInvariantGenerator = std::function<smt::SMTRef(Mark, Mark)>;
struct MarkPair {
    Mark startMark;
    Mark endMark;
};

inline bool operator==(const MarkPair &lhs, const MarkPair &rhs) {
    return lhs.startMark == rhs.startMark && lhs.endMark == rhs.endMark;
}

inline bool operator<(const MarkPair &lhs, const MarkPair &rhs) {
    if (lhs.startMark == rhs.startMark) {
        return lhs.endMark < rhs.endMark;
    }
    return lhs.startMark < rhs.startMark;
}

auto getSynchronizedPaths(const PathMap &pathMap1, const PathMap &pathMap2,
                          const FreeVarsMap &freeVarsMap1,
                          const FreeVarsMap &freeVarsMap2,
                          ReturnInvariantGenerator generateReturnInvariant)
    -> std::map<MarkPair, std::vector<std::unique_ptr<smt::SMTExpr>>>;

/// Find all paths with the same start but different end marks
/**
This is usually (when PerfectSync is false) slightly relaxed. If one program can
only
move away from the current block (e.g. the loop condition is no longer true) the
other is still allowed to loop at its block.
 */
auto getForbiddenPaths(const MonoPair<PathMap> &pathMaps,
                       const MonoPair<BidirBlockMarkMap> &marked,
                       const FreeVarsMap &freeVarsMap1,
                       const FreeVarsMap &freeVarsMap2, std::string funName,
                       bool main)
    -> std::map<Mark, std::vector<std::unique_ptr<smt::SMTExpr>>>;
/// Get the assertions for a single program
auto nonmutualPaths(const PathMap &pathMap, const FreeVarsMap &freeVarsMap,
                    Program prog, std::string funName, const llvm::Type *type,
                    std::vector<smt::SharedSMTRef> functionNumeralConstraints)
    -> std::vector<smt::SharedSMTRef>;
auto getStutterPaths(const PathMap &pathMap1, const PathMap &pathMap2,
                     const FreeVarsMap &freeVarsMap, std::string funName,
                     bool main)
    -> std::map<MarkPair, std::vector<std::unique_ptr<smt::SMTExpr>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(const Path &path, Program prog,
                       const std::vector<smt::SortedVar> &freeVars, bool toEnd)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(std::unique_ptr<smt::SMTExpr> endClause,
                           llvm::ArrayRef<AssignmentCallBlock> assignment1,
                           llvm::ArrayRef<AssignmentCallBlock> assignment2)
    -> std::unique_ptr<smt::SMTExpr>;
auto nonmutualSMT(std::unique_ptr<smt::SMTExpr> endClause,
                  llvm::ArrayRef<AssignmentCallBlock> assignments, Program prog)
    -> std::unique_ptr<smt::SMTExpr>;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualFunctionCall(std::unique_ptr<smt::SMTExpr> clause,
                        MonoPair<CallInfo> callPair) -> smt::SMTRef;
auto nonMutualFunctionCall(std::unique_ptr<smt::SMTExpr> clause, CallInfo call,
                           Program prog) -> smt::SMTRef;
auto forallStartingAt(std::unique_ptr<smt::SMTExpr> clause,
                      std::vector<smt::SortedVar> freeVars, Mark blockIndex,
                      ProgramSelection prog, std::string funName, bool main)
    -> std::unique_ptr<smt::SMTExpr>;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(smt::SharedSMTRef clause, smt::SharedSMTRef preClause,
                      std::vector<smt::SortedVar> args1,
                      std::vector<smt::SortedVar> args2) -> smt::SharedSMTRef;
auto equalInputsEqualOutputs(const std::vector<smt::SortedVar> &funArgs1,
                             const std::vector<smt::SortedVar> &funArgs2,
                             const llvm::Function &function1,
                             const llvm::Function &function2,
                             std::string funName,
                             const FreeVarsMap &freeVarsMap)
    -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto swapIndex(int i) -> int;

struct SplitAssignments {
    std::vector<std::vector<AssignmentBlock>> assignments;
    std::vector<CallInfo> callInfos;
};

auto splitAssignmentsFromCalls(
    llvm::ArrayRef<AssignmentCallBlock> assignmentCallBlocks)
    -> SplitAssignments;

auto checkPathMaps(const PathMap &map1, const PathMap &map2) -> void;
auto mapSubset(const PathMap &map1, const PathMap &map2) -> bool;
auto getDontLoopInvariant(smt::SMTRef endClause, Mark startIndex,
                          const PathMap &pathMap,
                          const FreeVarsMap &freeVarsMap, Program prog)
    -> smt::SMTRef;
auto addAssignments(std::unique_ptr<smt::SMTExpr> end,
                    llvm::ArrayRef<AssignmentBlock> assignments)
    -> std::unique_ptr<smt::SMTExpr>;
auto addMemory(std::vector<smt::SharedSMTRef> &implArgs)
    -> std::function<void(CallInfo call, int index)>;

// This combines `relationalFunctionDeclarations` and
// `relationalFunctionAssertions`.
auto generateRelationalFunctionSMT(
    MonoPair<const llvm::Function *> preprocessedFunction,
    const AnalysisResultsMap &analysisResults,
    std::vector<smt::SharedSMTRef> &assertions,
    std::vector<smt::SharedSMTRef> &declarations) -> void;
// This combines `functionalFunctionDeclarations` and
// `functionalFunctionAssertions`.
auto generateFunctionalFunctionSMT(const llvm::Function *preprocessedFunction,
                                   const AnalysisResultsMap &analysisResults,
                                   Program prog,
                                   std::vector<smt::SharedSMTRef> &assertions,
                                   std::vector<smt::SharedSMTRef> &declarations)
    -> void;
// This combines `relationalIterativeDeclarations` and
// `relationalIterativeAssertions`.
auto generateRelationalIterativeSMT(
    MonoPair<const llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults,
    std::vector<smt::SharedSMTRef> &assertions,
    std::vector<smt::SharedSMTRef> &declarations) -> void;

auto getFunctionNumeralConstraints(const llvm::Function *f, Program prog)
    -> std::vector<smt::SharedSMTRef>;
auto getFunctionNumeralConstraints(MonoPair<const llvm::Function *> functions)
    -> std::vector<smt::SharedSMTRef>;
auto clauseMapToClauseVector(
    const std::map<MarkPair, std::vector<smt::SharedSMTRef>> &clauseMap,
    bool main, ProgramSelection programSelection,
    std::vector<smt::SharedSMTRef> functionNumeralConstraints)
    -> std::vector<smt::SharedSMTRef>;

template <typename T>
std::vector<InterleaveStep> matchFunCalls(
    const std::vector<T> &callInfos1, const std::vector<T> &callInfos2,
    std::function<bool(typename std::add_lvalue_reference<const T>::type,

                       typename std::add_lvalue_reference<const T>::type)>
        areCallsCoupled) {
    // This is just a basic edit distance algorithm
    std::vector<std::vector<size_t>> table(
        callInfos1.size() + 1, std::vector<size_t>(callInfos2.size() + 1, 0));
    for (uint32_t i = 0; i <= callInfos1.size(); ++i) {
        table[i][0] = i;
    }
    for (uint32_t j = 0; j <= callInfos2.size(); ++j) {
        table[0][j] = j;
    }
    for (uint32_t i = 1; i <= callInfos1.size(); ++i) {
        for (uint32_t j = 1; j <= callInfos2.size(); ++j) {
            if (areCallsCoupled(callInfos1[i - 1], callInfos2[j - 1])) {
                table[i][j] = table[i - 1][j - 1];
            } else {
                table[i][j] =
                    std::min(table[i - 1][j] + 1, table[i][j - 1] + 1);
            }
        }
    }
    std::vector<InterleaveStep> interleaveSteps;
    uint64_t i = callInfos1.size(), j = callInfos2.size();
    while (i > 0 && j > 0) {
        if (areCallsCoupled(callInfos1[i - 1], callInfos2[j - 1])) {
            interleaveSteps.push_back(InterleaveStep::StepBoth);
            --i;
            --j;
        } else {
            if (table[i - 1][j] <= table[i][j - 1]) {
                interleaveSteps.push_back(InterleaveStep::StepFirst);
                --i;
            } else {
                interleaveSteps.push_back(InterleaveStep::StepSecond);
                --j;
            }
        }
    }
    while (i > 0) {
        interleaveSteps.push_back(InterleaveStep::StepFirst);
        --i;
    }
    while (j > 0) {
        interleaveSteps.push_back(InterleaveStep::StepSecond);
        --j;
    }
    std::reverse(interleaveSteps.begin(), interleaveSteps.end());
    return interleaveSteps;
}
