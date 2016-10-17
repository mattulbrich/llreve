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

using FAMRef = std::shared_ptr<llvm::FunctionAnalysisManager>;

auto dropTypesFreeVars(FreeVarsMap map)
    -> std::map<int, std::vector<std::string>>;

enum class InterleaveStep { StepBoth, StepFirst, StepSecond };

struct AssignmentCallBlock {
    std::vector<DefOrCallInfo> definitions;
    smt::SharedSMTRef condition;
    AssignmentCallBlock(std::vector<DefOrCallInfo> definitions,
                        smt::SharedSMTRef condition)
        : definitions(definitions), condition(condition) {}
};

struct AssignmentBlock {
    std::vector<smt::Assignment> definitions;
    smt::SharedSMTRef condition;
    AssignmentBlock(std::vector<smt::Assignment> definitions,
                    smt::SharedSMTRef condition)
        : definitions(definitions), condition(condition) {}
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

auto getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                          FreeVarsMap freeVarsMap,
                          ReturnInvariantGenerator generateReturnInvariant)
    -> std::map<MarkPair, std::vector<smt::SharedSMTRef>>;

/// Find all paths with the same start but different end marks
/**
This is usually (when PerfectSync is false) slightly relaxed. If one program can
only
move away from the current block (e.g. the loop condition is no longer true) the
other is still allowed to loop at its block.
 */
auto getForbiddenPaths(MonoPair<PathMap> pathMaps,
                       MonoPair<BidirBlockMarkMap> marked,
                       FreeVarsMap freeVarsMap, std::string funName, bool main)
    -> std::vector<smt::SharedSMTRef>;
/// Get the assertions for a single program
auto nonmutualPaths(PathMap pathMap, FreeVarsMap freeVarsMap, Program prog,
                    std::string funName, const llvm::Type *type)
    -> std::vector<smt::SharedSMTRef>;
auto getOffByNPaths(PathMap pathMap1, PathMap pathMap2, FreeVarsMap freeVarsMap,
                    std::string funName, bool main)
    -> std::map<MarkPair, std::vector<smt::SharedSMTRef>>;
auto offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                       FreeVarsMap freeVarsMap, Program prog,
                       std::string funName, bool main)
    -> std::map<MarkPair, std::vector<smt::SharedSMTRef>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path path, Program prog,
                       std::vector<smt::SortedVar> freeVars, bool toEnd)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(
    smt::SharedSMTRef endClause,
    MonoPair<std::vector<AssignmentCallBlock>> assignments)
    -> smt::SharedSMTRef;
auto nonmutualSMT(smt::SharedSMTRef endClause,
                  std::vector<AssignmentCallBlock> assignments, Program prog)
    -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualFunctionCall(smt::SharedSMTRef clause, MonoPair<CallInfo> callPair)
    -> smt::SMTRef;
auto nonMutualFunctionCall(smt::SharedSMTRef clause, CallInfo call,
                           Program prog) -> smt::SMTRef;
auto forallStartingAt(smt::SharedSMTRef clause,
                      std::vector<smt::SortedVar> freeVars, Mark blockIndex,
                      ProgramSelection prog, std::string funName, bool main,
                      FreeVarsMap freeVarsMap) -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(smt::SharedSMTRef clause, smt::SharedSMTRef preClause,
                      std::vector<smt::SortedVar> args1,
                      std::vector<smt::SortedVar> args2) -> smt::SharedSMTRef;
auto equalInputsEqualOutputs(std::vector<smt::SortedVar> funArgs,
                             std::vector<smt::SortedVar> funArgs1,
                             std::vector<smt::SortedVar> funArgs2,
                             std::string funName, FreeVarsMap freeVarsMap,
                             const llvm::Type *returnType) -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto swapIndex(int i) -> int;

struct SplitAssignments {
    std::vector<std::vector<AssignmentBlock>> assignments;
    std::vector<CallInfo> callInfos;
};

auto splitAssignmentsFromCalls(std::vector<AssignmentCallBlock>)
    -> SplitAssignments;

auto matchFunCalls(std::vector<CallInfo> callInfos1,
                   std::vector<CallInfo> callInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap map1, PathMap map2) -> void;
auto mapSubset(PathMap map1, PathMap map2) -> bool;
auto getDontLoopInvariant(smt::SMTRef endClause, Mark startIndex,
                          PathMap pathMap, FreeVarsMap freeVarsMap,
                          Program prog) -> smt::SMTRef;
auto addAssignments(const smt::SharedSMTRef end,
                    std::vector<AssignmentBlock> assignments)
    -> smt::SharedSMTRef;
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
