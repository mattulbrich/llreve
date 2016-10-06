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

auto dropTypesFreeVars(smt::FreeVarsMap map)
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
auto functionAssertion(MonoPair<PreprocessedFunction> preprocessedFuns,
                       std::vector<smt::SharedSMTRef> &declarations,
                       std::vector<smt::SortedVar> &variableDeclarations,
                       Memory memory) -> std::vector<smt::SharedSMTRef>;

/// Create the mutual assertions for slicing.
/**
This creates complete assertions for slicing.
 */
auto slicingAssertion(MonoPair<PreprocessedFunction> preprocessedFuns)
    -> std::vector<smt::SharedSMTRef>;

/// Create the assertion for the passed main function.
/**
The main function is special because it is never called so the predicates don’t
need to contain the output parameters. While it’s not necessary to use this
encoding it seems to perform better in some cases.
 */
auto mainAssertion(MonoPair<PreprocessedFunction> preprocessedFuns,
                   std::vector<smt::SharedSMTRef> &declarations,
                   std::vector<smt::SortedVar> &variableDeclarations,
                   bool onlyRec, Memory memory)
    -> std::vector<smt::SharedSMTRef>;

/// Get all combinations of paths that have the same start and end mark.
/**
  \return A nested map from start and end marks to a vector of paths. The paths
          are stored as a function to delay the choice of the predicate that
  needs to hold
          at the end mark.
 */
auto getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                          std::vector<smt::SortedVar> &variableDeclarations,
                          smt::FreeVarsMap freeVarsMap, Memory memory)
    -> std::map<int, std::map<int, std::vector<std::function<
                                       smt::SharedSMTRef(smt::SharedSMTRef)>>>>;
/// Declarations for the main function.
auto mainDeclarations(PathMap pathMap, std::string funName,
                      smt::FreeVarsMap freeVarsMap)
    -> std::vector<smt::SharedSMTRef>;
/// Declarations for functions that can be called.
auto recDeclarations(PathMap pathMap, std::string funName,
                     smt::FreeVarsMap freeVarsMap, Memory memory,
                     const llvm::Type *returnType)
    -> std::vector<smt::SharedSMTRef>;
/// Find all paths with the same start but different end marks
/**
This is usually (when PerfectSync is false) slightly relaxed. If one program can
only
move away from the current block (e.g. the loop condition is no longer true) the
other is still allowed to loop at its block.
 */
auto getForbiddenPaths(MonoPair<PathMap> pathMaps,
                       MonoPair<BidirBlockMarkMap> marked,
                       std::vector<smt::SortedVar> &variableDeclarations,
                       smt::FreeVarsMap freeVarsMap, std::string funName,
                       bool main, Memory memory)
    -> std::vector<smt::SharedSMTRef>;
/// Get the assertions for a single program
auto nonmutualPaths(PathMap pathMap, std::vector<smt::SharedSMTRef> &pathExprs,
                    smt::FreeVarsMap freeVarsMap, Program prog,
                    std::string funName,
                    std::vector<smt::SharedSMTRef> &declarations,
                    std::vector<smt::SortedVar> &variableDeclarations,
                    Memory memory, const llvm::Type *type) -> void;
auto getOffByNPaths(PathMap pathMap1, PathMap pathMap2,
                    smt::FreeVarsMap freeVarsMap,
                    std::vector<smt::SortedVar> &variableDeclarations,
                    std::string funName, bool main, Memory memory)
    -> std::map<int, std::map<int, std::vector<std::function<
                                       smt::SharedSMTRef(smt::SharedSMTRef)>>>>;
auto offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                       smt::FreeVarsMap freeVarsMap,
                       std::vector<smt::SortedVar> &variableDeclarations,
                       Program prog, std::string funName, bool main,
                       Memory memory)
    -> std::map<int, std::map<int, std::vector<std::function<
                                       smt::SharedSMTRef(smt::SharedSMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path path, Program prog,
                       std::vector<smt::SortedVar> freeVars, bool toEnd,
                       Memory memory) -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(
    smt::SharedSMTRef endClause,
    MonoPair<std::vector<AssignmentCallBlock>> assignments,
    std::vector<smt::SortedVar> &variableDeclarations, Memory memory)
    -> smt::SharedSMTRef;
auto nonmutualSMT(smt::SharedSMTRef endClause,
                  std::vector<AssignmentCallBlock> assignments,
                  std::vector<smt::SortedVar> &variableDeclarations,
                  Program prog, Memory memory) -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(smt::SharedSMTRef clause,
                           MonoPair<CallInfo> callPair,
                           std::vector<smt::SortedVar> &variableDeclarations,
                           Memory memory) -> smt::SMTRef;
auto nonmutualRecursiveForall(smt::SharedSMTRef clause, CallInfo call,
                              std::vector<smt::SortedVar> &variableDeclarations,
                              Program prog, Memory memory) -> smt::SMTRef;
auto forallStartingAt(smt::SharedSMTRef clause,
                      std::vector<smt::SortedVar> freeVars, int blockIndex,
                      ProgramSelection prog, std::string funName, bool main,
                      smt::FreeVarsMap freeVarsMap, Memory memory)
    -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(smt::SharedSMTRef clause, smt::SharedSMTRef preClause,
                      std::vector<smt::SortedVar> args1,
                      std::vector<smt::SortedVar> args2) -> smt::SharedSMTRef;
auto equalInputsEqualOutputs(std::vector<smt::SortedVar> funArgs,
                             std::vector<smt::SortedVar> funArgs1,
                             std::vector<smt::SortedVar> funArgs2,
                             std::string funName, smt::FreeVarsMap freeVarsMap,
                             Memory memory, const llvm::Type *returnType)
    -> smt::SharedSMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the search for free variables

struct FreeVar {
    smt::SortedVar var;
    llvm::Type *type;
};

inline bool operator<(const FreeVar &lhs, const FreeVar &rhs) {
    return lhs.var < rhs.var;
}

inline bool operator>(const FreeVar &lhs, const FreeVar &rhs) {
    return rhs < lhs;
}

inline bool operator<=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs > rhs);
}

inline bool operator>=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs < rhs);
}

inline bool operator==(const FreeVar &lhs, const FreeVar &rhs) {
    return lhs.var == rhs.var;
}

inline bool operator!=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs == rhs);
}

auto llvmValToFreeVar(const llvm::Value *val) -> FreeVar;
auto freeVarsForBlock(std::map<int, Paths> pathMap)
    -> std::pair<std::set<FreeVar>, std::map<int, std::set<FreeVar>>>;
auto freeVars(PathMap map1, PathMap map2, std::vector<smt::SortedVar> funArgs,
              Memory memory) -> smt::FreeVarsMap;
/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(const llvm::Function &fun1, const llvm::Function &fun2)
    -> MonoPair<std::vector<smt::SortedVar>>;
auto functionArgsFreeVars(const llvm::Function &fun1,
                          const llvm::Function &fun2)
    -> std::vector<smt::SortedVar>;
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
auto getDontLoopInvariant(smt::SMTRef endClause, int startIndex,
                          PathMap pathMap, smt::FreeVarsMap freeVarsMap,
                          std::vector<smt::SortedVar> &variableDeclarations,
                          Program prog, Memory memory) -> smt::SMTRef;
auto addAssignments(const smt::SharedSMTRef end,
                    std::vector<AssignmentBlock> assignments)
    -> smt::SharedSMTRef;
auto addMemory(std::vector<smt::SharedSMTRef> &implArgs, Memory memory)
    -> std::function<void(CallInfo call, int index)>;
/// Declare required variables globally
/**
This is used when MuZFlag is enabled
 */
auto declareVariables(smt::FreeVarsMap freeVarsMap,
                      std::vector<smt::SortedVar> &variableDeclarations)
    -> void;
