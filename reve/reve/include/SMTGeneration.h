#pragma once

/**
  \file SMTGeneration.h
  Contains the main logic for actually generating smt from the llvm assembly.
*/
#include "Assignment.h"
#include "Helper.h"
#include "Memory.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include <regex>
#include <tuple>

using FAMRef = std::shared_ptr<llvm::FunctionAnalysisManager>;
using FreeVarsMap = std::map<int, std::vector<std::string>>;

enum class InterleaveStep { StepBoth, StepFirst, StepSecond };

struct AssignmentCallBlock {
    std::vector<DefOrCallInfo> definitions;
    smt::SMTRef condition;
    AssignmentCallBlock(std::vector<DefOrCallInfo> definitions,
                        smt::SMTRef condition)
        : definitions(definitions), condition(condition) {}
};

struct AssignmentBlock {
    std::vector<smt::Assignment> definitions;
    smt::SMTRef condition;
    AssignmentBlock(std::vector<smt::Assignment> definitions,
                    smt::SMTRef condition)
        : definitions(definitions), condition(condition) {}
};

/// Create the mutual assertions for the passed function.
/**
This creates complete assertions containing the input and output parameters of
the function. Each jump is modeled as a possibly recursive call.
 */
auto functionAssertion(
    MonoPair<llvm::Function *> funs,
    MonoPair<std::shared_ptr<llvm::FunctionAnalysisManager>> fams, bool offByN,
    std::vector<smt::SMTRef> &declarations, Memory memory)
    -> std::vector<smt::SMTRef>;
/// Create the assertion for the passed main function.
/**
The main function is special because it is never called so the predicates don’t
need to contain the output parameters. While it’s not necessary to use this
encoding it seems to perform better in some cases.
 */
auto mainAssertion(MonoPair<llvm::Function *> funs, MonoPair<FAMRef> fams,
                   bool offByN, std::vector<smt::SMTRef> &declarations,
                   bool onlyRec, Memory memory, bool dontNest)
    -> std::vector<smt::SMTRef>;
/// Get all combinations of paths that have the same start and end mark.
/**
  \return A nested map from start and end marks to a vector of paths. The paths
          are stored as a function to delay the choice of the predicate that
  needs to hold
          at the end mark.
 */
auto getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                          FreeVarsMap freeVarsMap, Memory memory)
    -> std::map<
        int,
        std::map<int, std::vector<std::function<smt::SMTRef(smt::SMTRef)>>>>;
/// Declarations for the main function.
auto mainDeclarations(PathMap pathMap, std::string funName,
                      FreeVarsMap freeVarsMap) -> std::vector<smt::SMTRef>;
/// Declarations for functions that can be called.
auto recDeclarations(PathMap pathMap, std::string funName,
                     FreeVarsMap freeVarsMap, Memory memory)
    -> std::vector<smt::SMTRef>;
/// Find all paths with the same start but different end marks
/**
This can be relaxed when \p offByN is true. In this case if one program can only
move away from the current block (e.g. the loop condition is no longer true) the
other is still allowed to loop at its block.
 */
auto getForbiddenPaths(MonoPair<PathMap> pathMaps,
                       MonoPair<BidirBlockMarkMap> marked,
                       FreeVarsMap freeVarsMap, bool offByN,
                       std::string funName, bool main, Memory memory)
    -> std::vector<smt::SMTRef>;
/// Get the assertions for a single program
auto nonmutualPaths(PathMap pathMap, std::vector<smt::SMTRef> &pathExprs,
                    FreeVarsMap freeVarsMap, Program prog, std::string funName,
                    std::vector<smt::SMTRef> &declarations, Memory memory)
    -> void;
auto getOffByNPaths(PathMap pathMap1, PathMap pathMap2, FreeVarsMap freeVarsMap,
                    std::string funName, bool main, Memory memory)
    -> std::map<
        int,
        std::map<int, std::vector<std::function<smt::SMTRef(smt::SMTRef)>>>>;
auto offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                       FreeVarsMap freeVarsMap, Program prog,
                       std::string funName, bool main, Memory memory)
    -> std::map<
        int,
        std::map<int, std::vector<std::function<smt::SMTRef(smt::SMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path path, Program prog,
                       std::vector<std::string> freeVars, bool toEnd,
                       Memory memory) -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(
    smt::SMTRef endClause,
    MonoPair<std::vector<AssignmentCallBlock>> assignments, Memory memory)
    -> smt::SMTRef;
auto nonmutualSMT(smt::SMTRef endClause,
                  std::vector<AssignmentCallBlock> assignments, Program prog,
                  Memory memory) -> smt::SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(smt::SMTRef clause, MonoPair<CallInfo> callPair,
                           Memory memory) -> smt::SMTRef;
auto nonmutualRecursiveForall(smt::SMTRef clause, CallInfo call, Program prog,
                              Memory memory) -> smt::SMTRef;
auto forallStartingAt(smt::SMTRef clause, std::vector<std::string> freeVars,
                      int blockIndex, ProgramSelection prog,
                      std::string funName, bool main, FreeVarsMap freeVarsMap,
                      Memory memory) -> smt::SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(smt::SMTRef clause, smt::SMTRef preClause,
                      std::vector<std::string> args1,
                      std::vector<std::string> args2) -> smt::SMTRef;
auto inInvariant(MonoPair<const llvm::Function *> funs, smt::SMTRef body,
                 Memory memory, const llvm::Module &mod1,
                 const llvm::Module &mod2, bool strings) -> smt::SMTRef;
auto outInvariant(smt::SMTRef body, Memory memory) -> smt::SMTRef;
auto equalInputsEqualOutputs(std::vector<std::string> funArgs,
                             std::vector<std::string> funArgs1,
                             std::vector<std::string> funArgs2,
                             std::string funName, FreeVarsMap freeVarsMap,
                             Memory memory) -> smt::SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> pathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap map1, PathMap map2, std::vector<std::string> funArgs,
              Memory memory) -> FreeVarsMap;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(const llvm::Function &fun1, const llvm::Function &fun2)
    -> MonoPair<std::vector<std::string>>;
auto swapIndex(int i) -> int;

struct SplitAssignments {
    std::vector<std::vector<AssignmentBlock>> assignments;
    std::vector<CallInfo> callInfos;
};

auto splitAssignmentsFromCalls(std::vector<AssignmentCallBlock>)
    -> SplitAssignments;

auto stringConstants(const llvm::Module &mod, std::string heap)
    -> std::vector<smt::SMTRef>;
auto matchFunCalls(std::vector<CallInfo> callInfos1,
                   std::vector<CallInfo> callInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap map1, PathMap map2) -> void;
auto mapSubset(PathMap map1, PathMap map2) -> bool;
auto getDontLoopInvariant(smt::SMTRef endClause, int startIndex,
                          PathMap pathMap, FreeVarsMap freeVarsMap,
                          Program prog, Memory memory) -> smt::SMTRef;
auto addAssignments(const smt::SMTRef end,
                    std::vector<AssignmentBlock> assignments) -> smt::SMTRef;
auto addMemory(std::vector<smt::SMTRef> &implArgs, Memory memory)
    -> std::function<void(CallInfo call, int index)>;
