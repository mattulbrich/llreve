#pragma once

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

using std::make_shared;
using llvm::Instruction;

using FAMRef = shared_ptr<llvm::FunctionAnalysisManager>;

enum class InterleaveStep { StepBoth, StepFirst, StepSecond };

struct AssignmentCallBlock {
    std::vector<DefOrCallInfo> definitions;
    SMTRef condition;
    AssignmentCallBlock(std::vector<DefOrCallInfo> definitions,
                        SMTRef condition)
        : definitions(definitions), condition(condition) {}
};

struct AssignmentBlock {
    std::vector<Assignment> definitions;
    SMTRef condition;
    AssignmentBlock(std::vector<Assignment> definitions, SMTRef condition)
        : definitions(definitions), condition(condition) {}
};

auto convertToSMT(MonoPair<llvm::Function *> funs,
                  MonoPair<std::shared_ptr<llvm::FunctionAnalysisManager>> fams,
                  bool offByN, std::vector<SMTRef> &declarations, Memory memory,
                  bool everythingSigned) -> std::vector<SMTRef>;
auto mainAssertion(MonoPair<llvm::Function *> funs, MonoPair<FAMRef> fams,
                   bool offByN, std::vector<SMTRef> &declarations, bool onlyRec,
                   Memory memory, bool everythingSigned, bool dontNest)
    -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

auto getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                          std::map<int, std::vector<string>> freeVarsMap,
                          std::string funName,
                          std::vector<SMTRef> &declarations, Memory memory,
                          bool everythingSigned) -> std::vector<SMTRef>;
auto mainSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                           std::map<int, std::vector<string>> freeVarsMap,
                           std::string funName,
                           std::vector<SMTRef> &declarations, Memory memory,
                           bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto getForbiddenPaths(MonoPair<PathMap> pathMaps,
                       MonoPair<BidirBlockMarkMap> marked,
                       std::map<int, std::vector<string>> freeVarsMap,
                       bool offByN, std::string funName, bool main,
                       Memory memory, bool everythingSigned)
    -> std::vector<SMTRef>;
auto nonmutualPaths(PathMap pathMap, std::vector<SMTRef> &pathExprs,
                    std::map<int, std::vector<string>> freeVarsMap,
                    Program prog, std::string funName,
                    std::vector<SMTRef> &declarations, Memory memory,
                    bool everythingSigned) -> void;
auto getOffByNPaths(PathMap pathMap1, PathMap pathMap2,
                    std::map<int, std::vector<string>> freeVarsMap,
                    std::string funName, bool main, Memory memory,
                    bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                       std::map<int, std::vector<string>> freeVarsMap,
                       Program prog, std::string funName, bool main,
                       Memory memory, bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path path, Program prog,
                       std::vector<std::string> freeVars, bool toEnd,
                       Memory memory, bool everythingSigned)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(
    SMTRef endClause, MonoPair<std::vector<AssignmentCallBlock>> assignments,
    Memory memory) -> SMTRef;
auto nonmutualSMT(SMTRef endClause,
                  std::vector<AssignmentCallBlock> assignments, Program prog,
                  Memory memory) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef clause, MonoPair<CallInfo> callPair,
                           Memory memory) -> SMTRef;
auto nonmutualRecursiveForall(SMTRef clause, CallInfo call, Program prog,
                              Memory memory) -> SMTRef;
auto forallStartingAt(SMTRef clause, std::vector<std::string> freeVars,
                      int blockIndex, ProgramSelection prog,
                      std::string funName, bool main) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(SMTRef clause, SMTRef preClause,
                      std::vector<std::string> args1,
                      std::vector<std::string> args2) -> SMTRef;
auto inInvariant(MonoPair<const llvm::Function *> funs, SMTRef body,
                 Memory memory, const llvm::Module &mod1,
                 const llvm::Module &mod2, bool strings) -> SMTRef;
auto outInvariant(SMTRef body, Memory memory) -> SMTRef;
auto equalInputsEqualOutputs(std::vector<string> funArgs,
                             std::vector<string> funArgs1,
                             std::vector<string> funArgs2, std::string funName,
                             Memory memory) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> pathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap map1, PathMap map2, std::vector<string> funArgs,
              Memory memory) -> std::map<int, std::vector<std::string>>;

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

auto stringConstants(const llvm::Module &mod, string heap)
    -> std::vector<SMTRef>;
auto matchFunCalls(std::vector<CallInfo> callInfos1,
                   std::vector<CallInfo> callInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap map1, PathMap map2) -> void;
auto mapSubset(PathMap map1, PathMap map2) -> bool;
auto getDontLoopInvariant(SMTRef endClause, int startIndex, PathMap pathMap,
                          std::map<int, std::vector<string>> freeVarsMap,
                          Program prog, Memory memory, bool everythingSigned)
    -> SMTRef;
auto addAssignments(const SMTRef end, std::vector<AssignmentBlock> assignments)
    -> SMTRef;
auto addMemory(std::vector<SMTRef>& implArgs, Memory memory)
    -> std::function<void(CallInfo call, int index)>;
