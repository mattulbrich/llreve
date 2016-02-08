#pragma once

#include "Assignment.h"
#include "Helper.h"
#include "Memory.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include <tuple>
#include <regex>

using std::make_shared;
using llvm::Instruction;

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

auto convertToSMT(llvm::Function &fun1, llvm::Function &fun2,
                  std::shared_ptr<llvm::FunctionAnalysisManager> fam1,
                  std::shared_ptr<llvm::FunctionAnalysisManager> fam2,
                  bool offByN, std::vector<SMTRef> &declarations, Memory heap,
                  bool everythingSigned) -> std::vector<SMTRef>;
auto mainAssertion(llvm::Function &fun1, llvm::Function &fun2,
                   std::shared_ptr<llvm::FunctionAnalysisManager> fam1,
                   std::shared_ptr<llvm::FunctionAnalysisManager> fam2,
                   bool offByN, std::vector<SMTRef> &declarations, bool onlyRec,
                   Memory heap, bool everythingSigned, bool dontNest)
    -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

auto getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                          std::map<int, std::vector<string>> freeVarsMap,
                          std::string funName,
                          std::vector<SMTRef> &declarations, Memory heap,
                          bool everythingSigned) -> std::vector<SMTRef>;
auto mainSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                           std::map<int, std::vector<string>> freeVarsMap,
                           std::string funName,
                           std::vector<SMTRef> &declarations, Memory heap,
                           bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto getForbiddenPaths(PathMap pathMap1, PathMap pathMap2,
                       BidirBlockMarkMap marked1, BidirBlockMarkMap marked2,
                       std::map<int, std::vector<string>> freeVarsMap,
                       bool offByN, std::string funName, bool main, Memory heap,
                       bool everythingSigned) -> std::vector<SMTRef>;
auto nonmutualPaths(PathMap pathMap, std::vector<SMTRef> &pathExprs,
                    std::map<int, std::vector<string>> freeVarsMap,
                    Program prog, std::string funName,
                    std::vector<SMTRef> &declarations, Memory heap,
                    bool everythingSigned) -> void;
auto getOffByNPaths(PathMap pathMap1, PathMap pathMap2,
                    std::map<int, std::vector<string>> freeVarsMap,
                    std::string funName, bool main, Memory heap,
                    bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                       std::map<int, std::vector<string>> freeVarsMap,
                       Program prog, std::string funName, bool main,
                       Memory heap, bool everythingSigned)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path path, Program prog,
                       std::vector<std::string> freeVars, bool toEnd,
                       Memory heap, bool everythingSigned)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(SMTRef endClause,
                           std::vector<AssignmentCallBlock> assignments1,
                           std::vector<AssignmentCallBlock> assignments2,
                           Memory heap) -> SMTRef;
auto nonmutualSMT(SMTRef endClause,
                  std::vector<AssignmentCallBlock> assignments, Program prog,
                  Memory heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef clause, CallInfo call1, CallInfo call2,
                           Memory heap) -> SMTRef;
auto nonmutualRecursiveForall(SMTRef clause, CallInfo call, Program prog,
                              Memory heap) -> SMTRef;
auto forallStartingAt(SMTRef clause, std::vector<std::string> freeVars,
                      int blockIndex, ProgramSelection prog,
                      std::string funName, bool main) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(SMTRef clause, SMTRef preClause,
                      std::vector<std::string> args1,
                      std::vector<std::string> args2) -> SMTRef;
auto inInvariant(const llvm::Function &fun1, const llvm::Function &fun2,
                 SMTRef body, Memory heap, const llvm::Module &mod1,
                 const llvm::Module &mod2, bool strings) -> SMTRef;
auto outInvariant(SMTRef body, Memory heap) -> SMTRef;
auto equalInputsEqualOutputs(std::vector<string> funArgs,
                             std::vector<string> funArgs1,
                             std::vector<string> funArgs2, std::string funName,
                             Memory heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> pathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap map1, PathMap map2, std::vector<string> funArgs,
              Memory heap) -> std::map<int, std::vector<std::string>>;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(const llvm::Function &fun1, const llvm::Function &fun2)
    -> std::pair<std::vector<std::string>, std::vector<std::string>>;
auto swapIndex(int i) -> int;
auto splitAssignments(std::vector<AssignmentCallBlock>)
    -> std::pair<std::vector<std::vector<AssignmentBlock>>,
                 std::vector<CallInfo>>;
auto stringConstants(const llvm::Module &mod, string heap)
    -> std::vector<SMTRef>;
auto matchFunCalls(std::vector<CallInfo> callInfos1,
                   std::vector<CallInfo> callInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap map1, PathMap map2) -> void;
auto mapSubset(PathMap map1, PathMap map2) -> bool;
auto getDontLoopInvariant(SMTRef endClause, int startIndex, PathMap pathMap,
                          std::map<int, std::vector<string>> freeVarsMap,
                          Program prog, Memory heap, bool everythingSigned)
    -> SMTRef;
