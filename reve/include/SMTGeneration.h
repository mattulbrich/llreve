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
    std::vector<DefOrCallInfo> Definitions;
    SMTRef Condition;
    AssignmentCallBlock(std::vector<DefOrCallInfo> Definitions,
                        SMTRef Condition)
        : Definitions(Definitions), Condition(Condition) {}
};

struct AssignmentBlock {
    std::vector<Assignment> Definitions;
    SMTRef Condition;
    AssignmentBlock(std::vector<Assignment> Definitions, SMTRef Condition)
        : Definitions(Definitions), Condition(Condition) {}
};

auto convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                  std::shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                  std::shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                  bool OffByN, std::vector<SMTRef> &Declarations, Memory Heap,
                  bool Signed) -> std::vector<SMTRef>;
auto mainAssertion(llvm::Function &Fun1, llvm::Function &Fun2,
                   std::shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                   std::shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                   bool OffByN, std::vector<SMTRef> &Declarations, bool OnlyRec,
                   Memory Heap, bool Signed, bool DontNest)
    -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

auto synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       std::string FunName, std::vector<SMTRef> &Declarations,
                       Memory Heap, bool Signed) -> std::vector<SMTRef>;
auto mainSynchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                           std::map<int, std::vector<string>> FreeVarsMap,
                           std::string FunName,
                           std::vector<SMTRef> &Declarations, Memory Heap,
                           bool Signed)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
                    BidirBlockMarkMap Marked1, BidirBlockMarkMap Marked2,
                    std::map<int, std::vector<string>> FreeVarsMap, bool OffByN,
                    std::string FunName, bool Main, Memory Heap, bool Signed)
    -> std::vector<SMTRef>;
auto nonmutualPaths(PathMap PathMap, std::vector<SMTRef> &PathExprs,
                    std::map<int, std::vector<string>> FreeVarsMap, Program For,
                    std::string FunName, std::vector<SMTRef> &Declarations,
                    Memory Heap, bool Signed) -> void;
auto offByNPaths(PathMap PathMap1, PathMap PathMap2,
                 std::map<int, std::vector<string>> FreeVarsMap,
                 std::string FunName, bool Main, Memory Heap, bool Signed)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
auto offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       Program Prog, std::string FunName, bool Main,
                       Memory Heap, bool Signed)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path Path, Program Prog,
                       std::vector<std::string> FreeVars, bool ToEnd,
                       Memory Heap, bool Signed)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(SMTRef EndClause,
                           std::vector<AssignmentCallBlock> Assignments1,
                           std::vector<AssignmentCallBlock> Assignments2,
                           Memory Heap) -> SMTRef;
auto nonmutualSMT(SMTRef EndClause,
                  std::vector<AssignmentCallBlock> Assignments, Program Prog,
                  Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef Clause, CallInfo Call1, CallInfo Call2,
                           Memory Heap) -> SMTRef;
auto nonmutualRecursiveForall(SMTRef Clause, CallInfo Call, Program Prog,
                              Memory Heap) -> SMTRef;
auto forallStartingAt(SMTRef Clause, std::vector<std::string> FreeVars,
                      int BlockIndex, ProgramSelection For, std::string FunName,
                      bool Main) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(SMTRef Clause, SMTRef PreClause,
                      std::vector<std::string> Args1,
                      std::vector<std::string> Args2) -> SMTRef;
auto inInvariant(const llvm::Function &Fun1, const llvm::Function &Fun2,
                 SMTRef Body, Memory Heap, const llvm::Module &Mod1,
                 const llvm::Module &Mod2, bool Strings) -> SMTRef;
auto outInvariant(SMTRef Body, Memory Heap) -> SMTRef;
auto equalInputsEqualOutputs(std::vector<string> FunArgs,
                             std::vector<string> FunArgs1,
                             std::vector<string> FunArgs2, std::string FunName,
                             Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> PathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap Map1, PathMap Map2, std::vector<string> FunArgs,
              Memory Heap) -> std::map<int, std::vector<std::string>>;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(const llvm::Function &Fun1, const llvm::Function &Fun2)
    -> std::pair<std::vector<std::string>, std::vector<std::string>>;
auto swapIndex(int I) -> int;
auto splitAssignments(std::vector<AssignmentCallBlock>)
    -> std::pair<std::vector<std::vector<AssignmentBlock>>,
                 std::vector<CallInfo>>;
auto stringConstants(const llvm::Module &Mod, string Heap)
    -> std::vector<SMTRef>;
auto matchFunCalls(std::vector<CallInfo> CallInfos1,
                   std::vector<CallInfo> CallInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap Map1, PathMap Map2) -> void;
auto mapSubset(PathMap Map1, PathMap Map2) -> bool;
auto dontLoopInvariant(SMTRef EndClause, int StartIndex, PathMap PathMap,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       Program Prog, Memory Heap, bool Signed) -> SMTRef;
