#ifndef SMT_GENERATION_H
#define SMT_GENERATION_H

#include "PathAnalysis.h"
#include "SMT.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Instructions.h"

#include <tuple>

using std::make_shared;
using llvm::Instruction;

using Assignment = std::tuple<std::string, SMTRef>;

struct CallInfo {
    std::string AssignedTo;
    std::string CallName;
    std::vector<SMTRef> Args;
    CallInfo(std::string AssignedTo, std::string CallName,
             std::vector<SMTRef> Args)
        : AssignedTo(AssignedTo), CallName(CallName), Args(Args) {}
};

enum DefOrCallInfoTag { Call, Def };

struct DefOrCallInfo {
    std::shared_ptr<Assignment> Definition;
    std::shared_ptr<CallInfo> CallInfo;
    enum DefOrCallInfoTag Tag;
    DefOrCallInfo(std::shared_ptr<Assignment> Definition)
        : Definition(Definition), CallInfo(nullptr), Tag(Def) {}
    DefOrCallInfo(std::shared_ptr<struct CallInfo> CallInfo)
        : Definition(nullptr), CallInfo(CallInfo), Tag(Call) {}
};

struct Assignments {
    std::vector<DefOrCallInfo> Definitions;
    SMTRef Condition;
    Assignments(std::vector<DefOrCallInfo> Definitions, SMTRef Condition)
        : Definitions(Definitions), Condition(Condition) {}
};

struct CleanAssignments {
    std::vector<Assignment> Definitions;
    SMTRef Condition;
    CleanAssignments(std::vector<Assignment> Definitions, SMTRef Condition)
        : Definitions(Definitions), Condition(Condition) {}
};

enum SMTFor { First, Second, Both };

auto convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                  std::unique_ptr<llvm::FunctionAnalysisManager> Fam1,
                  std::unique_ptr<llvm::FunctionAnalysisManager> Fam2) -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

auto synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                       std::map<int, set<string>> FreeVarsMap,
                       std::vector<string> FunArgs1,
                       std::vector<string> FunArgs2)
    -> std::pair<std::vector<SMTRef>, std::vector<SMTRef>>;
auto forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
                    std::map<int, set<string>> FreeVarsMap,
                    std::vector<string> FunArgs1, std::vector<string> FunArgs2)
    -> std::vector<SMTRef>;
auto smtForNonMutualPaths(PathMap PathMap, std::vector<SMTRef> &PathExprs,
                 std::vector<SMTRef> &InvariantDefs,
                 std::map<int, set<string>> FreeVarsMap,
                 std::vector<string> FunArgs, SMTFor For) -> void;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto pathToSMT(Path Path, int Program, std::set<std::string> FreeVars,
               bool ToEnd) -> std::vector<Assignments>;
auto interleaveSMT(SMTRef EndClause, std::vector<Assignments> Assignments1,
                   std::vector<Assignments> Assignments2,
                   std::vector<string> FunArgs1, std::vector<string> FunArgs2)
    -> SMTRef;
auto standaloneSMT(SMTRef EndClause, std::vector<Assignments> Assignments,
                   std::vector<string> FunArgs, SMTFor For) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

auto invariant(int StartIndex, int EndIndex, std::set<std::string> InputArgs,
               std::set<std::string> EndArgs, SMTFor SMTFor) -> SMTRef;
auto invariantDef(int BlockIndex, std::set<std::string> FreeVars, SMTFor For)
    -> std::pair<SMTRef, SMTRef>;
auto invName(int Index, SMTFor For) -> std::string;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef Clause, std::vector<SMTRef> Args1,
                           std::vector<SMTRef> Args2, std::string Ret1,
                           std::string Ret2, std::vector<string> FunArgs1,
                           std::vector<string> FunArgs2) -> SMTRef;
auto recursiveForall(SMTRef Clause, std::vector<SMTRef> Args, std::string Ret,
                     std::vector<string> FunArgs, SMTFor For) -> SMTRef;
auto wrapToplevelForall(SMTRef Clause, std::set<std::string> Args) -> SMTRef;
auto wrapForall(SMTRef Clause, std::set<std::string> FreeVars, int BlockIndex,
                SMTFor For) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(SMTRef Clause, SMTRef PreClause,
                      std::set<std::string> Args1, std::set<std::string> Args2)
    -> SMTRef;
auto equalInputsEqualOutputs(set<string> FunArgs, std::vector<string> FunArgs1,
                             std::vector<string> FunArgs2) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

auto instrToDefs(const llvm::BasicBlock *BB, const llvm::BasicBlock *PrevBB,
                 bool IgnorePhis, bool OnlyPhis, int Program,
                 set<string> &Constructed) -> std::vector<DefOrCallInfo>;
auto toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
           set<string> &Constructed)
    -> std::shared_ptr<std::tuple<std::string, SMTRef>>;
auto getPredicateName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto getOpName(const llvm::BinaryOperator &Op) -> std::string;
auto getInstrNameOrValue(const llvm::Value *Val, const llvm::Type *Ty,
                         std::set<std::string> &Constructed) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

auto freeVars(std::map<int, Paths> PathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVarsMap(PathMap Map1, PathMap Map2, set<string> FunArgs)
    -> std::map<int, std::set<std::string>>;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(llvm::Function &Fun1, llvm::Function &Fun2)
    -> std::pair<std::vector<std::string>, std::vector<std::string>>;
auto filterVars(int Program, std::set<std::string> Vars)
    -> std::set<std::string>;
auto swapIndex(int I) -> int;
auto splitAssignments(std::vector<Assignments>)
    -> std::pair<std::vector<std::vector<CleanAssignments>>,
                 std::vector<CallInfo>>;
auto toCallInfo(std::string AssignedTo, const llvm::CallInst *CallInst,
                set<string> &Constructed) -> std::shared_ptr<CallInfo>;

#endif // SMT_GENERATION_H
