#pragma once

#include "PathAnalysis.h"
#include "SMT.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include <tuple>
#include <regex>

using std::make_shared;
using llvm::Instruction;

const uint8_t HEAP_MASK = 0x01;
const uint8_t STACK_MASK = 0x02;

enum class InterleaveStep { StepBoth, StepFirst, StepSecond };

using Memory = uint8_t;

using Assignment = std::pair<std::string, SMTRef>;

auto makeAssignment(string Name, SMTRef Val) -> std::shared_ptr<Assignment>;

const std::regex HEAP_REGEX =
    std::regex("^(HEAP|STACK)\\$(1|2)(_old)?$", std::regex::ECMAScript);
const std::regex INDEX_REGEX =
    std::regex("^i(1|2)(_res|_old|_stack)?$", std::regex::ECMAScript);

struct CallInfo {
    std::string AssignedTo;
    std::string CallName;
    std::vector<SMTRef> Args;
    bool Extern;
    const llvm::Function &Fun;
    CallInfo(std::string AssignedTo, std::string CallName,
             std::vector<SMTRef> Args, bool Extern, const llvm::Function &Fun)
        : AssignedTo(AssignedTo), CallName(CallName), Args(Args),
          Extern(Extern), Fun(Fun) {}
    bool operator==(const CallInfo &Other) const {
        bool Result = CallName == Other.CallName;
        if (!Extern) {
            return Result;
        } else {
            // We don’t have a useful abstraction for extern functions which
            // don’t have the same number of arguments so we only want to couple
            // those that have one
            return Result &&
                   Fun.getFunctionType()->getNumParams() ==
                       Other.Fun.getFunctionType()->getNumParams();
        }
    }
};

enum class DefOrCallInfoTag { Call, Def };

struct DefOrCallInfo {
    std::shared_ptr<Assignment> Definition;
    std::shared_ptr<CallInfo> CallInfo_;
    enum DefOrCallInfoTag Tag;
    DefOrCallInfo(std::shared_ptr<Assignment> Definition)
        : Definition(Definition), CallInfo_(nullptr),
          Tag(DefOrCallInfoTag::Def) {}
    DefOrCallInfo(std::shared_ptr<struct CallInfo> CallInfo_)
        : Definition(nullptr), CallInfo_(CallInfo_),
          Tag(DefOrCallInfoTag::Call) {}
};

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

enum class Program { First, Second, Both };

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
                       int Program, Program For, std::string FunName, bool Main,
                       Memory Heap, bool Signed)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path Path, int Program,
                       std::vector<std::string> FreeVars, bool ToEnd,
                       Memory Heap, bool Signed)
    -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(SMTRef EndClause,
                           std::vector<AssignmentCallBlock> Assignments1,
                           std::vector<AssignmentCallBlock> Assignments2,
                           Memory Heap) -> SMTRef;
auto nonmutualSMT(SMTRef EndClause,
                  std::vector<AssignmentCallBlock> Assignments, Program For,
                  Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

auto invariant(int StartIndex, int EndIndex, std::vector<std::string> InputArgs,
               std::vector<std::string> EndArgs, Program SMTFor,
               std::string FunName, Memory Heap) -> SMTRef;
auto mainInvariant(int EndIndex, std::vector<string> FreeVars, string FunName,
                   Memory Heap) -> SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                          Program For, std::string FunName, Memory Heap)
    -> std::pair<SMTRef, SMTRef>;
auto mainInvariantDeclaration(int BlockIndex, std::vector<string> FreeVars,
                              Program For, std::string FunName) -> SMTRef;
auto invariantName(int Index, Program For, std::string FunName,
                   uint32_t VarArgs = 0) -> std::string;
auto dontLoopInvariant(SMTRef EndClause, int StartIndex, PathMap PathMap,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       int Program, Program For, Memory Heap, bool Signed)
    -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef Clause, CallInfo Call1, CallInfo Call2,
                           Memory Heap) -> SMTRef;
auto nonmutualRecursiveForall(SMTRef Clause, CallInfo Call, Program For,
                              Memory Heap) -> SMTRef;
auto forallStartingAt(SMTRef Clause, std::vector<std::string> FreeVars,
                      int BlockIndex, Program For, std::string FunName,
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
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

auto blockAssignments(const llvm::BasicBlock &BB,
                      const llvm::BasicBlock *PrevBB, bool OnlyPhis,
                      int Program, Memory Heap, bool Signed)
    -> std::vector<DefOrCallInfo>;
auto instrAssignment(const llvm::Instruction &Instr,
                     const llvm::BasicBlock *PrevBB, int Program, bool Signed)
    -> std::shared_ptr<std::pair<std::string, SMTRef>>;
auto predicateName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto predicateFun(const llvm::CmpInst::CmpInst &Pred, bool Signed)
    -> std::function<SMTRef(SMTRef)>;
auto opName(const llvm::BinaryOperator &Op) -> std::string;
auto combineOp(const llvm::BinaryOperator &Op)
    -> std::function<SMTRef(string, SMTRef, SMTRef)>;

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> PathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap Map1, PathMap Map2, std::vector<string> FunArgs,
              Memory Heap) -> std::map<int, std::vector<std::string>>;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(const llvm::Function &Fun1, const llvm::Function &Fun2)
    -> std::pair<std::vector<std::string>, std::vector<std::string>>;
auto filterVars(int Program, std::vector<std::string> Vars)
    -> std::vector<std::string>;
auto swapIndex(int I) -> int;
auto splitAssignments(std::vector<AssignmentCallBlock>)
    -> std::pair<std::vector<std::vector<AssignmentBlock>>,
                 std::vector<CallInfo>>;
auto toCallInfo(std::string AssignedTo, int Program,
                const llvm::CallInst &CallInst) -> std::shared_ptr<CallInfo>;
auto resolveHeapReferences(std::vector<std::string> Args, std::string Suffix,
                           Memory &Heap) -> std::vector<std::string>;
auto wrapHeap(SMTRef Inv, Memory Heap, std::vector<std::string> FreeVars)
    -> SMTRef;
auto adaptSizeToHeap(unsigned long Size, std::vector<string> FreeVars)
    -> unsigned long;
auto isStackOp(const llvm::Instruction &Inst) -> bool;
auto argSort(std::string Arg) -> std::string;
auto stringConstants(const llvm::Module &Mod, string Heap)
    -> std::vector<SMTRef>;
auto matchFunCalls(std::vector<CallInfo> CallInfos1,
                   std::vector<CallInfo> CallInfos2)
    -> std::vector<InterleaveStep>;
auto checkPathMaps(PathMap Map1, PathMap Map2) -> void;
auto mapSubset(PathMap Map1, PathMap Map2) -> bool;
auto memcpyIntrinsic(const llvm::CallInst *CallInst, int Program)
    -> std::vector<DefOrCallInfo>;
auto isPtrDiff(const llvm::Instruction &Instr) -> bool;
auto mergePathFuns(
    std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>> A,
    std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>> B)
    -> std::map<int, std::map<int, std::vector<std::function<SMTRef(SMTRef)>>>>;
