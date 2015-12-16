#ifndef SMT_GENERATION_H
#define SMT_GENERATION_H

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

enum InterleaveStep { StepBoth, StepFirst, StepSecond };

using Memory = uint8_t;

using Assignment = std::tuple<std::string, SMTRef>;

const std::regex HEAP_REGEX =
    std::regex("^(HEAP|STACK)\\$(1|2)(_old)?$", std::regex::ECMAScript);
const std::regex INDEX_REGEX =
    std::regex("^i(1|2)(_res|_old|_stack)?$", std::regex::ECMAScript);

struct CallInfo {
    std::string AssignedTo;
    std::string CallName;
    std::vector<SMTRef> Args;
    bool Extern;
    CallInfo(std::string AssignedTo, std::string CallName,
             std::vector<SMTRef> Args, bool Extern)
        : AssignedTo(AssignedTo), CallName(CallName), Args(Args),
          Extern(Extern) {}
};

enum DefOrCallInfoTag { Call, Def };

struct DefOrCallInfo {
    std::shared_ptr<Assignment> Definition;
    std::shared_ptr<CallInfo> CallInfo_;
    enum DefOrCallInfoTag Tag;
    DefOrCallInfo(std::shared_ptr<Assignment> Definition)
        : Definition(Definition), CallInfo_(nullptr), Tag(Def) {}
    DefOrCallInfo(std::shared_ptr<struct CallInfo> CallInfo_)
        : Definition(nullptr), CallInfo_(CallInfo_), Tag(Call) {}
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

enum SMTFor { First, Second, Both };

auto convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                  std::shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                  std::shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                  bool OffByN, std::vector<SMTRef> &Declarations, Memory Heap)
    -> std::vector<SMTRef>;
auto mainAssertion(llvm::Function &Fun1, llvm::Function &Fun2,
                   std::shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                   std::shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                   bool OffByN, std::vector<SMTRef> &Declarations, bool OnlyRec,
                   Memory Heap) -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

auto synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       std::string FunName, std::vector<SMTRef> &Declarations,
                       Memory Heap) -> std::vector<SMTRef>;
auto mainSynchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                           std::map<int, std::vector<string>> FreeVarsMap,
                           std::string FunName,
                           std::vector<SMTRef> &Declarations, Memory Heap)
    -> std::vector<SMTRef>;
auto forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
                    BidirBlockMarkMap Marked1, BidirBlockMarkMap Marked2,
                    std::map<int, std::vector<string>> FreeVarsMap, bool OffByN,
                    std::string FunName, bool Main, Memory Heap)
    -> std::vector<SMTRef>;
auto nonmutualPaths(PathMap PathMap, std::vector<SMTRef> &PathExprs,
                    std::map<int, std::vector<string>> FreeVarsMap, SMTFor For,
                    std::string FunName, std::vector<SMTRef> &Declarations,
                    Memory Heap) -> void;
auto offByNPaths(PathMap PathMap1, PathMap PathMap2,
                 std::map<int, std::vector<string>> FreeVarsMap,
                 std::string FunName, bool Main, Memory Heap)
    -> std::vector<SMTRef>;
auto offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       int Program, SMTFor For, std::string FunName, bool Main,
                       Memory Heap) -> std::vector<SMTRef>;

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

auto assignmentsOnPath(Path Path, int Program,
                       std::vector<std::string> FreeVars, bool ToEnd,
                       Memory Heap) -> std::vector<AssignmentCallBlock>;
auto interleaveAssignments(SMTRef EndClause,
                           std::vector<AssignmentCallBlock> Assignments1,
                           std::vector<AssignmentCallBlock> Assignments2,
                           Memory Heap) -> SMTRef;
auto nonmutualSMT(SMTRef EndClause,
                  std::vector<AssignmentCallBlock> Assignments, SMTFor For,
                  Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

auto invariant(int StartIndex, int EndIndex, std::vector<std::string> InputArgs,
               std::vector<std::string> EndArgs, SMTFor SMTFor,
               std::string FunName, Memory Heap) -> SMTRef;
auto mainInvariant(int EndIndex, std::vector<string> FreeVars, string FunName,
                   Memory Heap) -> SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                          SMTFor For, std::string FunName, Memory Heap)
    -> std::pair<SMTRef, SMTRef>;
auto mainInvariantDeclaration(int BlockIndex, std::vector<string> FreeVars,
                              SMTFor For, std::string FunName) -> SMTRef;
auto invariantName(int Index, SMTFor For, std::string FunName) -> std::string;
auto dontLoopInvariant(SMTRef EndClause, int StartIndex, PathMap PathMap,
                       std::map<int, std::vector<string>> FreeVarsMap,
                       int Program, SMTFor For, Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

auto mutualRecursiveForall(SMTRef Clause, std::vector<SMTRef> Args1,
                           std::vector<SMTRef> Args2, std::string Ret1,
                           std::string Ret2, std::string FunName, bool Extern,
                           Memory Heap) -> SMTRef;
auto nonmutualRecursiveForall(SMTRef Clause, std::vector<SMTRef> Args,
                              std::string Ret, SMTFor For, std::string FunName,
                              bool Extern, Memory Heap) -> SMTRef;
auto assertForall(SMTRef Clause, std::vector<std::string> FreeVars,
                  int BlockIndex, SMTFor For, std::string FunName, bool Main)
    -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

auto makeFunArgsEqual(SMTRef Clause, SMTRef PreClause,
                      std::vector<std::string> Args1,
                      std::vector<std::string> Args2) -> SMTRef;
auto inInvariant(llvm::Function &Fun1, llvm::Function &Fun2, SMTRef Body,
                 Memory Heap, llvm::Module &Mod1, llvm::Module &Mod2,
                 bool Strings) -> SMTRef;
auto outInvariant(SMTRef Body, Memory Heap) -> SMTRef;
auto equalInputsEqualOutputs(std::vector<string> FunArgs,
                             std::vector<string> FunArgs1,
                             std::vector<string> FunArgs2, std::string FunName,
                             Memory Heap) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

auto blockAssignments(llvm::BasicBlock *BB, llvm::BasicBlock *PrevBB,
                      bool IgnorePhis, bool OnlyPhis, int Program,
                      set<string> &Constructed, Memory Heap)
    -> std::vector<DefOrCallInfo>;
auto instrAssignment(llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
                     set<string> &Constructed, int Program)
    -> std::shared_ptr<std::tuple<std::string, SMTRef>>;
auto predicateName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto opName(const llvm::BinaryOperator &Op) -> std::string;
auto instrNameOrVal(const llvm::Value *Val, const llvm::Type *Ty,
                    std::set<std::string> &Constructed) -> SMTRef;

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

auto freeVarsForBlock(std::map<int, Paths> PathMap)
    -> std::pair<std::set<std::string>, std::map<int, std::set<std::string>>>;
auto freeVars(PathMap Map1, PathMap Map2, std::vector<string> FunArgs,
              Memory Heap) -> std::map<int, std::vector<std::string>>;

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

auto functionArgs(llvm::Function &Fun1, llvm::Function &Fun2)
    -> std::pair<std::vector<std::string>, std::vector<std::string>>;
auto filterVars(int Program, std::vector<std::string> Vars)
    -> std::vector<std::string>;
auto swapIndex(int I) -> int;
auto splitAssignments(std::vector<AssignmentCallBlock>)
    -> std::pair<std::vector<std::vector<AssignmentBlock>>,
                 std::vector<CallInfo>>;
auto toCallInfo(std::string AssignedTo, int Program,
                const llvm::CallInst *CallInst, set<string> &Constructed)
    -> std::shared_ptr<CallInfo>;
auto resolveHeapReferences(std::vector<std::string> Args, std::string Suffix,
                           Memory &Heap) -> std::vector<std::string>;
auto wrapHeap(SMTRef Inv, Memory Heap, std::vector<std::string> FreeVars)
    -> SMTRef;
auto resolveName(std::string Name, std::set<std::string> &Constructed)
    -> std::string;
auto adaptSizeToHeap(unsigned long Size, std::vector<string> FreeVars)
    -> unsigned long;
auto flagInstr(llvm::Instruction &Instr, std::string Flag) -> void;
template <typename T>
auto resolveGEP(T &GEP, set<string> &Constructed) -> SMTRef;
auto isStackOp(const llvm::Instruction *Inst) -> bool;
auto argSort(std::string Arg) -> std::string;
auto stringConstants(llvm::Module &Mod, string Heap) -> std::vector<SMTRef>;
auto matchFunCalls(std::vector<CallInfo> CallInfos1,
                   std::vector<CallInfo> CallInfos2)
    -> std::vector<InterleaveStep>;

#endif // SMT_GENERATION_H
