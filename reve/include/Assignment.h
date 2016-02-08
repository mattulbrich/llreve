#pragma once

#include "Memory.h"
#include "Program.h"

#include "llvm/IR/Instructions.h"

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

using Assignment = std::pair<std::string, SMTRef>;

auto makeAssignment(string Name, SMTRef Val) -> std::shared_ptr<Assignment>;

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

auto blockAssignments(const llvm::BasicBlock &BB,
                      const llvm::BasicBlock *PrevBB, bool OnlyPhis,
                      Program Prog, Memory Heap, bool Signed)
    -> std::vector<DefOrCallInfo>;
auto instrAssignment(const llvm::Instruction &Instr,
                     const llvm::BasicBlock *PrevBB, Program Prog, bool Signed)
    -> std::shared_ptr<std::pair<std::string, SMTRef>>;
auto predicateName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto predicateFun(const llvm::CmpInst::CmpInst &Pred, bool Signed)
    -> std::function<SMTRef(SMTRef)>;
auto opName(const llvm::BinaryOperator &Op) -> std::string;
auto combineOp(const llvm::BinaryOperator &Op)
    -> std::function<SMTRef(string, SMTRef, SMTRef)>;
auto memcpyIntrinsic(const llvm::CallInst *CallInst, Program Prog)
    -> std::vector<DefOrCallInfo>;
auto toCallInfo(std::string AssignedTo, Program Prog,
                const llvm::CallInst &CallInst) -> std::shared_ptr<CallInfo>;
auto isPtrDiff(const llvm::Instruction &Instr) -> bool;
auto isStackOp(const llvm::Instruction &Inst) -> bool;
