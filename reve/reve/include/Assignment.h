#pragma once

#include "Memory.h"
#include "Program.h"

#include "llvm/IR/Instructions.h"

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

struct CallInfo {
    std::string assignedTo;
    std::string callName;
    std::vector<smt::SharedSMTRef> args;
    bool externFun;
    const llvm::Function &fun;
    CallInfo(std::string assignedTo, std::string callName,
             std::vector<smt::SharedSMTRef> args, bool externFun,
             const llvm::Function &fun)
        : assignedTo(assignedTo), callName(callName), args(args),
          externFun(externFun), fun(fun) {}
    bool operator==(const CallInfo &other) const {
        bool result = callName == other.callName;
        if (!externFun) {
            return result;
        } else {
            // We don’t have a useful abstraction for extern functions which
            // don’t have the same number of arguments so we only want to couple
            // those that have one
            return result &&
                   fun.getFunctionType()->getNumParams() ==
                       other.fun.getFunctionType()->getNumParams();
        }
    }
};

enum class DefOrCallInfoTag { Call, Def };

struct DefOrCallInfo {
    std::shared_ptr<const smt::Assignment> definition;
    std::shared_ptr<CallInfo> callInfo;
    enum DefOrCallInfoTag tag;
    DefOrCallInfo(std::shared_ptr<const smt::Assignment> definition)
        : definition(definition), callInfo(nullptr),
          tag(DefOrCallInfoTag::Def) {}
    DefOrCallInfo(std::shared_ptr<struct CallInfo> callInfo)
        : definition(nullptr), callInfo(callInfo), tag(DefOrCallInfoTag::Call) {
    }
};

auto blockAssignments(const llvm::BasicBlock &bb,
                      const llvm::BasicBlock *prevBb, bool onlyPhis,
                      Program prog, Memory heap) -> std::vector<DefOrCallInfo>;
auto instrAssignment(const llvm::Instruction &instr,
                     const llvm::BasicBlock *prevBb, Program prog)
    -> std::unique_ptr<const smt::Assignment>;
auto predicateName(const llvm::CmpInst::Predicate pred) -> std::string;
auto predicateFun(const llvm::CmpInst::CmpInst &pred)
    -> std::function<smt::SMTRef(smt::SMTRef)>;
auto opName(const llvm::BinaryOperator &op) -> std::string;
auto combineOp(const llvm::BinaryOperator &op)
    -> std::function<smt::SMTRef(std::string, smt::SMTRef, smt::SMTRef)>;
auto memcpyIntrinsic(const llvm::CallInst *callInst, Program prog)
    -> std::vector<DefOrCallInfo>;
auto toCallInfo(std::string assignedTo, Program prog,
                const llvm::CallInst &callInst) -> std::shared_ptr<CallInfo>;
auto isPtrDiff(const llvm::Instruction &instr) -> bool;
auto isStackOp(const llvm::Instruction &inst) -> bool;
