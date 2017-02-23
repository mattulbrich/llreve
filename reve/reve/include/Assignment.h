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

#include "Program.h"
#include "SMT.h"

#include "llvm/IR/Instructions.h"

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic
// blocks to SMT assignments

struct CallInfo {
    std::string assignedTo;
    std::string callName;
    std::vector<smt::SharedSMTRef> args;
    unsigned varArgs;
    const llvm::Function &fun;
    CallInfo(std::string assignedTo, std::string callName,
             std::vector<smt::SharedSMTRef> args, unsigned varArgs,
             const llvm::Function &fun)
        : assignedTo(assignedTo), callName(callName), args(args),
          varArgs(varArgs), fun(fun) {}
};

auto coupledCalls(const CallInfo &call1, const CallInfo &call2) -> bool;

enum class DefOrCallInfoTag { Call, Def };

struct DefOrCallInfo {
    std::unique_ptr<smt::Assignment> definition;
    std::unique_ptr<CallInfo> callInfo;
    DefOrCallInfoTag tag;
    DefOrCallInfo(std::unique_ptr<smt::Assignment> definition)
        : definition(std::move(definition)), callInfo(nullptr),
          tag(DefOrCallInfoTag::Def) {}
    DefOrCallInfo(std::unique_ptr<struct CallInfo> callInfo)
        : definition(nullptr), callInfo(std::move(callInfo)),
          tag(DefOrCallInfoTag::Call) {}
};

auto blockAssignments(const llvm::BasicBlock &bb,
                      const llvm::BasicBlock *prevBb, bool onlyPhis,
                      Program prog) -> std::vector<DefOrCallInfo>;
auto instrAssignment(const llvm::Instruction &instr,
                     const llvm::BasicBlock *prevBb, Program prog)
    -> llvm::SmallVector<std::unique_ptr<smt::Assignment>, 1>;
auto predicateName(const llvm::CmpInst::Predicate pred) -> std::string;
auto predicateFun(const llvm::CmpInst &pred, smt::SMTRef) -> smt::SMTRef;
auto fpPredicate(const llvm::CmpInst::Predicate pred) -> smt::FPCmp::Predicate;
auto binaryFPOpcode(const llvm::Instruction::BinaryOps op)
    -> smt::BinaryFPOperator::Opcode;
auto opName(const llvm::BinaryOperator &op) -> std::string;
auto combineOp(const llvm::BinaryOperator &op, std::string opName,
               smt::SMTRef firstArg, smt::SMTRef secondArg) -> smt::SMTRef;
auto memcpyIntrinsic(const llvm::CallInst *callInst, Program prog)
    -> std::vector<DefOrCallInfo>;
auto toCallInfo(std::string assignedTo, Program prog,
                const llvm::CallInst &callInst) -> std::unique_ptr<CallInfo>;
auto isPtrDiff(const llvm::Instruction &instr) -> bool;
