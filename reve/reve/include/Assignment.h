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
    std::shared_ptr<const smt::Assignment> definition;
    std::shared_ptr<CallInfo> callInfo;
    DefOrCallInfoTag tag;
    DefOrCallInfo(std::shared_ptr<const smt::Assignment> definition)
        : definition(definition), callInfo(nullptr),
          tag(DefOrCallInfoTag::Def) {}
    DefOrCallInfo(std::shared_ptr<struct CallInfo> callInfo)
        : definition(nullptr), callInfo(callInfo), tag(DefOrCallInfoTag::Call) {
    }
};

auto blockAssignments(const llvm::BasicBlock &bb,
                      const llvm::BasicBlock *prevBb, bool onlyPhis,
                      Program prog) -> std::vector<DefOrCallInfo>;
auto instrAssignment(const llvm::Instruction &instr,
                     const llvm::BasicBlock *prevBb, Program prog)
    -> std::vector<std::shared_ptr<const smt::Assignment>>;
auto predicateName(const llvm::CmpInst::Predicate pred) -> std::string;
auto predicateFun(const llvm::CmpInst &pred)
    -> std::function<smt::SMTRef(smt::SMTRef)>;
auto fpPredicate(const llvm::CmpInst::Predicate pred) -> smt::FPCmp::Predicate;
auto binaryFPOpcode(const llvm::Instruction::BinaryOps op)
    -> smt::BinaryFPOperator::Opcode;
auto opName(const llvm::BinaryOperator &op) -> std::string;
auto combineOp(const llvm::BinaryOperator &op)
    -> std::function<smt::SMTRef(std::string, smt::SMTRef, smt::SMTRef)>;
auto memcpyIntrinsic(const llvm::CallInst *callInst, Program prog)
    -> std::vector<DefOrCallInfo>;
auto toCallInfo(std::string assignedTo, Program prog,
                const llvm::CallInst &callInst) -> std::shared_ptr<CallInfo>;
auto isPtrDiff(const llvm::Instruction &instr) -> bool;
