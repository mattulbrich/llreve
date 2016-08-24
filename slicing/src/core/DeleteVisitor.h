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
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Dominators.h"

/**
 * Removes the visited operation and manipulates the IR accordingly
 * to produce a prooper slice.
 *
 * The retun type of the visit methods states if the instruction
 * could be removed.
 */
class DeleteVisitor: public llvm::InstVisitor<DeleteVisitor, bool> {
public:
	DeleteVisitor(llvm::DominatorTree* domTree){domTree_ = domTree;}
	bool visitInstruction(llvm::Instruction &I);
	bool visitTerminatorInst(llvm::TerminatorInst &I);
	bool visitCallInst(llvm::CallInst &I);
	bool visitBranchInst(llvm::BranchInst &I);

	/**
	 * Phi nodes may contain inlined constants and arguments,
	 * from privious blocks. Those will be deleted.
	 */
	bool visitPHINode(llvm::PHINode &I);

private:
	llvm::DominatorTree* domTree_;

	bool isPriviousDef(const llvm::DIVariable* variable, llvm::Instruction& instruction);
	llvm::Instruction* findPriviousDef(const llvm::DIVariable* variable, llvm::Instruction& instruction);

	bool handleNoUses(llvm::Instruction& instruction);
	bool handleHasPriviousDef(llvm::Instruction& instruction, llvm::DIVariable* variable);
	bool handleIsArgument(llvm::Instruction& instruction, llvm::DIVariable* variable);
	bool handleSinglePhiUse(llvm::Instruction& instruction);
};
