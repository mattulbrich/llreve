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

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"

#include <unordered_set>

class MarkAnalysisPass : public llvm::ModulePass {
public:
	static char ID;
	static std::string FUNCTION_NAME;


	MarkAnalysisPass() : llvm::ModulePass(ID) {markCounter = 0;}
	virtual bool runOnModule(llvm::Module &Fun) override;
	virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

private:
	std::unordered_set<llvm::BasicBlock*> marks;
	int markCounter;

	virtual int optimizeMark(llvm::BasicBlock* entry, llvm::BasicBlock* exit, llvm::Function &fun);
	virtual bool hasMark(llvm::BasicBlock* block);
	virtual void findMarks(llvm::Module &module);
	virtual void addLoopMarks(llvm::Function &function);

	void addMark(int mark, llvm::BasicBlock* block);
	void addMark(llvm::BasicBlock* block);	
	static llvm::Function& getMarkFunction(llvm::Module& module);
};
