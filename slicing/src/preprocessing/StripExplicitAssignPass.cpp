/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "StripExplicitAssignPass.h"

#include "preprocessing/ExplicitAssignPass.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

#include <vector>

char StripExplicitAssignPass::ID = 0;

using namespace llvm;
using namespace std;

bool StripExplicitAssignPass::runOnModule(llvm::Module &module){
	std::vector<Function*> toErase;

	for (Function& function: module) {
		if (function.getName().find(
				ExplicitAssignPass::FUNCTION_NAME) == 0) {
			toErase.push_back(&function);
		}

		for (BasicBlock& block: function) {

			vector<Instruction*> toDelete;
			for (auto it = block.begin(); it != block.end(); it++){
				Instruction& instruction = *it;
				if (CallInst* call = dyn_cast<CallInst>(&instruction)) {
					if (call->getCalledFunction()
						&& (call->getCalledFunction()->getName().find(
								ExplicitAssignPass::FUNCTION_NAME) == 0)) {
						call->replaceAllUsesWith(call->getArgOperand(0));
						toDelete.push_back(call);
					}
				}
			}

			for (Instruction* instruction:toDelete) {
				instruction->eraseFromParent();
			}
		}
	}

	for (Function* function:toErase) {
		function->eraseFromParent();
	}

	return true;
}
