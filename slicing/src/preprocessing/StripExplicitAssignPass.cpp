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
	std::vector<Function*> functionsToErase;

	for (Function& function: module) {
		if (ExplicitAssignPass::isExplicitAssignFunction(function)) {
			functionsToErase.push_back(&function);
		}

		for (BasicBlock& block: function) {

			vector<Instruction*> instructionsToErase;
			for (auto it = block.begin(); it != block.end(); it++){
				Instruction& instruction = *it;
				if (CallInst* call = dyn_cast<CallInst>(&instruction)) {
					if (call->getCalledFunction()
						&& ExplicitAssignPass::isExplicitAssignFunction(*call->getCalledFunction())) {
						call->replaceAllUsesWith(call->getArgOperand(0));
						instructionsToErase.push_back(call);
					}
				}
			}

			for (Instruction* instruction:instructionsToErase) {
				instruction->eraseFromParent();
			}
		}
	}

	for (Function* function:functionsToErase) {
		function->eraseFromParent();
	}

	return true;
}
