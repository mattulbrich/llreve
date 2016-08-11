/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "PromoteAssertSlicedPass.h"
#include "preprocessing/ExplicitAssignPass.h"

#include "llvm/IR/IntrinsicInst.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Verifier.h"

#include "core/Util.h"
#include <iostream>
#include <set>

using namespace llvm;

char PromoteAssertSlicedPass::ID = 0;
std::string PromoteAssertSlicedPass::ASSERT_SLICED = "assert_sliced";
std::string PromoteAssertSlicedPass::FUNCTION_NAME = "__assert_sliced";

PromoteAssertSlicedPass::PromoteAssertSlicedPass(): llvm::FunctionPass(ID) {
	//ctor
}

PromoteAssertSlicedPass::~PromoteAssertSlicedPass() {
	//dtor
}

bool PromoteAssertSlicedPass::runOnFunction(llvm::Function& fun) {
	std::set<Instruction*> toDelete;

	Instruction* priviousInstruction = nullptr;
	for(Instruction& instruction : Util::getInstructions(fun)) {
		if (CallInst* call = dyn_cast<CallInst>(&instruction)) {
			if (call->getCalledFunction()
					&& call->getCalledFunction()->getName() == FUNCTION_NAME) {
				Value* assertedValue = call->getArgOperand(0);

				Instruction* assertedInstruction = dyn_cast<Instruction>(assertedValue);

				if (priviousInstruction)
					if (CallInst* assignment = dyn_cast<CallInst>(priviousInstruction))
						if (assignment->getCalledFunction()
							&& assignment->getCalledFunction()->getName()
								== ExplicitAssignPass::FUNCTION_NAME){
							if (assignment->getArgOperand(0) == call->getArgOperand(0)) {
								assertedInstruction = assignment;
							}
				}

				if (assertedInstruction) {
					markAssertSliced(*assertedInstruction);
					assert(!instruction.hasNUsesOrMore(1) && "Please make sure __assert_sliced is not used!");
					toDelete.insert(&instruction);
				}
			}
		}
		priviousInstruction = &instruction;
	}

	for (Instruction* instruction: toDelete) {
		instruction->eraseFromParent();
	}

	bool hasError = llvm::verifyFunction(fun, &errs());
	assert(!hasError && "Internal Error: PromoteAssertSlicedPass produced slice candidate, which ist not a valid llvm program.");

	return true;
}

void PromoteAssertSlicedPass::getAnalysisUsage(llvm::AnalysisUsage& AU) const {

}

void PromoteAssertSlicedPass::markAssertSliced(llvm::Instruction& instruction) {
	LLVMContext& context = instruction.getContext();
	MDString* metadata = MDString::get(context, ASSERT_SLICED.c_str());
	MDNode* node = MDNode::get(context, metadata);
	instruction.setMetadata(ASSERT_SLICED, node);
}

bool PromoteAssertSlicedPass::isAssertSliced(llvm::Instruction& instruction) {
    if (auto metaData = instruction.getMetadata(ASSERT_SLICED)) {
        std::string data = cast<MDString>(metaData->getOperand(0))->getString();
        if (data == ASSERT_SLICED) {
            return true;
        }
    }

    return false;
}


