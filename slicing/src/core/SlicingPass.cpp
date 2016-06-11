#include "SlicingPass.h"
#include "AddVariableNamePass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "core/DeleteVisitor.h"

#include "llvm/IR/Dominators.h"

#include <queue>
#include <iostream>

using namespace llvm;


char SlicingPass::ID = 0;

void SlicingPass::toBeSliced(llvm::Instruction& instruction) {
	LLVMContext& context = instruction.getContext();
	MDNode* node = MDNode::get(context, ConstantAsMetadata::get(ConstantInt::getTrue(context)));
	instruction.setMetadata("sliced", node);
}

bool SlicingPass::isToBeSliced(llvm::Instruction& instruction){
	if (instruction.getMetadata("sliced")) {
		return true;
	} else {
		return false;
	}
}

bool SlicingPass::runOnFunction(llvm::Function& function){
	this->domTree = &getAnalysis<llvm::DominatorTreeWrapperPass>().getDomTree();
	std::queue<llvm::Instruction*> instructionsToDelete;

	for(llvm::BasicBlock& block: function) {
		for(llvm::Instruction& instruction: block) {
			if (SlicingPass::isToBeSliced(instruction)) {
				instructionsToDelete.push(&instruction);
			}
		}
	}

	std::queue<llvm::Instruction*> secondTry;

	std::queue<llvm::Instruction*>* activeQueue = &instructionsToDelete;
	std::queue<llvm::Instruction*>* secondQueue = &secondTry;

	bool changed = true;
	while(changed) {
		changed = false;

		while (!instructionsToDelete.empty()) {
			Instruction& instruction = *activeQueue->front();
			activeQueue->pop();

			DeleteVisitor visitor(this->domTree);
			bool deleted = visitor.visit(instruction);

			if (!deleted) {
				changed = true;
				secondQueue->push(&instruction);
			}
		}

		std::queue<llvm::Instruction*>* temp;
		temp = activeQueue;
		activeQueue = secondQueue;
		secondQueue = temp;
	}

	return true;
}

void SlicingPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
	AU.addRequired<llvm::DominatorTreeWrapperPass>();
}
