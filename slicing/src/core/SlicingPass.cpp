// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "SlicingPass.h"
#include "AddVariableNamePass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Verifier.h"

#include "core/DeleteVisitor.h"
#include "core/Util.h"

#include "llvm/IR/Dominators.h"

#include <queue>
#include <set>
#include <iostream>

using namespace llvm;


char SlicingPass::ID = 0;

const std::string SlicingPass::TO_BE_SLICED = "to be sliced";
const std::string SlicingPass::NOT_SLICED = "not sliced";
const std::string SlicingPass::SLICE = "slice";

SlicingPass::SlicingPass() : llvm::FunctionPass(ID) {
	this->hasUnSlicedInstructions_ = false;
}

void SlicingPass::toBeSliced(llvm::Instruction& instruction) {
	LLVMContext& context = instruction.getContext();
	MDString* metadata = MDString::get(context, TO_BE_SLICED.c_str());
	MDNode* node = MDNode::get(context, metadata);
	instruction.setMetadata(SLICE, node);
}

void SlicingPass::markNotSliced(llvm::Instruction& instruction) {
	LLVMContext& context = instruction.getContext();
	MDString* metadata = MDString::get(context, NOT_SLICED.c_str());
	MDNode* node = MDNode::get(context, metadata);
	instruction.setMetadata(SLICE, node);
}

bool SlicingPass::isToBeSliced(llvm::Instruction& instruction){
	if (instruction.getMetadata(SLICE)) {
		return true;
	} else {
		return false;
	}
}

bool SlicingPass::isNotSliced(llvm::Instruction& instruction){
	if (auto metadata = instruction.getMetadata(SLICE)) {
		std::string data = cast<MDString>(metadata->getOperand(0))->getString();
		if (data == NOT_SLICED) {
			return true;
		}
	}

	return false;
}


bool SlicingPass::runOnFunction(llvm::Function& function){
	this->domTree = &getAnalysis<llvm::DominatorTreeWrapperPass>().getDomTree();
	std::queue<llvm::Instruction*> instructionsToDelete;

	for(llvm::BasicBlock& block: function) {
		for(llvm::Instruction& instruction: block) {
			if (SlicingPass::isToBeSliced(instruction)) {
				markNotSliced(instruction);
				if (!isa<BranchInst>(instruction)) {
					instructionsToDelete.push(&instruction);
				}
			}
		}
	}

	std::queue<llvm::Instruction*> secondTry;

	std::queue<llvm::Instruction*>* activeQueue = &instructionsToDelete;
	std::queue<llvm::Instruction*>* secondQueue = &secondTry;

	bool changed = true;
	while(changed) {
		changed = false;

		while (!activeQueue->empty()) {
			Instruction& instruction = *activeQueue->front();
			activeQueue->pop();

			DeleteVisitor visitor(this->domTree);
			bool deleted = visitor.visit(instruction);

			if (!deleted) {
				secondQueue->push(&instruction);
			} else {
				changed = true;
			}
		}

		std::set<BasicBlock*> deletedBlocks;
		for (BasicBlock& block:function){
			DeleteVisitor visitor(this->domTree);
			bool deleted = visitor.visit(block.getTerminator());
			if (deleted) {
				changed = true;
			}

			if (block.empty() && &function.getEntryBlock() != &block) {
				deletedBlocks.insert(&block);
			}
		}

		for (BasicBlock* block: deletedBlocks){
			block->eraseFromParent();
		}

		std::queue<llvm::Instruction*>* temp;
		temp = activeQueue;
		activeQueue = secondQueue;
		secondQueue = temp;
	}

	while (!activeQueue->empty()) {
		Instruction& instruction = *activeQueue->front();
		activeQueue->pop();
	}

	for(Instruction& instruction : Util::getInstructions(function)) {
		if (isNotSliced(instruction)) {
			this->hasUnSlicedInstructions_ = true;
		}
	}

	bool hasError = llvm::verifyFunction(function, &errs());
	assert(!hasError && "Internal Error: Slicing pass produced slice candidate, which ist not a valid llvm program.");

	return true;
}

void SlicingPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
	AU.addRequired<llvm::DominatorTreeWrapperPass>();
}

bool SlicingPass::hasUnSlicedInstructions(){
	return this->hasUnSlicedInstructions_;
}
