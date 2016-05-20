#include "SlicingPass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"

#include <set>

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
	std::set<llvm::Instruction*> instructionsToDelete;

	for(llvm::BasicBlock& block: function) {
		for(llvm::Instruction& instruction: block) {
			if (SlicingPass::isToBeSliced(instruction)) {
				instructionsToDelete.insert(&instruction);
			}
		}
	}

	for(llvm::Instruction* instruction: instructionsToDelete) {
		instruction->eraseFromParent();
	}

	return true;
}
