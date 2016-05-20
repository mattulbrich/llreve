#include "SlicingPass.h"
#include "AddVariableNamePass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "llvm/IR/Dominators.h"

#include <set>
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

bool SlicingPass::isPriviousDef(const DIVariable* variable, Instruction& instruction) {
	return variable == AddVariableNamePass::getSrcVariable(instruction);
}

Instruction* SlicingPass::findPriviousDef(const DIVariable* variable, Instruction& instruction) {	
	BasicBlock* parent = instruction.getParent();
	if (!parent) {
		return nullptr;
	}
	
	auto treeNode = this->domTree->getNode(parent);

	Instruction* result = nullptr;
	while (!result && treeNode) {
		BasicBlock* block = treeNode->getBlock();
		for (Instruction& instructionInBlock: *block) {
			if (this->isPriviousDef(variable, instructionInBlock)) {
				// double check, as we might still be in the same block.
				if (this->domTree->dominates(&instructionInBlock, &instruction)) {
					result = &instructionInBlock;
				}
			}
		}
		treeNode = treeNode->getIDom();
	}

	return result;
}

bool SlicingPass::runOnFunction(llvm::Function& function){
	this->domTree = &getAnalysis<llvm::DominatorTreeWrapperPass>().getDomTree();
	std::set<llvm::Instruction*> instructionsToDelete;

	for(llvm::BasicBlock& block: function) {
		for(llvm::Instruction& instruction: block) {
			if (SlicingPass::isToBeSliced(instruction)) {
				instructionsToDelete.insert(&instruction);
			}
		}
	}

	for(llvm::Instruction* ins: instructionsToDelete) {
		Instruction& instruction = *ins;
		llvm::outs() << "Looking for Privious def of: " << instruction << '\n';

		//if (!instruction.hasNUsesOrMore(1)) {
		//	instruction.eraseFromParent();
		//} else 
		{
			if (DIVariable* variable = AddVariableNamePass::getSrcVariable(instruction)){
				Instruction* priviousDef = this->findPriviousDef(variable,instruction);
				if (priviousDef) {
					llvm::outs() << "Found: " << *priviousDef << '\n';
				}
			}
		}
		
	}

	return true;
}

void SlicingPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
	AU.addRequired<llvm::DominatorTreeWrapperPass>();
}
