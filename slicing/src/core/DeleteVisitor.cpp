#include "core/DeleteVisitor.h"
#include "core/Criterion.h"
#include "preprocessing/AddVariableNamePass.h"
#include "util/FileOperations.h"

#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"


#include <iostream>

using namespace llvm;
using namespace std;

bool DeleteVisitor::visitInstruction(llvm::Instruction &instruction){
	DIVariable* variable = AddVariableNamePass::getSrcVariable(instruction);

	bool erased =
	handleNoUses(instruction)
	|| handleHasPriviousDef(instruction, variable)
	|| handleIsArgument(instruction, variable)
	|| handleSinglePhiUse(instruction);
	return erased;
}

bool DeleteVisitor::visitTerminatorInst(TerminatorInst &instruction){
	return false;
}

bool DeleteVisitor::visitCallInst(CallInst &instruction){
	if (instruction.getCalledFunction()
		&& instruction.getCalledFunction()->getName() == Criterion::FUNCTION_NAME) {
		return false;
} else {
		//TODD: avoid removing call instructions, that coudl modify
		//thier parameters.
	return visitInstruction(instruction);
}
}

bool DeleteVisitor::visitBranchInst (BranchInst &instruction){
	unsigned instructionCount = 0;
	BasicBlock& instructionBlock = *instruction.getParent();

	for (Instruction& i :instructionBlock){
		instructionCount++;
	}

	if (instruction.isUnconditional() && instructionCount == 1) {
		BasicBlock* successor = instruction.getSuccessor(0);
		Function& function = *instructionBlock.getParent();
		bool canRemoveFromAllUsers = true;
		if (&function.getEntryBlock() == successor
			|| &function.getEntryBlock() == &instructionBlock) {
			// Entry blocks may have no predecessor
			// therefore no block can have the entry block as successor
			// And the entry block should not be deleted
			canRemoveFromAllUsers = false;
		}

		for (User* user:instructionBlock.users()) {
			if (!isa<BranchInst>(user)) {
				canRemoveFromAllUsers = false;
			}
		}

		for (Instruction& instructionInSuccessor:*successor) {
			if (PHINode* phi = dyn_cast<PHINode>(&instructionInSuccessor)) {
				for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
					BasicBlock* block = phi->getIncomingBlock(i);
					if (block == &instructionBlock) {
						canRemoveFromAllUsers = false;
					}
				}
			}
		}

		if (canRemoveFromAllUsers) {
			set<User*> users;
			for (User* user:instructionBlock.users()) {
				users.insert(user);
			}

			for (User* user:users) {
				if (BranchInst* userBranch = dyn_cast<BranchInst>(user)) {
					for (unsigned i = 0; i < userBranch->getNumSuccessors(); ++i) {
						if (userBranch->getSuccessor(i) == &instructionBlock) {
							userBranch->setSuccessor(i, successor);
						}
					}

					if (userBranch->isConditional()) {
						bool allSuccessorsSame = true; // and succssor
						for (unsigned i = 0; i < userBranch->getNumSuccessors(); ++i) {
							if (userBranch->getSuccessor(i) != successor) {
								allSuccessorsSame = false;
							}
						}

						if (allSuccessorsSame) {
							BasicBlock* userBlock = userBranch->getParent();
							BranchInst::Create(successor, userBlock);
							//IRBuilder<> Builder(userBranch);
							//Builder.CreateBr(successor);
							userBranch->eraseFromParent();
						}
					}
				}
			}

			instruction.eraseFromParent();

			assert(instructionBlock.hasNUses(0));
			//instructionBlock.eraseFromParent();


			return true;
		}
	}

	return visitTerminatorInst(instruction);
}

bool DeleteVisitor::visitPHINode(llvm::PHINode &instruction) {
	// Phi nodes may contain inlined constants and arguments from privious blocks.
	// A call to delete a phi node will try to resolve such inlining first.
	// This is possible if all other incoming values are
	// dominating the phi node.
	// Usually we have only two incoming values. In other cases
	// there might be further optimisation potential.

	unsigned dominatingCount = 0;
	BasicBlock* notDominatingBlock = nullptr;
	for (unsigned i = 0; i < instruction.getNumIncomingValues(); i++) {
		BasicBlock* block = instruction.getIncomingBlock(i);

		if (this->domTree_->dominates(block,instruction.getParent())) {
			++dominatingCount;
		} else {
			notDominatingBlock = block;
		}
	}

	if (dominatingCount == instruction.getNumIncomingValues() - 1) {
		instruction.removeIncomingValue(notDominatingBlock);
	}

	if (instruction.getNumIncomingValues() == 1) {
		instruction.replaceAllUsesWith(instruction.getIncomingValue(0));
		instruction.eraseFromParent();
		return true;
	} else {
		return visitInstruction(instruction);
	}
}

bool DeleteVisitor::isPriviousDef(const DIVariable* variable, Instruction& instruction) {
	return variable == AddVariableNamePass::getSrcVariable(instruction);
}

Instruction* DeleteVisitor::findPriviousDef(const DIVariable* variable, Instruction& instruction) {
	BasicBlock* parent = instruction.getParent();
	if (!parent) {
		return nullptr;
	}

	auto treeNode = this->domTree_->getNode(parent);

	Instruction* result = nullptr;
	while (!result && treeNode) {
		BasicBlock* block = treeNode->getBlock();
		for (Instruction& instructionInBlock: *block) {
			if (this->isPriviousDef(variable, instructionInBlock)) {
				// double check, as we might still be in the same block.
				if (this->domTree_->dominates(&instructionInBlock, &instruction)) {
					result = &instructionInBlock;
				}
			}
		}
		treeNode = treeNode->getIDom();
	}

	return result;
}

bool DeleteVisitor::handleSinglePhiUse(llvm::Instruction& instruction){
	// If instruction is only used within a phi node and that
	// phi node has another value, which can be used insted of instruction
	// value, than we can use this and remove instruction.

	if (instruction.hasNUses(1)) {
		if (PHINode* phi = dyn_cast<PHINode>(*instruction.uses().begin())) {
			bool hasDominating = false;
			for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
				BasicBlock* block = phi->getIncomingBlock(i);

				if (this->domTree_->dominates(block,phi->getParent())) {
					hasDominating = true;
				}
			}

			if (hasDominating) {
				phi->removeIncomingValue(instruction.getParent());
				instruction.eraseFromParent();

				if (phi->getNumIncomingValues() == 1) {
					phi->replaceAllUsesWith(phi->getIncomingValue(0));
					phi->eraseFromParent();
				}

				return true;
			}
		}
	}
	return false;
}


bool DeleteVisitor::handleNoUses(llvm::Instruction& instruction){
	if (!instruction.hasNUsesOrMore(1)) {
		instruction.eraseFromParent();
		return true;
	}
	return false;
}

bool DeleteVisitor::handleHasPriviousDef(llvm::Instruction& instruction, DIVariable* variable) {
	if (variable){
		Instruction* priviousDef = this->findPriviousDef(variable,instruction);
		if (priviousDef) {
			instruction.replaceAllUsesWith(priviousDef);
			instruction.eraseFromParent();
			return true;
		}
	}
	return false;
}

bool DeleteVisitor::handleIsArgument(llvm::Instruction& instruction, DIVariable* variable){
	if (variable){
		if (DILocalVariable* localVariable = dyn_cast<DILocalVariable>(variable)) {
			if (localVariable->isParameter()) {
				Function* function = instruction.getFunction();
				if (function) {
					unsigned arg = localVariable->getArg();
					unsigned i = 1;
					Argument* searchedArgument = nullptr;

					for (Argument& argument : function->getArgumentList()) {
						if (arg == i) {
							searchedArgument = &argument;
							break;
						}
						i++;
					}

					if (searchedArgument) {
						instruction.replaceAllUsesWith(searchedArgument);
						instruction.eraseFromParent();
						return true;
					}
				}
			}
		}
	}

	return false;
}
