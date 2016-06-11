#include "core/DeleteVisitor.h"
#include "core/Criterion.h"
#include "core/AddVariableNamePass.h"

using namespace llvm;

bool DeleteVisitor::visitInstruction(llvm::Instruction &instruction){
	DIVariable* variable = AddVariableNamePass::getSrcVariable(instruction);

	bool erased =
		   handleNoUses(instruction)
		|| handleHasPriviousDef(instruction, variable)
		|| handleIsArgument(instruction, variable);
	return erased;
}

bool DeleteVisitor::visitTerminatorInst(TerminatorInst &instruction){
	return false;
}

bool DeleteVisitor::visitCallInst(CallInst &instruction){
	if (instruction.getCalledFunction()
			&& instruction.getCalledFunction()->getName() == Criterion::CRITERION_FUNCTION_NAME) {
		return false;
	} else {
		//TODD: avoid removing call instructions, that coudl modify
		//thier parameters.
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
