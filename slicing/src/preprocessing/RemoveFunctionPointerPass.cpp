#include "RemoveFunctionPointerPass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"

#include "util/logging.h"

char RemoveFunctionPointerPass::ID = 0;

bool RemoveFunctionPointerPass::runOnFunction(llvm::Function &function) {
	bool changed = false;
	std::vector<llvm::Value*> toReplace;
	for (llvm::BasicBlock& block: function) {
		for (llvm::Instruction& instruction: block) {
			if (llvm::CallInst* callInst = llvm::dyn_cast<llvm::CallInst>(&instruction)) {
				for (unsigned i =0; i < callInst->getNumArgOperands();++i) {
					llvm::Value* arg = callInst->getArgOperand(i);
					if (llvm::isa<llvm::Function>(arg)){
						toReplace.push_back(callInst);
						Log(Warning) << "Found function Pointer as parameter in Function call. Function pointer are not supported, the called function was replaced with undef.";
					}
				}
			}
		}
	}

	for (llvm::Value* value:toReplace) {
		llvm::UndefValue* undef = llvm::UndefValue::get(value->getType());
		value->replaceAllUsesWith(undef);
		if (llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(value)){
			inst->eraseFromParent();
		}
		changed = true;
	}

	return changed;
}
