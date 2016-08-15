#include "ReplaceUndefPass.h"

#include "core/Util.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constant.h"

using namespace llvm;

char ReplaceUndefPass::ID = 0;

bool ReplaceUndefPass::runOnFunction(llvm::Function &function){
		for (Instruction& instruction : Util::getInstructions(function)) {
			for (Use& use:instruction.operands()) {
				if (isa<UndefValue>(use)){
					use->replaceAllUsesWith(Constant::getNullValue(use->getType()));
				}
			}
		}
	return true;
}
