#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"

class SlicingPass : public llvm::FunctionPass {
public:
	static char ID;
	SlicingPass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &Fun) override;

	static void toBeSliced(llvm::Instruction& instruction);
	static bool isToBeSliced(llvm::Instruction& instruction);
};


