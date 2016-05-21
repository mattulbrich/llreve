#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"
#include <set>



/**
 * This class analyzes debug information to provide ssa variables (instructions)
 * with information about the related src variable. Make sure to use debug flag
 * during construction of the ir. Will only work properly after mem2reg pass.
 * 
 * The following instructions get a related src variable:
 *  * instructions that have a assoziated debug information
 *  * phi instruction, which only use instructions that have the same related src variable
**/
class AddVariableNamePass : public llvm::FunctionPass {
public:
	static char ID;

	AddVariableNamePass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &Fun) override;
	static llvm::DIVariable* getSrcVariable(llvm::Instruction& instruction);

private:
	static std::string srcVariableMetadataName;

	std::set<llvm::Instruction*>* hasNoName;

	void setSrcVariable(llvm::Instruction& instruction, llvm::DIVariable* variable);
	void setAndPropagate(llvm::DIVariable* srcVariable, llvm::Instruction* instruction);
	void propagateNoVariable(llvm::Instruction* instruction);
};
