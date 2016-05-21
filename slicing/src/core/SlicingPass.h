#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/DebugInfoMetadata.h"



class SlicingPass : public llvm::FunctionPass {
public:
	static char ID;

	SlicingPass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &Fun) override;
	virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;


	static void toBeSliced(llvm::Instruction& instruction);
	static bool isToBeSliced(llvm::Instruction& instruction);

private:
	llvm::DominatorTree* domTree;

	bool isPriviousDef(const llvm::DIVariable* variable, llvm::Instruction& instruction);
	llvm::Instruction* findPriviousDef(const llvm::DIVariable* variable, llvm::Instruction& instruction);

	bool handleTerminatingInstruction(llvm::Instruction& instruction);
	bool handleNoUses(llvm::Instruction& instruction);
	bool handleHasPriviousDef(llvm::Instruction& instruction, llvm::DIVariable* variable);
	bool handleIsArgument(llvm::Instruction& instruction, llvm::DIVariable* variable);

};

