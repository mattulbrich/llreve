#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Function.h"

#include <unordered_map>

class ExplicitAssignPass : public llvm::ModulePass {
public:
	static char ID;
	static std::string FUNCTION_NAME;

	ExplicitAssignPass() : llvm::ModulePass(ID) {}
	virtual bool runOnModule(llvm::Module &module) override;

private:
	llvm::Function& getID(llvm::Type& type, llvm::Module& module);
	std::unordered_map<llvm::FunctionType*, llvm::Function*> idFunctionMap_;
	bool noDublicateAssignment(llvm::Value* value);
};
