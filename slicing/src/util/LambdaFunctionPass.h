#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/DebugInfoMetadata.h"

typedef std::function<bool (llvm::Function& function)> FunctionPassLambda;

class LambdaFunctionPass : public llvm::FunctionPass {
public:
	static char ID;

	LambdaFunctionPass() : llvm::FunctionPass(ID), lambda(nullptr) {}
	LambdaFunctionPass(FunctionPassLambda lambda) : llvm::FunctionPass(ID), lambda(lambda) {}

	virtual bool runOnFunction(llvm::Function &function) override;

	static void runOnModule(llvm::Module& module, FunctionPassLambda lambda);

private:
	FunctionPassLambda lambda;

};
