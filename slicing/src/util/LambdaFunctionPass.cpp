#include "LambdaFunctionPass.h"

char LambdaFunctionPass::ID = 0;

bool LambdaFunctionPass::runOnFunction(llvm::Function &function) {
	if (lambda) {
		return lambda(function);
	}
	return false;
}

void LambdaFunctionPass::runOnModule(llvm::Module& module, FunctionPassLambda lambda){
	llvm::legacy::PassManager PM;
	PM.add(new LambdaFunctionPass(lambda));
	PM.run(module);
}

char LambdaModulePass::ID = 0;

bool LambdaModulePass::runOnModule(llvm::Module &module) {
	if (lambda) {
		return lambda(module);
	}
	return false;
}
