#include "LambdaFunctionPass.h"

char LambdaFunctionPass::ID = 0;

bool LambdaFunctionPass::runOnFunction(llvm::Function &function) {
	if (lambda) {
		return lambda(function);
	}
	return false;
}
