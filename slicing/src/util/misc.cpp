#include "misc.h"

#include "core/PromoteAssertSlicedPass.h"
#include "core/ExplicitAssignPass.h"
#include "core/Criterion.h"

using namespace llvm;

bool Util::isSpecialFunction(Function& function){
	return function.getName() == Criterion::FUNCTION_NAME
			|| function.getName() == "__mark"
			|| function.getName() == PromoteAssertSlicedPass::FUNCTION_NAME
			|| function.getName() == ExplicitAssignPass::FUNCTION_NAME;
}
