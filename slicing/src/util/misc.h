#pragma once

#include "llvm/IR/Function.h"

namespace Util {
	bool isSpecialFunction(llvm::Function& function);
}
