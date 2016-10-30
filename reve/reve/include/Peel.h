#pragma once

#include "MarkAnalysis.h"

void peelAtMark(llvm::Function &f, Mark mark, const BidirBlockMarkMap &marks,
                std::string prefix);
