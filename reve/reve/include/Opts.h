#pragma once

#include "llvm/Support/CommandLine.h"

extern llvm::cl::OptionCategory ReveCategory;

// Opts for SMT generation
extern std::string MainFunction;
extern bool Heap;
extern bool Stack;
extern bool GlobalConstants;
extern bool OnlyRecursive;
extern bool NoByteHeapFlag;
extern bool EverythingSignedFlag;
extern bool SingleInvariantFlag;
extern bool MuZFlag;
extern bool PerfectSyncFlag;
extern bool NestFlag;
extern bool PassInputThroughFlag;

// Opts for preprocessing
extern bool ShowCFG;
extern bool ShowMarkedCFG;
