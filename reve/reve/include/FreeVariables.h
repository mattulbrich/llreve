#pragma once

#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

#include "llvm/IR/BasicBlock.h"

auto freeVars(PathMap map1, PathMap map2,
              MonoPair<std::vector<smt::SortedVar>> funArgs)
    -> smt::FreeVarsMap;
auto freeVars(PathMap map, std::vector<smt::SortedVar> funArgs, Program prog)
    -> smt::FreeVarsMap;
