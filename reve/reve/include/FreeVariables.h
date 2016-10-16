#pragma once

#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

using FreeVarsMap = std::map<int, std::vector<smt::SortedVar>>;
auto freeVars(PathMap map, std::vector<smt::SortedVar> funArgs, Program prog)
    -> FreeVarsMap;
