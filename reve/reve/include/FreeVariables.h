#pragma once

#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

using FreeVarsMap = std::map<Mark, std::vector<smt::SortedVar>>;
auto freeVars(PathMap map, std::vector<smt::SortedVar> funArgs, Program prog)
    -> FreeVarsMap;
auto addMemoryArrays(std::vector<smt::SortedVar> vars, Program prog)
    -> std::vector<smt::SortedVar>;
