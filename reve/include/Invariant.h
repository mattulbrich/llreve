#pragma once

#include "Memory.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

auto invariant(int StartIndex, int EndIndex, std::vector<std::string> InputArgs,
               std::vector<std::string> EndArgs, ProgramSelection SMTFor,
               std::string FunName, Memory Heap) -> SMTRef;
auto mainInvariant(int EndIndex, std::vector<string> FreeVars, string FunName,
                   Memory Heap) -> SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                          ProgramSelection For, std::string FunName,
                          Memory Heap) -> std::pair<SMTRef, SMTRef>;
auto mainInvariantDeclaration(int BlockIndex, std::vector<string> FreeVars,
                              ProgramSelection For, std::string FunName)
    -> SMTRef;
auto invariantName(int Index, ProgramSelection For, std::string FunName,
                   uint32_t VarArgs = 0) -> std::string;
