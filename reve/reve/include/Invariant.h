#pragma once

#include "Memory.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

auto invariant(int StartIndex, int EndIndex, std::vector<std::string> InputArgs,
               std::vector<std::string> EndArgs, ProgramSelection SMTFor,
               std::string FunName, Memory memory) -> smt::SMTRef;
auto mainInvariant(int EndIndex, std::vector<std::string> FreeVars,
                   std::string FunName, Memory memory) -> smt::SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                          ProgramSelection For, std::string FunName,
                          Memory heap) -> MonoPair<smt::SMTRef>;
auto mainInvariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                              ProgramSelection For, std::string FunName)
    -> smt::SMTRef;
auto invariantName(int Index, ProgramSelection For, std::string FunName,
                   std::string Suffix = "", uint32_t VarArgs = 0)
    -> std::string;
auto singleInvariant(std::map<int, std::vector<std::string>> freeVarsMap,
                     Memory memory, ProgramSelection prog) -> smt::SMTRef;
auto invariantArgs(std::vector<std::string> freeVars, Memory memory,
                   ProgramSelection prog, bool main) -> size_t;
