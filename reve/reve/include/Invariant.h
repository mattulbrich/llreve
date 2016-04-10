#pragma once

#include "Memory.h"
#include "MonoPair.h"
#include "Opts.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

enum class InvariantAttr { MAIN, PRE, NONE };

auto invariant(int StartIndex, int EndIndex, std::vector<std::string> InputArgs,
               std::vector<std::string> EndArgs, ProgramSelection SMTFor,
               std::string FunName, Memory memory,
               std::map<int, std::vector<std::string>> freeVarsMap)
    -> smt::SMTRef;
auto mainInvariant(int EndIndex, std::vector<std::string> FreeVars,
                   std::string FunName) -> smt::SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                          ProgramSelection For, std::string FunName,
                          Memory heap) -> MonoPair<smt::SMTRef>;
auto singleInvariantDeclaration(
    std::map<int, std::vector<std::string>> freeVarsMap, Memory memory,
    ProgramSelection prog, std::string funName) -> MonoPair<smt::SMTRef>;
auto mainInvariantDeclaration(int BlockIndex, std::vector<std::string> FreeVars,
                              ProgramSelection For, std::string FunName)
    -> smt::SharedSMTRef;
auto singleMainInvariant(std::map<int, std::vector<std::string>> freeVarsMap,
                         Memory memory, ProgramSelection prog)
    -> smt::SharedSMTRef;
auto invariantName(int Index, ProgramSelection For, std::string FunName,
                   InvariantAttr attr = InvariantAttr::NONE,
                   uint32_t VarArgs = 0) -> std::string;

auto invariantArgs(std::vector<std::string> freeVars, Memory memory,
                   ProgramSelection prog, InvariantAttr attr) -> size_t;
// maximum number of arguments required
auto maxArgs(std::map<int, std::vector<std::string>> freeVarsMap, Memory mem,
             ProgramSelection prog, InvariantAttr attr) -> size_t;
auto fillUpArgs(std::vector<smt::SharedSMTRef> args,
                std::map<int, std::vector<std::string>> freeVarsMap, Memory mem,
                ProgramSelection prog, InvariantAttr attr)
    -> std::vector<smt::SharedSMTRef>;
auto fillUpArgs(std::vector<std::string> args,
                std::map<int, std::vector<std::string>> freeVarsMap, Memory mem,
                ProgramSelection prog, InvariantAttr attr)
    -> std::vector<std::string>;
template <typename T>
auto fillUpArgsWithFiller(T filler, std::vector<T> args,
                          std::map<int, std::vector<std::string>> freeVarsMap,
                          Memory mem, ProgramSelection prog, InvariantAttr attr)
    -> std::vector<T> {
    if (!SMTGenerationOpts::getInstance().SingleInvariant) {
        return args;
    }
    size_t neededArgs = maxArgs(freeVarsMap, mem, prog, attr);
    for (size_t i = args.size(); i < neededArgs; ++i) {
        args.push_back(filler);
    }
    return args;
}
