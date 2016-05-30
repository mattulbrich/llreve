#pragma once

#include "Memory.h"
#include "MonoPair.h"
#include "Opts.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

enum class InvariantAttr { MAIN, PRE, NONE };

auto invariant(int StartIndex, int EndIndex,
               std::vector<smt::SortedVar> InputArgs,
               std::vector<smt::SortedVar> EndArgs, ProgramSelection SMTFor,
               std::string FunName, Memory memory, smt::FreeVarsMap freeVarsMap)
    -> smt::SMTRef;
auto mainInvariant(int EndIndex, std::vector<smt::SortedVar> FreeVars,
                   std::string FunName) -> smt::SMTRef;
auto invariantDeclaration(int BlockIndex, std::vector<smt::SortedVar> FreeVars,
                          ProgramSelection For, std::string FunName,
                          Memory heap, const llvm::Type *resultType)
    -> MonoPair<smt::SMTRef>;
auto singleInvariantDeclaration(smt::FreeVarsMap freeVarsMap, Memory memory,
                                ProgramSelection prog, std::string funName)
    -> MonoPair<smt::SMTRef>;
auto mainInvariantDeclaration(int BlockIndex,
                              std::vector<smt::SortedVar> FreeVars,
                              ProgramSelection For, std::string FunName)
    -> smt::SharedSMTRef;
auto singleMainInvariant(smt::FreeVarsMap freeVarsMap, Memory memory,
                         ProgramSelection prog) -> smt::SharedSMTRef;
auto invariantName(int Index, ProgramSelection For, std::string FunName,
                   InvariantAttr attr = InvariantAttr::NONE,
                   uint32_t VarArgs = 0) -> std::string;

auto invariantArgs(std::vector<smt::SortedVar> freeVars, Memory memory,
                   ProgramSelection prog, InvariantAttr attr) -> size_t;
// maximum number of arguments required
auto maxArgs(smt::FreeVarsMap freeVarsMap, Memory mem, ProgramSelection prog,
             InvariantAttr attr) -> size_t;
auto fillUpArgs(std::vector<smt::SharedSMTRef> args,
                smt::FreeVarsMap freeVarsMap, Memory mem, ProgramSelection prog,
                InvariantAttr attr) -> std::vector<smt::SharedSMTRef>;
auto fillUpArgs(std::vector<std::string> args, smt::FreeVarsMap freeVarsMap,
                Memory mem, ProgramSelection prog, InvariantAttr attr)
    -> std::vector<std::string>;
template <typename T>
auto fillUpArgsWithFiller(T filler, std::vector<T> args,
                          smt::FreeVarsMap freeVarsMap, Memory mem,
                          ProgramSelection prog, InvariantAttr attr)
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
