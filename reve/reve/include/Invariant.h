/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "FreeVariables.h"
#include "Memory.h"
#include "MonoPair.h"
#include "Opts.h"
#include "PathAnalysis.h"
#include "Program.h"
#include "SMT.h"

enum class InvariantAttr { MAIN, PRE, NONE };

auto functionalCouplingPredicate(Mark StartIndex, Mark EndIndex,
                                 std::vector<smt::SortedVar> InputArgs,
                                 std::vector<smt::SortedVar> EndArgs,
                                 ProgramSelection SMTFor, std::string FunName,
                                 FreeVarsMap freeVarsMap) -> smt::SMTRef;
auto iterativeCouplingPredicate(Mark EndIndex,
                                std::vector<smt::SortedVar> FreeVars,
                                std::string FunName) -> smt::SMTRef;
auto invariantDeclaration(Mark BlockIndex, std::vector<smt::SortedVar> FreeVars,
                          ProgramSelection For, std::string FunName,
                          const llvm::Type *resultType)
    -> MonoPair<smt::SMTRef>;
auto mainInvariantComment(Mark blockIndex,
                          const std::vector<smt::SortedVar> &freeVars,
                          ProgramSelection selection, std::string funName)
    -> smt::SMTRef;
auto mainInvariantDeclaration(Mark BlockIndex,
                              std::vector<smt::SortedVar> FreeVars,
                              ProgramSelection For, std::string FunName)
    -> smt::SMTRef;
auto invariantName(Mark Index, ProgramSelection For, std::string FunName,
                   InvariantAttr attr = InvariantAttr::NONE,
                   uint32_t VarArgs = 0) -> std::string;

auto invariantArgs(std::vector<smt::SortedVar> freeVars, ProgramSelection prog,
                   InvariantAttr attr) -> size_t;
