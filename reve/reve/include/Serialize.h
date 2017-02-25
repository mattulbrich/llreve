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

#include "Opts.h"
#include "SMT.h"

void serializeSMT(std::vector<smt::SharedSMTRef> smtExprs, bool muZ,
                  llreve::opts::SerializeOpts opts);

// Remove forall and collect quantified variables. These variables are then
// declared as global variables for Z3.
std::shared_ptr<smt::SMTExpr>
removeForalls(smt::SMTExpr &expr,
              std::set<smt::SortedVar> &introducedVariables);
