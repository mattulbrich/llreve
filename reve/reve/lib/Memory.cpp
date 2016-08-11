/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Memory.h"
#include "Opts.h"

using std::vector;
using std::make_shared;
using std::string;
using smt::SharedSMTRef;
using smt::SortedVar;
using smt::Forall;
