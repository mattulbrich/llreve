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
                  SerializeOpts opts);
