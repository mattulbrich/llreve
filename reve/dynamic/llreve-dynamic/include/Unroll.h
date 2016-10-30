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

#include "MarkAnalysis.h"

#include "llvm/Analysis/LoopInfo.h"

void unrollAtMark(llvm::Function &f, Mark mark, const BidirBlockMarkMap &marks,
                  size_t factor);
