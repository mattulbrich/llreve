/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */
#include "SExpr.h"

using namespace sexpr;

using std::make_unique;
using std::string;

SExprRef sexprFromString(string value) {
    return make_unique<Value<string>>(value);
}
