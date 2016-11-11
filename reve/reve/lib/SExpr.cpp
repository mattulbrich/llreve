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

#include <string>

using namespace sexpr;

using std::make_unique;
using std::string;

void Value::serialize(std::ostream &os, size_t /* unused */,
                      bool /* unused */) const {
    os << val;
}

void Apply::serialize(std::ostream &os, size_t indent, bool pretty) const {
    os << "(" << fun;
    if (pretty) {
        bool atomicOp = atomicOps.find(fun) != atomicOps.end();
        bool simpleOp = args.size() <= 1 &&
                        forceIndentOps.find(fun) == forceIndentOps.end();
        bool inv = fun.substr(0, 3) == "INV" || fun == "OUT_INV" ||
                   fun == "IN_INV" || fun == "INIT";
        if (atomicOp || simpleOp || inv) {
            for (auto &arg : args) {
                os << " ";
                arg->serialize(os, indent + fun.size() + 3, pretty);
            }
        } else {
            for (auto &arg : args) {
                os << "\n";
                os << std::string(indent + 3, ' ');
                arg->serialize(os, indent + 3, pretty);
            }
        }
    } else {
        for (auto &arg : args) {
            os << ' ';
            arg->serialize(os, indent + 3, pretty);
        }
    }
    os << ")";
}

void List::serialize(std::ostream &os, size_t indent, bool pretty) const {
    os << "(";
    auto it = elements.begin();
    auto e = elements.end();
    if (it != e) {
        (*it)->serialize(os, indent + 1, pretty);
        ++it;
        for (; it != e; ++it) {
            os << "\n";
            os << std::string(indent + 1, ' ');
            (*it)->serialize(os, indent + 1, pretty);
        }
    }
    os << ")";
}

void Comment::serialize(std::ostream &os, size_t /* unused */,
                        bool /* unused */) const {
    os << "; " << val;
}

const llvm::StringSet<> Apply::forceIndentOps = {"assert", "and", "rule"};
const llvm::StringSet<> Apply::atomicOps = {
    "+",      "-",      "*",       "<=",       "<",      ">",
    ">=",     "=",      "not",     "distinct", "select", "ite",
    "div",    "_",      "bvadd",   "bvsub",    "bvmul",  "store",
    "store_", "select", "select_", "Array"};

SExprRef sexprFromString(string value) { return make_unique<Value>(value); }

std::ostream &sexpr::operator<<(std::ostream &os, const SExpr &val) {
    val.serialize(os, 0, true);
    return os;
}
