/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "HeapPattern.h"

template <>
mpz_class Variable<const llvm::Value *>::eval(
    const VarMap<const llvm::Value *> &variables,
    const MonoPair<Heap> & /* unused */, const HoleMap & /* unused */) const {
    return unsafeIntValRef(variables.at(varName)).asUnbounded();
}

template <>
std::ostream &Variable<const llvm::Value *>::dump(std::ostream &os) const {
    std::string name = varName->getName();
    os << name;
    return os;
}

mpz_class getHeapVal(HeapAddress addr, Heap heap) {
    auto it = heap.find(addr);
    if (it != heap.end()) {
        return it->second.asUnbounded();
    } else {
        return 0;
    }
}

template <> smt::SMTRef Variable<const llvm::Value *>::toSMT() const {
    return smt::stringExpr(varName->getName());
}
