/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/HeapPattern.h"

namespace llreve {
namespace dynamic {
template <>
mpz_class
Variable<const llvm::Value *>::eval(const FastVarMap &variables,
                                    const MonoPair<Heap> & /* unused */,
                                    const HoleMap & /* unused */) const {
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
    if (varName->getName().empty()) {
        // In this case we have a return instruction that’s either in program 1
        // or program 2.
        // To figure out in which one we are we use a really hacky workaround
        // based on the block name
        auto retInst = llvm::dyn_cast<llvm::ReturnInst>(varName);
        assert(retInst);
        char program = retInst->getParent()->getName().back();
        if (program == '1') {
            return smt::stringExpr(resultName(Program::First));
        } else {
            assert(program == '2');
            return smt::stringExpr(resultName(Program::Second));
        }
    }
    return smt::stringExpr(varName->getName());
}
}
}
