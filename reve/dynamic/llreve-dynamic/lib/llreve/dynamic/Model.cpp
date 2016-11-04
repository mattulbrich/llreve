/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Model.h"

#include "Helper.h"

#include <cassert>

using std::set;
using std::string;

TopLevelExpr::~TopLevelExpr() = default;
SMTExpr::~SMTExpr() = default;
mpz_class SMTExpr::getVal() const {
    logError("Trying to get an integer out of an arbitrary smtexpr\n");
    exit(1);
}

ArrayVal SMTExpr::getArrayVal() const { return {}; }
mpz_class SMTExpr::getIndex() const {
    logError("Can’t get exit ouf of smtexpr\n");
    exit(1);
}

set<string> DefineFun::references() const {
    set<string> defRefs = definition->references();
    for (const auto &arg : argTypes) {
        defRefs.erase(arg.first);
    }
    return defRefs;
}

string DefineFun::getName() const { return name; }

Type DefineFun::type() const {
    if (returnType == Type::IntArray) {
        assert(argTypes.empty());
        return Type::IntArray;
    } else {
        if (argTypes.empty()) {
            return Type::Int;
        } else {
            assert(argTypes.size() == 1);
            return Type::IntFun;
        }
    }
}

mpz_class DefineFun::getVal() const { return definition->getVal(); }
ArrayVal DefineFun::getArrayVal() const { return definition->getArrayVal(); }

set<string> AsArray::references() const { return {arg}; }

set<string> String::references() const { return {}; }

set<string> Int::references() const { return {}; }

mpz_class Int::getVal() const { return val; }
ArrayVal Int::getArrayVal() const { return {val, {}}; }

set<string> Eq::references() const {
    set<string> leftRefs = left->references();
    set<string> rightRefs = right->references();
    leftRefs.insert(rightRefs.begin(), rightRefs.end());
    return leftRefs;
}

mpz_class Eq::getIndex() const { return right->getVal(); }

set<string> ITE::references() const {
    set<string> condRefs = cond->references();
    set<string> trueRefs = ifTrue->references();
    set<string> falseRefs = ifFalse->references();
    condRefs.insert(trueRefs.begin(), trueRefs.end());
    condRefs.insert(falseRefs.begin(), falseRefs.end());
    return condRefs;
}

ArrayVal ITE::getArrayVal() const {
    mpz_class i = cond->getIndex();
    mpz_class val = ifTrue->getVal();
    ArrayVal acc = ifFalse->getArrayVal();
    acc.vals.insert({i, val});
    return acc;
}

set<string> Identifier::references() const { return {name}; }

ModelValues parseValues(Model model) {
    ModelValues modelValues;
    std::map<std::string, ArrayVal> functions;
    for (const auto &expr : model.exprs) {
        if (expr->type() == Type::Int) {
            modelValues.values.insert({expr->getName(), expr->getVal()});
        } else if (expr->type() == Type::IntFun) {
            functions.insert({expr->getName(), expr->getArrayVal()});
        }
    }
    for (const auto &expr : model.exprs) {
        if (expr->type() == Type::IntArray) {
            assert(expr->references().size() == 1);
            modelValues.arrays.insert(
                {expr->getName(), functions.at(*expr->references().begin())});
        }
    }
    return modelValues;
}

Result::~Result() = default;

bool Unsat::isSat() const { return false; }

bool Sat::isSat() const { return true; }
