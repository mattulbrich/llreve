/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Serialize.h"

#include <llvm/ADT/StringMap.h>

#include <fstream>
#include <iostream>

using smt::SharedSMTRef;
using smt::SortedVar;
using smt::VarDecl;
using std::vector;
using smt::Forall;
using smt::Op;
using std::set;
using std::shared_ptr;

using namespace llreve::opts;

// Rename variables to a more readable form. This is only done to make the
// resulting SMT easier to read and has no effect
static llvm::StringMap<std::string>
simplifyVariableNames(const std::set<SortedVar> &variables, bool inlineLets) {
    llvm::StringMap<std::string> variableNameMap;
    for (const auto &var : variables) {
        variableNameMap.insert({var.name, var.name});
    }
    if (!inlineLets) {
        // The following transformations assume that 'variables' contains all
        // variables in an expression. This is not the case if lets have not
        // been inlined.
        return variableNameMap;
    }
    for (auto &var : variableNameMap) {
        // Strip "_old" suffix from variable name if such a variable does not
        // already exist
        if (var.getValue().size() > 4) {
            if (var.getValue().compare(var.getValue().size() - 4, 4, "_old") ==
                0) {
                std::string shortName =
                    var.getValue().substr(0, var.getValue().size() - 4);
                if (variableNameMap.find(shortName) == variableNameMap.end()) {
                    var.getValue() = shortName;
                }
            }
        }
    }
    return variableNameMap;
}

struct VariableRenamer : smt::SMTVisitor {
    const llvm::StringMap<std::string> &variableNameMap;
    VariableRenamer(const llvm::StringMap<std::string> &variableNameMap)
        : variableNameMap(variableNameMap) {}
    void dispatch(smt::TypedVariable &var) override {
        auto foundIt = variableNameMap.find(var.name);
        if (foundIt != variableNameMap.end()) {
            var.name = foundIt->second;
        }
    }
};

static void renameVariables(smt::SMTExpr &expr,
                            llvm::StringMap<std::string> variableNameMap) {
    VariableRenamer renamer{variableNameMap};
    expr.accept(renamer);
}

struct AssignmentRenameVisitor : smt::SMTVisitor {
    llvm::StringMap<unsigned> variableMap;
    void dispatch(smt::TypedVariable &var) override {
        auto foundIt = variableMap.find(var.name);
        if (foundIt != variableMap.end()) {
            var.name += "_" + std::to_string(foundIt->getValue());
        }
    }
    // There are still some places left where we use ConstantString instead of
    // TypedVariable so we need rename those as well.
    void dispatch(smt::ConstantString &str) override {
        auto foundIt = variableMap.find(str.value);
        if (foundIt != variableMap.end()) {
            str.value += "_" + std::to_string(foundIt->getValue());
        }
    }

    void dispatch(smt::Let &let) override {
        for (auto &assignment : let.defs) {
            int newIndex = ++variableMap[assignment.first];
            assignment.first += "_" + std::to_string(newIndex);
        }
    }
    void dispatch(Forall &forall) override {
        for (auto &var : forall.vars) {
            int newIndex = ++variableMap[var.name];
            var.name += "_" + std::to_string(newIndex);
        }
    }
};

// Rename assignments to unique names. This allows moving things around as
// done by mergeImplications.
static shared_ptr<smt::SMTExpr> renameAssignments(smt::SMTExpr &expr) {
    AssignmentRenameVisitor visitor;
    return expr.accept(visitor);
};

struct RemoveForallVisitor : smt::SMTVisitor {
    std::set<SortedVar> &introducedVariables;
    RemoveForallVisitor(std::set<SortedVar> &introducedVariables)
        : introducedVariables(introducedVariables) {}
    shared_ptr<smt::SMTExpr> reassemble(Forall &forall) override {
        for (const auto &var : forall.vars) {
            introducedVariables.insert(var);
        }
        return forall.expr;
    }
};

shared_ptr<smt::SMTExpr>
removeForalls(smt::SMTExpr &expr, std::set<SortedVar> &introducedVariables) {
    RemoveForallVisitor visitor{introducedVariables};
    return expr.accept(visitor);
}

struct CompressLetVisitor : smt::SMTVisitor {
    std::vector<smt::Assignment> defs;
    std::map<smt::SMTExpr *, std::vector<smt::Assignment>> storedDefs;
    CompressLetVisitor() : smt::SMTVisitor(true) {}
    void dispatch(Forall &forall) override {
        storedDefs.insert({&forall, defs});
        defs.clear();
    }
    shared_ptr<smt::SMTExpr> reassemble(Forall &forall) override {
        defs.clear();
        return nestLets(forall.shared_from_this(), storedDefs.at(&forall));
    }
    void dispatch(smt::Let &let) override {
        defs.insert(defs.end(), let.defs.begin(), let.defs.end());
    }
    shared_ptr<smt::SMTExpr> reassemble(smt::Let &let) override {
        return let.expr;
    }
    void dispatch(Op &op) override {
        storedDefs.insert({&op, defs});
        defs.clear();
    }
    shared_ptr<smt::SMTExpr> reassemble(Op &op) override {
        auto ret = nestLets(op.shared_from_this(), storedDefs.at(&op));
        defs.clear();
        return ret;
    }
    shared_ptr<smt::SMTExpr> reassemble(smt::ConstantString &str) override {
        auto ret = nestLets(str.shared_from_this(), defs);
        defs.clear();
        return ret;
    }
    shared_ptr<smt::SMTExpr> reassemble(smt::ConstantBool &cbool) override {
        auto ret = nestLets(cbool.shared_from_this(), defs);
        defs.clear();
        return ret;
    }
};

static shared_ptr<smt::SMTExpr> compressLets(smt::SMTExpr &expr) {
    CompressLetVisitor visitor;
    return expr.accept(visitor);
}

struct InstantiateArraysVisitor : smt::SMTVisitor {
    InstantiateArraysVisitor() : smt::SMTVisitor(true) {}
    shared_ptr<smt::SMTExpr> reassemble(Op &op) {
        if (op.opName.compare(0, 4, "INV_") == 0 || op.opName == "INIT") {
            std::vector<SortedVar> indices;
            std::vector<SharedSMTRef> newArgs;
            for (const auto &arg : op.args) {
                if (auto array = arg->heapInfo()) {
                    if (op.instantiate) {
                        std::string index = "i" + array->index + array->suffix;
                        newArgs.push_back(smt::stringExpr(index));
                        newArgs.push_back(
                            makeOp("select", arg, smt::stringExpr(index)));
                        indices.push_back({index, smt::pointerType()});
                    } else {
                        newArgs.push_back(arg);
                    }
                } else {
                    newArgs.push_back(arg);
                }
            }
            return std::make_shared<Forall>(
                indices, std::make_shared<Op>(op.opName, newArgs));
        }
        if (op.opName == "=" && op.args.size() == 2 &&
            op.args.at(0)->heapInfo()) {
            std::vector<SortedVar> indices = {{"i", smt::pointerType()}};
            return std::make_shared<Forall>(
                indices, makeOp("=", makeOp("select", op.args.at(0), "i"),
                                makeOp("select", op.args.at(1), "i")));
        }
        return op.shared_from_this();
    }
    shared_ptr<smt::SMTExpr> reassemble(smt::FunDecl &funDecl) {
        std::vector<smt::Type> newInTypes;
        for (const auto &type : funDecl.inTypes) {
            if (isArray(type)) {
                newInTypes.push_back(smt::int64Type());
                newInTypes.push_back(smt::IntType(8));
            } else {
                newInTypes.push_back(type);
            }
        }
        funDecl.inTypes = std::move(newInTypes);
        return funDecl.shared_from_this();
    }
};

static shared_ptr<smt::SMTExpr> instantiateArrays(smt::SMTExpr &expr) {
    InstantiateArraysVisitor visitor;
    return expr.accept(visitor);
}

void serializeSMT(vector<SharedSMTRef> smtExprs, bool muZ, SerializeOpts opts) {
    // write to file or to stdout
    std::streambuf *buf;
    std::ofstream ofStream;

    if (!opts.OutputFileName.empty()) {
        ofStream.open(opts.OutputFileName);
        buf = ofStream.rdbuf();
    } else {
        buf = std::cout.rdbuf();
    }

    std::ostream outFile(buf);

    int i = 0;
    if (muZ) {
        set<SortedVar> introducedVariables;
        vector<SharedSMTRef> preparedSMTExprs;
        // Explicit casts are significantly easier to debug
        outFile << *makeOp("set-option", ":int-real-coercions",
                           std::make_unique<smt::ConstantBool>(false))
                        ->toSExpr()
                << "\n";
        vector<SharedSMTRef> letCompressedExprs;
        for (const auto &smt : smtExprs) {
            auto splitSMTs = smt->splitConjunctions();
            for (auto &expr : splitSMTs) {
                expr = renameAssignments(*compressLets(*expr));
                if (opts.InlineLets) {
                    expr = expr->inlineLets({});
                }
                expr = removeForalls(*expr, introducedVariables);
                preparedSMTExprs.push_back(expr->mergeImplications({}));
            }
        }
        const auto renamedVariables =
            simplifyVariableNames(introducedVariables, opts.InlineLets);
        for (const auto &var : introducedVariables) {
            outFile << *VarDecl({renamedVariables.lookup(var.name), var.type})
                            .toSExpr();
            outFile << "\n";
        }
        for (const auto &smt : preparedSMTExprs) {
            renameVariables(*smt, renamedVariables);
            outFile << *smt->toSExpr();
            outFile << "\n";
        }
    } else {
        for (auto &expr : smtExprs) {
            if (opts.Pretty) {
                expr = compressLets(*expr);
            }
            if (opts.InlineLets) {
                expr = renameAssignments(*expr)->inlineLets({});
            }
            if (opts.MergeImplications) {
                expr = expr->mergeImplications({});
            }
            if (!opts.DontInstantiate) {
                expr = instantiateArrays(*expr);
            }
            expr->toSExpr()->serialize(outFile, 0, opts.Pretty);
            outFile << "\n";
            ++i;
        }
    }

    if (!opts.OutputFileName.empty()) {
        ofStream.close();
    }
}
