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
using std::set;
using std::shared_ptr;

using namespace llreve::opts;

// Rename variables to a more readable form. This is only done to make the
// resulting SMT easier to read and has no effect
static llvm::StringMap<std::string>
simplifyVariableNames(const std::set<SortedVar> &variables) {
    llvm::StringMap<std::string> variableNameMap;
    for (const auto &var : variables) {
        variableNameMap.insert({var.name, var.name});
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

struct VariableRenamer : smt::BottomUpVisitor {
    llvm::StringMap<std::string> variableNameMap;
    VariableRenamer(llvm::StringMap<std::string> variableNameMap)
        : variableNameMap(std::move(variableNameMap)) {}
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

struct AssignmentRenameVisitor : smt::TopDownVisitor {
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
    void dispatch(smt::Forall &forall) override {
        for (auto &var : forall.vars) {
            int newIndex = ++variableMap[var.name];
            var.name += "_" + std::to_string(newIndex);
        }
    }
};

// Rename assignments to unique names. This allows moving things around as
// done by mergeImplications.
static void renameAssignments(smt::SMTExpr &expr) {
    AssignmentRenameVisitor visitor;
    expr.accept(visitor);
};

struct RemoveForallVisitor : smt::TopDownVisitor {
    std::set<SortedVar> &introducedVariables;
    RemoveForallVisitor(std::set<SortedVar> &introducedVariables)
        : introducedVariables(introducedVariables) {}
    shared_ptr<smt::SMTExpr> reassemble(smt::Forall &forall) {
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
            const auto splitSMTs = smt->splitConjunctions();
            for (const auto &splitSMT : splitSMTs) {
                letCompressedExprs.push_back(splitSMT->compressLets());
                // renaming to unique variable names simplifies the following
                // steps
            }
        }
        // Variable renaming can interfer with let compression since variables
        // are shared between different expressions. By compressing using the
        // original names and only then renaming, we avoid this problem.
        // Eventually, it might make sense to remove this sharing since it makes
        // transformations easier.
        for (auto &expr : letCompressedExprs) {
            renameAssignments(*expr);
            if (opts.InlineLets) {
                expr = expr->inlineLets({});
            }
            expr = removeForalls(*expr, introducedVariables);
            preparedSMTExprs.push_back(expr->mergeImplications({}));
        }
        const auto renamedVariables =
            simplifyVariableNames(introducedVariables);
        for (const auto &var : introducedVariables) {
            outFile << *VarDecl({renamedVariables.lookup(var.name),
                                 var.type->copy()})
                            .toSExpr();
            outFile << "\n";
        }
        for (const auto &smt : preparedSMTExprs) {
            renameVariables(*smt, renamedVariables);
            outFile << *smt->toSExpr();
            outFile << "\n";
        }
    } else {
        vector<SharedSMTRef> letCompressedExprs;
        // See the comment above on why we first compress all expressions before
        // renaming.
        for (const auto &smt : smtExprs) {
            letCompressedExprs.push_back(opts.Pretty ? smt->compressLets()
                                                     : smt);
        }
        for (auto &expr : letCompressedExprs) {
            if (opts.InlineLets) {
                renameAssignments(*expr);
                expr = expr->inlineLets({});
            }
            if (opts.MergeImplications) {
                expr = expr->mergeImplications({});
            }
            if (!opts.DontInstantiate) {
                expr = expr->instantiateArrays();
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
