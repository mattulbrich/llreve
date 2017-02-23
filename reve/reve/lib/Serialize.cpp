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

#include <fstream>
#include <iostream>

using smt::SharedSMTRef;
using smt::SortedVar;
using smt::VarDecl;
using std::vector;
using std::set;

using namespace llreve::opts;

// Rename variables to a more readable form. This is only done to make the
// resulting SMT easier to read and has no effect
static std::map<SortedVar, SortedVar>
simplifyVariableNames(const std::set<SortedVar> &variableNames) {
    std::map<SortedVar, SortedVar> variableMap;
    for (const auto &var : variableNames) {
        variableMap.insert({var, var});
    }
    return variableMap;
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
        for (const auto &smt : smtExprs) {
            const auto splitSMTs = smt->splitConjunctions();
            for (const auto &splitSMT : splitSMTs) {
                // renaming to unique variable names simplifies the following
                // steps
                auto smt_ = splitSMT->compressLets()->renameAssignments({});
                if (opts.InlineLets) {
                    smt_ = smt->inlineLets({});
                }
                preparedSMTExprs.push_back(
                    smt_->removeForalls(introducedVariables)
                        ->mergeImplications({}));
            }
        }
        std::map<SortedVar, SortedVar> renamedVariables =
            simplifyVariableNames(introducedVariables);
        for (const auto &var : introducedVariables) {
            outFile << *VarDecl(var).toSExpr();
            outFile << "\n";
        }
        for (const auto &smt : preparedSMTExprs) {
            outFile << *smt->toSExpr();
            outFile << "\n";
        }
    } else {
        for (const auto &smt : smtExprs) {
            smt::SharedSMTRef out = opts.Pretty ? smt->compressLets() : smt;
            if (opts.InlineLets) {
                out = out->renameAssignments({})->inlineLets({});
            }
            if (opts.MergeImplications) {
                out = out->mergeImplications({});
            }
            if (!opts.DontInstantiate) {
                out = out->instantiateArrays();
            }
            out->toSExpr()->serialize(outFile, 0, opts.Pretty);
            outFile << "\n";
            ++i;
        }
    }

    if (!opts.OutputFileName.empty()) {
        ofStream.close();
    }
}
