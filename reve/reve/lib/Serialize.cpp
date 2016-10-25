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
        // Explicit casts are a lot easier to debug
        outFile << *makeOp("set-option", ":int-real-coercions",
                           std::make_unique<smt::ConstantBool>(false))
                        ->toSExpr()
                << "\n";
        for (const auto &smt : smtExprs) {
            const auto splitSMTs = smt->splitConjunctions();
            for (const auto &splitSMT : splitSMTs) {
                preparedSMTExprs.push_back(
                    splitSMT->compressLets()
                        ->renameAssignments({})
                        ->removeForalls(introducedVariables)
                        ->mergeImplications({}));
            }
        }
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
