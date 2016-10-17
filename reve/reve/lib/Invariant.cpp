/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Invariant.h"

#include "Helper.h"
#include "Opts.h"

using std::vector;
using std::make_shared;
using std::unique_ptr;
using std::string;
using smt::makeOp;
using smt::stringExpr;
using smt::SharedSMTRef;
using smt::SMTRef;
using smt::SMTExpr;
using smt::SortedVar;
using smt::Forall;
using smt::FunDecl;

using std::map;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

SMTRef invariant(Mark StartIndex, Mark EndIndex, vector<SortedVar> InputArgs,
                 vector<SortedVar> EndArgs, ProgramSelection SMTFor,
                 std::string FunName, FreeVarsMap freeVarsMap) {
    // we want to end up with something like
    // (and pre (=> (nextcall newargs res) (currentcall oldargs res)))
    auto FilteredArgs = InputArgs;
    auto FilteredEndArgs = EndArgs;
    if (SMTFor == ProgramSelection::First) {
        FilteredArgs = filterVars(1, FilteredArgs);
        FilteredEndArgs = filterVars(1, FilteredEndArgs);
    }
    if (SMTFor == ProgramSelection::Second) {
        FilteredArgs = filterVars(2, FilteredArgs);
        FilteredEndArgs = filterVars(2, FilteredEndArgs);
    }
    vector<string> ResultArgs;
    switch (SMTFor) {
    case ProgramSelection::First:
        ResultArgs.push_back("result$1");
        break;
    case ProgramSelection::Second:
        ResultArgs.push_back("result$2");
        break;
    case ProgramSelection::Both:
        ResultArgs.push_back("result$1");
        ResultArgs.push_back("result$2");
        break;
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        switch (SMTFor) {
        case ProgramSelection::First:
            ResultArgs.push_back("HEAP$1_res");
            break;
        case ProgramSelection::Second:
            ResultArgs.push_back("HEAP$2_res");
            break;
        case ProgramSelection::Both:
            ResultArgs.push_back("HEAP$1_res");
            ResultArgs.push_back("HEAP$2_res");
            break;
        }
    }
    // Arguments passed into the current invariant
    vector<string> EndArgsVect;
    for (const auto &arg : FilteredArgs) {
        EndArgsVect.push_back(arg.name + "_old");
    }
    EndArgsVect.insert(EndArgsVect.end(), ResultArgs.begin(), ResultArgs.end());
    // The current invariant
    SMTRef Clause =
        makeOp(invariantName(StartIndex, SMTFor, FunName), EndArgsVect);

    if (EndIndex != EXIT_MARK) {
        // The result of another call is required to establish the current
        // invariant
        // so we do do that call and use the result in the current invariant
        vector<SortedVar> ForallArgs;
        for (auto ResultArg : ResultArgs) {
            ForallArgs.push_back(SortedVar(ResultArg, argSort(ResultArg)));
        }
        if (EndIndex != UNREACHABLE_MARK) {
            vector<string> usingArgsPre;
            for (const auto &arg : FilteredEndArgs) {
                usingArgsPre.push_back(arg.name);
            }
            vector<string> usingArgs = usingArgsPre;
            SMTRef PreInv = makeOp(
                invariantName(EndIndex, SMTFor, FunName, InvariantAttr::PRE),
                usingArgsPre);
            usingArgs.insert(usingArgs.end(), ResultArgs.begin(),
                             ResultArgs.end());
            Clause =
                makeOp("=>", makeOp(invariantName(EndIndex, SMTFor, FunName),
                                    usingArgs),
                       std::move(Clause));
            if (SMTFor == ProgramSelection::Both) {
                Clause = makeOp("and", std::move(PreInv), std::move(Clause));
            }
        }
        Clause = std::make_unique<Forall>(ForallArgs, std::move(Clause));
    }
    return Clause;
}

SMTRef mainInvariant(Mark EndIndex, vector<SortedVar> FreeVars,
                     string FunName) {
    vector<string> args;
    for (const auto &var : FreeVars) {
        args.push_back(var.name);
    }
    if (EndIndex == EXIT_MARK) {
        vector<string> Args = {"result$1", "result$2"};
        for (const auto &arg : args) {
            // No stack in output
            if (arg.compare(0, 5, "STACK") && arg.compare(0, 2, "SP")) {
                Args.push_back(arg);
            }
        }
        return makeOp("OUT_INV", Args);
    }
    if (EndIndex == UNREACHABLE_MARK) {
        return stringExpr("true");
    }
    return makeOp(invariantName(EndIndex, ProgramSelection::Both, FunName,
                                InvariantAttr::MAIN),
                  args);
}

/// Declare an invariant
MonoPair<SMTRef> invariantDeclaration(Mark BlockIndex,
                                      vector<smt::SortedVar> FreeVars,
                                      ProgramSelection For, std::string FunName,
                                      const llvm::Type *resultType) {
    vector<string> args;
    for (const auto &arg : FreeVars) {
        args.push_back(getSMTType(arg.type));
    }
    const vector<string> preArgs = args;
    // add results
    args.push_back(llvmTypeToSMTSort(resultType));
    if (For == ProgramSelection::Both) {
        args.push_back(llvmTypeToSMTSort(resultType));
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        args.push_back(arrayType());
        if (For == ProgramSelection::Both) {
            args.push_back(arrayType());
        }
    }

    return makeMonoPair<SMTRef>(
        std::make_unique<FunDecl>(invariantName(BlockIndex, For, FunName), args,
                                  "Bool"),
        std::make_unique<FunDecl>(
            invariantName(BlockIndex, For, FunName, InvariantAttr::PRE),
            preArgs, "Bool"));
}

size_t invariantArgs(vector<smt::SortedVar> freeVars, ProgramSelection prog,
                     InvariantAttr attr) {
    size_t numArgs = freeVars.size();
    if (attr == InvariantAttr::NONE) {
        // we need result arguments
        // + 1 for each result
        numArgs += 1 + (prog == ProgramSelection::Both ? 1 : 0);
        if (SMTGenerationOpts::getInstance().Heap) {
            // index + value at that index
            if (prog == ProgramSelection::Both) {
                numArgs += 2;
            } else {
                numArgs += 1;
            }
        }
    }
    return numArgs;
}

size_t maxArgs(FreeVarsMap freeVarsMap, ProgramSelection prog,
               InvariantAttr attr) {
    size_t maxArgs = 0;
    for (auto It : freeVarsMap) {
        size_t numArgs = invariantArgs(It.second, prog, attr);
        if (numArgs > maxArgs) {
            maxArgs = numArgs;
        }
    }
    return maxArgs;
}

SharedSMTRef mainInvariantDeclaration(Mark BlockIndex,
                                      vector<smt::SortedVar> FreeVars,
                                      ProgramSelection For,
                                      std::string FunName) {
    vector<string> Args;
    for (const auto &arg : FreeVars) {
        Args.push_back(getSMTType(arg.type));
    }

    return std::make_shared<class FunDecl>(
        invariantName(BlockIndex, For, FunName, InvariantAttr::MAIN), Args,
        "Bool");
}

/// Return the invariant name, special casing the entry block
string invariantName(Mark Index, ProgramSelection For, std::string FunName,
                     InvariantAttr attr, uint32_t VarArgs) {
    string Name;
    if (attr == InvariantAttr::MAIN) {
        Name = "INV_MAIN";
        Name += "_" + Index.toString();
    } else {
        if (Index == ENTRY_MARK) {
            Name = "INV_REC_" + FunName;
        } else {
            Name = "INV_" + Index.toString();
        }
    }

    if (VarArgs > 0) {
        Name += "_" + std::to_string(VarArgs) + "varargs";
    }
    if (For == ProgramSelection::First) {
        Name += "__1";
    } else if (For == ProgramSelection::Second) {
        Name += "__2";
    }
    if (attr == InvariantAttr::PRE) {
        Name += "_PRE";
    }
    return Name;
}
