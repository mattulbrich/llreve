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

using std::make_unique;
using std::vector;
using std::make_shared;
using std::unique_ptr;
using std::string;
using std::map;

using namespace smt;
using namespace llreve::opts;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

static void addArgumentsForSelection(
    ProgramSelection SMTFor, std::function<std::string(Program)> getVarName,
    std::unique_ptr<Type> varType, std::vector<TypedVariable> &argVec) {
    switch (SMTFor) {
    case ProgramSelection::First:
        argVec.emplace_back(getVarName(Program::First), varType->copy());
        break;
    case ProgramSelection::Second:
        argVec.emplace_back(getVarName(Program::Second), varType->copy());
        break;
    case ProgramSelection::Both:
        argVec.emplace_back(getVarName(Program::First), varType->copy());
        argVec.emplace_back(getVarName(Program::Second), varType->copy());
        break;
    }
}

static std::unique_ptr<TypedVariable>
cloneTypedVariable(const TypedVariable &var) {
    return make_unique<TypedVariable>(var.name, var.type->copy());
}

SMTRef functionalCouplingPredicate(Mark currentCallMark, Mark tailCallMark,
                                   vector<SortedVar> currentCallArguments,
                                   vector<SortedVar> tailCallArguments,
                                   ProgramSelection SMTFor,
                                   std::string functionName,
                                   FreeVarsMap freeVarsMap) {
    // we want to end up with something like
    // (and pre (=> (tailcall newargs res) (currentcall oldargs res)))

    // TODO get rid of filtering
    if (SMTFor == ProgramSelection::First) {
        currentCallArguments = filterVars(1, currentCallArguments);
        tailCallArguments = filterVars(1, tailCallArguments);
    }
    if (SMTFor == ProgramSelection::Second) {
        currentCallArguments = filterVars(2, currentCallArguments);
        tailCallArguments = filterVars(2, tailCallArguments);
    }

    vector<TypedVariable> resultValues;
    addArgumentsForSelection(SMTFor, resultName, int64Type(), resultValues);
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        addArgumentsForSelection(SMTFor, heapResultName, memoryType(),
                                 resultValues);
    }
    if (SMTGenerationOpts::getInstance().Stack == StackOpt::Enabled) {
        addArgumentsForSelection(SMTFor, stackResultName, memoryType(),
                                 resultValues);
    }

    // Arguments passed into the current invariant
    vector<SharedSMTRef> currentCallArgumentsPost;
    std::transform(currentCallArguments.begin(), currentCallArguments.end(),
                   std::back_inserter(currentCallArgumentsPost),
                   [](const SortedVar &var) {
                       return make_unique<TypedVariable>(var.name + "_old",
                                                         var.type->copy());
                   });
    std::transform(resultValues.begin(), resultValues.end(),
                   std::back_inserter(currentCallArgumentsPost),
                   cloneTypedVariable);

    SMTRef currentCallInvariant = std::make_unique<Op>(
        invariantName(currentCallMark, SMTFor, functionName),
        currentCallArgumentsPost);

    if (tailCallMark == EXIT_MARK) {
        return currentCallInvariant;
    }

    // In this case, a tail call is necessary to get the result values which can
    // then be used in the invariant of the current call.
    vector<SortedVar> forallArguments;
    std::transform(resultValues.begin(), resultValues.end(),
                   std::back_inserter(forallArguments),
                   [](const TypedVariable &var) {
                       return SortedVar(var.name, var.type->copy());
                   });
    if (tailCallMark == UNREACHABLE_MARK) {
        return std::make_unique<Forall>(forallArguments,
                                        std::move(currentCallInvariant));
    }

    vector<SharedSMTRef> tailCallArgumentsPre;
    std::transform(tailCallArguments.begin(), tailCallArguments.end(),
                   std::back_inserter(tailCallArgumentsPre),
                   typedVariableFromSortedVar);
    SMTRef tailCallInvariantPre = std::make_unique<Op>(
        invariantName(tailCallMark, SMTFor, functionName, InvariantAttr::PRE),
        tailCallArgumentsPre);

    vector<SharedSMTRef> tailCallArgumentsPost = tailCallArgumentsPre;
    std::transform(resultValues.begin(), resultValues.end(),
                   std::back_inserter(tailCallArgumentsPost),
                   cloneTypedVariable);
    SMTRef tailCallInvariantPost =
        std::make_unique<Op>(invariantName(tailCallMark, SMTFor, functionName),
                             tailCallArgumentsPost);

    SMTRef clause = makeOp("=>", std::move(tailCallInvariantPost),
                           std::move(currentCallInvariant));
    if (SMTFor == ProgramSelection::Both) {
        clause =
            makeOp("and", std::move(tailCallInvariantPre), std::move(clause));
    }
    return std::make_unique<Forall>(forallArguments, std::move(clause));
}

SMTRef iterativeCouplingPredicate(Mark EndIndex, vector<SortedVar> FreeVars,
                                  string FunName) {
    if (EndIndex == EXIT_MARK) {
        vector<SharedSMTRef> args = {stringExpr(resultName(Program::First)),
                                     stringExpr(resultName(Program::Second))};
        for (const auto &arg : FreeVars) {
            // No stack in output
            if (arg.name.compare(0, 5, "STACK") &&
                arg.name.compare(0, 2, "SP")) {
                args.push_back(std::make_unique<TypedVariable>(
                    arg.name, arg.type->copy()));
            }
        }
        return std::make_unique<Op>("OUT_INV", std::move(args));
    } else if (EndIndex == UNREACHABLE_MARK) {
        return make_unique<ConstantBool>(true);
    } else {
        vector<SharedSMTRef> args;
        for (auto &arg : FreeVars) {
            args.push_back(typedVariableFromSortedVar(arg));
        }
        return std::make_unique<Op>(invariantName(EndIndex,
                                                  ProgramSelection::Both,
                                                  FunName, InvariantAttr::MAIN),
                                    std::move(args));
    }
}

/// Declare an invariant
MonoPair<SMTRef> invariantDeclaration(Mark BlockIndex,
                                      vector<SortedVar> FreeVars,
                                      ProgramSelection For, std::string FunName,
                                      const llvm::Type *resultType) {
    vector<unique_ptr<Type>> args;
    for (auto arg : FreeVars) {
        args.push_back(std::move(arg.type));
    }
    vector<unique_ptr<Type>> preArgs;
    for (const auto &arg : args) {
        preArgs.push_back(arg->copy());
    }
    // add results
    args.push_back(llvmType(resultType));
    if (For == ProgramSelection::Both) {
        args.push_back(llvmType(resultType));
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        args.push_back(memoryType());
        if (For == ProgramSelection::Both) {
            args.push_back(memoryType());
        }
    }
    if (SMTGenerationOpts::getInstance().Stack == StackOpt::Enabled) {
        args.push_back(memoryType());
        if (For == ProgramSelection::Both) {
            args.push_back(memoryType());
        }
    }

    return makeMonoPair<SMTRef>(
        std::make_unique<FunDecl>(invariantName(BlockIndex, For, FunName),
                                  std::move(args), boolType()),
        std::make_unique<FunDecl>(
            invariantName(BlockIndex, For, FunName, InvariantAttr::PRE),
            std::move(preArgs), boolType()));
}

size_t invariantArgs(vector<SortedVar> freeVars, ProgramSelection prog,
                     InvariantAttr attr) {
    size_t numArgs = freeVars.size();
    if (attr == InvariantAttr::NONE) {
        // we need result arguments
        // + 1 for each result
        numArgs += 1 + (prog == ProgramSelection::Both ? 1 : 0);
        if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
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

SMTRef mainInvariantComment(Mark blockIndex, const vector<SortedVar> &freeVars,
                            ProgramSelection selection, std::string funName) {
    std::string name =
        invariantName(blockIndex, selection, funName, InvariantAttr::MAIN);
    std::string comment = ":annot (" + name;
    for (auto &arg : freeVars) {
        comment += " " + arg.name;
    }
    comment += ")";
    return make_unique<Comment>(std::move(comment));
}

SharedSMTRef mainInvariantDeclaration(Mark BlockIndex,
                                      vector<SortedVar> FreeVars,
                                      ProgramSelection For,
                                      std::string FunName) {
    vector<unique_ptr<Type>> args;
    for (auto &arg : FreeVars) {
        args.push_back(std::move(arg.type));
    }

    return std::make_shared<class FunDecl>(
        invariantName(BlockIndex, For, FunName, InvariantAttr::MAIN),
        std::move(args), boolType());
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
