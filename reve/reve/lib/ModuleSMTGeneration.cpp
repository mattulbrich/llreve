/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "ModuleSMTGeneration.h"

#include "Compat.h"
#include "FixedAbstraction.h"
#include "FunctionSMTGeneration.h"
#include "Helper.h"
#include "Invariant.h"
#include "Memory.h"
#include "Slicing.h"

#include "llvm/IR/Constants.h"

using std::make_unique;
using std::shared_ptr;
using std::string;
using std::vector;
using std::set;

using namespace smt;
using namespace llreve::opts;

vector<SharedSMTRef> generateSMT(MonoPair<const llvm::Module &> modules,
                                 const AnalysisResultsMap &analysisResults,
                                 FileOptions fileOpts) {
    std::vector<SharedSMTRef> declarations;
    std::vector<SortedVar> variableDeclarations;
    SMTGenerationOpts &smtOpts = SMTGenerationOpts::getInstance();

    if (smtOpts.OutputFormat == SMTFormat::Z3) {
        declarations.push_back(make_unique<smt::FunDecl>(
            "END_QUERY", std::vector<Type>(), boolType()));
    }
    std::vector<SharedSMTRef> assertions;
    std::vector<SharedSMTRef> smtExprs;
    if (smtOpts.OutputFormat == SMTFormat::SMTHorn && !smtOpts.Invert) {
        smtExprs.push_back(make_unique<SetLogic>("HORN"));
    }

    if (smtOpts.Stack == StackOpt::Enabled) {
        declarations.push_back(select_Declaration());
        declarations.push_back(store_Declaration());
    }

    externDeclarations(modules.first, modules.second, declarations,
                       fileOpts.FunctionConditions);

    auto globalDecls = globalDeclarations(modules.first, modules.second);
    smtExprs.insert(smtExprs.end(), globalDecls.begin(), globalDecls.end());

    // We use an iterative encoding for the main function since this seems to
    // perform better than a recursive encoding
    generateSMTForMainFunctions(modules, analysisResults, fileOpts, assertions,
                                declarations);

    for (auto &funPair : smtOpts.CoupledFunctions) {
        // We only need to generate a relational abstraction if both program
        // call a function transitively since we will never couple calls
        // otherwise
        auto isCalledFromMain =
            callsTransitively(*smtOpts.MainFunctions.first, *funPair.first) &&
            callsTransitively(*smtOpts.MainFunctions.second, *funPair.second);
        // Main is abstracted using an iterative encoding except for the case
        // where OnlyRecursive is enabled
        auto onlyRecursiveMain =
            funPair == smtOpts.MainFunctions &&
            smtOpts.OnlyRecursive == FunctionEncoding::OnlyRecursive;
        if (!hasMutualFixedAbstraction(funPair) &&
            (onlyRecursiveMain || isCalledFromMain)) {
            if (funPair.first->getName() == "__criterion") {
                auto newSmtExprs = slicingAssertion(funPair, analysisResults);
                assertions.insert(assertions.end(), newSmtExprs.begin(),
                                  newSmtExprs.end());
            } else {
                generateRelationalFunctionSMT(funPair, analysisResults,
                                              assertions, declarations);
            }
        }
    }
    generateFunctionalAbstractions(modules.first, smtOpts.MainFunctions.first,
                                   analysisResults, Program::First, assertions,
                                   declarations);
    generateFunctionalAbstractions(modules.second, smtOpts.MainFunctions.second,
                                   analysisResults, Program::Second, assertions,
                                   declarations);

    smtExprs.insert(smtExprs.end(), declarations.begin(), declarations.end());
    if (SMTGenerationOpts::getInstance().Invert) {
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("INV_INDEX_START", int64Type())));
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("INV_INDEX_END", int64Type())));
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("FUNCTION_1", int64Type())));
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("FUNCTION_2", int64Type())));
        smtExprs.push_back(make_unique<VarDecl>(SortedVar("MAIN", boolType())));
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("PROGRAM_1", boolType())));
        smtExprs.push_back(
            make_unique<VarDecl>(SortedVar("PROGRAM_2", boolType())));
        smtExprs.push_back(
            make_unique<Assert>(make_unique<Op>("or", assertions)));
    } else {
        for (const auto &assertion : assertions) {
            smtExprs.push_back(make_unique<Assert>(assertion));
        }
    }
    if (smtOpts.OutputFormat == SMTFormat::Z3) {
        smtExprs.push_back(make_unique<Query>("END_QUERY"));
    } else {
        smtExprs.push_back(make_unique<CheckSat>());
        smtExprs.push_back(make_unique<GetModel>());
    }
    return smtExprs;
}

void generateSMTForMainFunctions(MonoPair<const llvm::Module &> modules,
                                 const AnalysisResultsMap &analysisResults,
                                 FileOptions fileOpts,
                                 std::vector<smt::SharedSMTRef> &assertions,
                                 std::vector<smt::SharedSMTRef> &declarations) {
    const auto &smtOpts = SMTGenerationOpts::getInstance();
    std::shared_ptr<FunDef> inInv =
        inInvariant(smtOpts.MainFunctions, analysisResults, fileOpts.InRelation,
                    modules.first, modules.second,
                    smtOpts.GlobalConstants == GlobalConstantsOpt::Enabled,
                    fileOpts.AdditionalInRelation);
    declarations.push_back(inInv);
    declarations.push_back(outInvariant(
        getFunctionArguments(smtOpts.MainFunctions, analysisResults),
        fileOpts.OutRelation, smtOpts.MainFunctions.first->getReturnType()));
    if (smtOpts.InitPredicate) {
        declarations.push_back(initPredicate(*inInv));
        declarations.push_back(initPredicateComment(*inInv));
        assertions.push_back(initImplication(*inInv));
    }
    generateRelationalIterativeSMT(smtOpts.MainFunctions, analysisResults,
                                   assertions, declarations);
}

void generateFunctionalAbstractions(
    const llvm::Module &module, const llvm::Function *mainFunction,
    const AnalysisResultsMap &analysisResults, Program prog,
    std::vector<smt::SharedSMTRef> &assertions,
    std::vector<smt::SharedSMTRef> &declarations) {
    for (auto &fun : module) {
        if (!isLlreveIntrinsic(fun) && !hasFixedAbstraction(fun) &&
            callsTransitively(*mainFunction, fun)) {
            generateFunctionalFunctionSMT(&fun, analysisResults, prog,
                                          assertions, declarations);
        }
    }
}

SMTRef select_Declaration() {
    SharedSMTRef body =
        makeOp("ite", "onStack", makeOp("select", "stack", "pointer"),
               makeOp("select", "heap", "pointer"));
    vector<SortedVar> args = {{"heap", memoryType()},
                              {"stack", memoryType()},
                              {"pointer", int64Type()},
                              {"onStack", boolType()}};
    return make_unique<FunDef>("select_", std::move(args), int64Type(), body);
}

SMTRef store_Declaration() {
    SharedSMTRef body =
        makeOp("ite", "onStack", makeOp("store", "stack", "pointer", "val"),
               makeOp("store", "heap", "pointer", "val"));
    vector<SortedVar> args = {{"heap", memoryType()},
                              {"stack", memoryType()},
                              {"pointer", int64Type()},
                              {"onStack", boolType()},
                              {"val", int64Type()}};
    return make_unique<FunDef>("store_", std::move(args), memoryType(), body);
}

vector<SharedSMTRef> globalDeclarationsForMod(int globalPointer,
                                              const llvm::Module &mod,
                                              const llvm::Module &modOther,
                                              int program) {
    std::vector<SharedSMTRef> declarations;
    for (auto &global1 : mod.globals()) {
        std::string globalName = global1.getName();
        std::string otherGlobalName = dropSuffixFromName(globalName) + "$" +
                                      std::to_string(swapIndex(program));
        if (!modOther.getNamedGlobal(otherGlobalName)) {
            // we want the size of string constants not the size of the
            // pointer
            // pointing to them
            if (const auto pointerTy =
                    llvm::dyn_cast<llvm::PointerType>(global1.getType())) {
                globalPointer +=
                    typeSize(pointerTy->getElementType(), mod.getDataLayout());
            } else {
                globalPointer +=
                    typeSize(global1.getType(), mod.getDataLayout());
            }
            std::vector<SortedVar> empty;
            auto constDef1 =
                make_unique<FunDef>(globalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(std::move(constDef1));
        }
    }
    return declarations;
}

std::vector<SharedSMTRef> globalDeclarations(const llvm::Module &mod1,
                                             const llvm::Module &mod2) {
    // First match globals with the same name to make sure that they get the
    // same pointer, then match globals that only exist in one module
    std::vector<SharedSMTRef> declarations;
    int globalPointer = 1;
    for (auto &global1 : mod1.globals()) {
        std::string globalName = global1.getName();
        std::string otherGlobalName = dropSuffixFromName(globalName) + "$2";
        if (mod2.getNamedGlobal(otherGlobalName)) {
            // we want the size of string constants not the size of the
            // pointer
            // pointing to them
            if (const auto pointerTy =
                    llvm::dyn_cast<llvm::PointerType>(global1.getType())) {
                globalPointer +=
                    typeSize(pointerTy->getElementType(), mod1.getDataLayout());
            } else {
                globalPointer +=
                    typeSize(global1.getType(), mod1.getDataLayout());
            }
            std::vector<SortedVar> empty;
            auto constDef1 =
                make_unique<FunDef>(globalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            auto constDef2 =
                make_unique<FunDef>(otherGlobalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(std::move(constDef1));
            declarations.push_back(std::move(constDef2));
        }
    }
    auto decls1 = globalDeclarationsForMod(globalPointer, mod1, mod2, 1);
    auto decls2 = globalDeclarationsForMod(globalPointer, mod2, mod1, 2);
    declarations.insert(declarations.end(), decls1.begin(), decls1.end());
    declarations.insert(declarations.end(), decls2.begin(), decls2.end());
    return declarations;
}

vector<SharedSMTRef> stringConstants(const llvm::Module &mod, string memory) {
    vector<SharedSMTRef> stringConstants;
    for (const auto &global : mod.globals()) {
        const string globalName = global.getName();
        vector<SharedSMTRef> stringConstant;
        if (global.hasInitializer() && global.isConstant()) {
            if (const auto arr = llvm::dyn_cast<llvm::ConstantDataArray>(
                    global.getInitializer())) {
                for (unsigned int i = 0; i < arr->getNumElements(); ++i) {
                    stringConstant.push_back(
                        makeOp("=", std::to_string(arr->getElementAsInteger(i)),
                               makeOp("select", makeOp("+", globalName,
                                                       std::to_string(i)))));
                }
            }
        }
        if (!stringConstant.empty()) {
            stringConstants.push_back(make_unique<Op>("and", stringConstant));
        }
    }
    return stringConstants;
}

std::unique_ptr<FunDef> inInvariant(MonoPair<const llvm::Function *> funs,
                                    const AnalysisResultsMap &analysisResults,
                                    SharedSMTRef body, const llvm::Module &mod1,
                                    const llvm::Module &mod2, bool strings,
                                    bool additionalIn) {
    MonoPair<std::vector<smt::SortedVar>> functionArgumentsPair =
        getFunctionArguments(funs, analysisResults);
    functionArgumentsPair.first =
        addMemoryArrays(functionArgumentsPair.first, Program::First);
    functionArgumentsPair.second =
        addMemoryArrays(functionArgumentsPair.second, Program::Second);

    vector<SortedVar> funArgs;
    funArgs.insert(funArgs.end(), functionArgumentsPair.first.begin(),
                   functionArgumentsPair.first.end());
    funArgs.insert(funArgs.end(), functionArgumentsPair.second.begin(),
                   functionArgumentsPair.second.end());

    vector<SMTRef> functionArguments1;
    std::transform(
        functionArgumentsPair.first.begin(), functionArgumentsPair.first.end(),
        std::back_inserter(functionArguments1), typedVariableFromSortedVar);
    vector<SMTRef> functionArguments2;
    std::transform(functionArgumentsPair.second.begin(),
                   functionArgumentsPair.second.end(),
                   std::back_inserter(functionArguments2),
                   typedVariableFromSortedVar);

    if (body == nullptr || additionalIn) {
        assert(functionArguments1.size() == functionArguments2.size());
        vector<SharedSMTRef> equalInputs;
        std::transform(functionArguments1.begin(), functionArguments1.end(),
                       functionArguments2.begin(), std::back_inserter(equalInputs),
                       [](auto &arg1, auto &arg2) {
                           return makeOp("=", std::move(arg1), std::move(arg2));
                       });
        if (additionalIn) {
            equalInputs.push_back(body);
        }
        body = make_unique<Op>("and", equalInputs);
    }
    if (strings) {
        // Add values of static arrays, strings and similar things
        vector<SharedSMTRef> smtArgs = {body};
        auto stringConstants1 = stringConstants(mod1, heapName(Program::First));
        auto stringConstants2 =
            stringConstants(mod2, heapName(Program::Second));
        if (!stringConstants1.empty()) {
            smtArgs.push_back(make_unique<Op>("and", stringConstants1));
        }
        if (!stringConstants2.empty()) {
            smtArgs.push_back(make_unique<Op>("and", stringConstants2));
        }
        body = make_unique<Op>("and", smtArgs);
    }

    return make_unique<FunDef>("IN_INV", funArgs, boolType(), body);
}

std::unique_ptr<FunDef>
outInvariant(MonoPair<vector<smt::SortedVar>> functionArgs, SharedSMTRef body,
             const llvm::Type *returnType) {
    vector<SortedVar> funArgs = {
        {resultName(Program::First), llvmType(returnType)},
        {resultName(Program::Second), llvmType(returnType)}};
    std::sort(functionArgs.first.begin(), functionArgs.first.end());
    std::sort(functionArgs.second.begin(), functionArgs.second.end());
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        funArgs.insert(funArgs.end(), functionArgs.first.begin(),
                       functionArgs.first.end());
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        funArgs.push_back({heapName(Program::First), memoryType()});
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        funArgs.insert(funArgs.end(), functionArgs.second.begin(),
                       functionArgs.second.end());
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        funArgs.push_back({heapName(Program::Second), memoryType()});
    }
    if (body == nullptr) {
        body = makeOp("=", resultName(Program::First),
                      resultName(Program::Second));
        if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
            body = makeOp(
                "and", body,
                makeOp("=", smt::memoryVariable(heapName(Program::First)),
                       smt::memoryVariable(heapName(Program::Second))));
        }
    }

    return make_unique<FunDef>("OUT_INV", funArgs, boolType(), body);
}

SMTRef initPredicate(const FunDef &inInv) {
    vector<Type> funArgs;
    for (const auto &var : inInv.args) {
        funArgs.push_back(var.type);
    }

    return make_unique<smt::FunDecl>("INIT", std::move(funArgs), boolType());
}

SMTRef initPredicateComment(const FunDef &inInv) {

    std::ostringstream comment;
    comment << "; INIT-ARGS";
    for (const auto &var : inInv.args) {
        comment << " " << var.name;
    }

    return make_unique<smt::Comment>(comment.str());
}

SMTRef initImplication(const FunDef &funDecl) {
    vector<SharedSMTRef> ininv_args;
    vector<SharedSMTRef> init_args;
    vector<SortedVar> quantified_vars;

    for (const auto &var : funDecl.args) {
        ininv_args.push_back(typedVariableFromSortedVar(var));
        init_args.push_back(typedVariableFromSortedVar(var));
    }

    SMTRef inAppl = std::make_unique<Op>("IN_INV", ininv_args);
    SMTRef initAppl = std::make_unique<Op>("INIT", init_args);

    SMTRef clause = makeOp("=>", std::move(inAppl), std::move(initAppl));
    SMTRef forall =
        std::make_unique<smt::Forall>(funDecl.args, std::move(clause));

    // return make_unique<smt::Assert>(std::move(forall));
    // MU: Potential bugfix for #21
    return forall;
}
