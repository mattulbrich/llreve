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

using std::make_shared;
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
        vector<std::unique_ptr<Type>> args;
        declarations.push_back(make_shared<smt::FunDecl>(
            "END_QUERY", std::move(args), boolType()));
    }
    std::vector<SharedSMTRef> assertions;
    std::vector<SharedSMTRef> smtExprs;
    if (smtOpts.OutputFormat == SMTFormat::SMTHorn && !smtOpts.Invert) {
        smtExprs.push_back(std::make_shared<SetLogic>("HORN"));
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
        smtExprs.push_back(make_shared<Query>("END_QUERY"));
    } else {
        smtExprs.push_back(make_shared<CheckSat>());
        smtExprs.push_back(make_shared<GetModel>());
    }
    return smtExprs;
}

void generateSMTForMainFunctions(MonoPair<const llvm::Module &> modules,
                                 const AnalysisResultsMap &analysisResults,
                                 FileOptions fileOpts,
                                 std::vector<smt::SharedSMTRef> &assertions,
                                 std::vector<smt::SharedSMTRef> &declarations) {
    const auto &smtOpts = SMTGenerationOpts::getInstance();
    auto inInv =
        inInvariant(smtOpts.MainFunctions, analysisResults, fileOpts.InRelation,
                    modules.first, modules.second,
                    smtOpts.GlobalConstants == GlobalConstantsOpt::Enabled,
                    fileOpts.AdditionalInRelation);
    declarations.push_back(inInv);
    declarations.push_back(outInvariant(
        getFunctionArguments(smtOpts.MainFunctions, analysisResults),
        fileOpts.OutRelation, smtOpts.MainFunctions.first->getReturnType()));
    if (smtOpts.InitPredicate) {
        declarations.push_back(initPredicate(inInv));
        declarations.push_back(initPredicateComment(inInv));
        assertions.push_back(initImplication(inInv));
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
                make_shared<FunDef>(globalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
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
                make_shared<FunDef>(globalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            auto constDef2 =
                make_shared<FunDef>(otherGlobalName, empty, int64Type(),
                                    makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
            declarations.push_back(constDef2);
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
            stringConstants.push_back(make_shared<Op>("and", stringConstant));
        }
    }
    return stringConstants;
}

shared_ptr<FunDef> inInvariant(MonoPair<const llvm::Function *> funs,
                               const AnalysisResultsMap &analysisResults,
                               SharedSMTRef body, const llvm::Module &mod1,
                               const llvm::Module &mod2, bool strings,
                               bool additionalIn) {

    vector<SharedSMTRef> args;
    const auto funArgsPair =
        getFunctionArguments(funs, analysisResults)
            .indexedMap<vector<smt::SortedVar>>([](vector<smt::SortedVar> args,
                                                   int index)
                                                    -> vector<smt::SortedVar> {
                if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
                    args.push_back(SortedVar(heapName(index), memoryType()));
                }
                if (SMTGenerationOpts::getInstance().Stack ==
                    StackOpt::Enabled) {
                    args.push_back(
                        SortedVar(stackPointerName(index), pointerType()));
                    args.push_back(SortedVar(stackName(index), memoryType()));
                }
                return args;
            });
    vector<string> Args1;
    for (const auto &arg : funArgsPair.first) {
        Args1.push_back(arg.name);
    }
    vector<string> Args2;
    for (const auto &arg : funArgsPair.second) {
        Args2.push_back(arg.name);
    }

    assert(Args1.size() == Args2.size());

    vector<SortedVar> funArgs;
    funArgsPair.forEach([&funArgs](const auto &args) {
        for (auto var : args) {
            funArgs.push_back({var.name, std::move(var.type)});
        }
    });

    std::transform(Args1.begin(), Args1.end(), Args2.begin(),
                   std::back_inserter(args),
                   [](const auto &arg1, const auto &arg2) {
                       return makeOp("=", arg1, arg2);
                   });
    if (additionalIn) {
        args.push_back(body);
    }
    if (body == nullptr || additionalIn) {
        body = make_shared<Op>("and", args);
    }
    if (strings) {
        // Add values of static arrays, strings and similar things
        vector<SharedSMTRef> smtArgs = {body};
        makeMonoPair(&mod1, &mod2)
            .indexedMap<vector<SharedSMTRef>>(
                [&args](const llvm::Module *mod, int index) {
                    return stringConstants(*mod, heapName(index));
                })
            .forEach([&smtArgs](vector<SharedSMTRef> constants) {
                if (!constants.empty()) {
                    smtArgs.push_back(make_shared<Op>("and", constants));
                }
            });
        body = make_shared<Op>("and", smtArgs);
    }

    return make_shared<FunDef>("IN_INV", funArgs, boolType(), body);
}

SharedSMTRef outInvariant(MonoPair<vector<smt::SortedVar>> functionArgs,
                          SharedSMTRef body, const llvm::Type *returnType) {
    vector<SortedVar> funArgs = {
        {resultName(Program::First), llvmType(returnType)},
        {resultName(Program::Second), llvmType(returnType)}};
    std::sort(functionArgs.first.begin(), functionArgs.first.end());
    std::sort(functionArgs.second.begin(), functionArgs.second.end());
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (auto arg : functionArgs.first) {
            funArgs.push_back(std::move(arg));
        }
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        funArgs.push_back({heapName(Program::First), memoryType()});
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (auto arg : functionArgs.second) {
            funArgs.push_back(std::move(arg));
        }
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

    return make_shared<FunDef>("OUT_INV", funArgs, boolType(), body);
}

SharedSMTRef initPredicate(shared_ptr<const FunDef> inInv) {

    vector<std::unique_ptr<Type>> funArgs;
    for (auto var : inInv->args) {
        funArgs.push_back(std::move(var.type));
    }

    return make_shared<smt::FunDecl>("INIT", std::move(funArgs), boolType());
}

SharedSMTRef initPredicateComment(shared_ptr<const FunDef> inInv) {

    std::stringstream comment;
    comment << "; INIT-ARGS";
    for (auto var : inInv->args) {
        comment << " " << var.name;
    }

    return make_shared<smt::Comment>(comment.str());
}

SharedSMTRef initImplication(shared_ptr<const FunDef> funDecl) {

    vector<SharedSMTRef> ininv_args;
    vector<SharedSMTRef> init_args;
    vector<SortedVar> quantified_vars;

    for (auto var : funDecl->args) {
        ininv_args.push_back(typedVariableFromSortedVar(var));
        init_args.push_back(typedVariableFromSortedVar(var));
    }

    SharedSMTRef inAppl = std::make_shared<Op>("IN_INV", ininv_args);
    SharedSMTRef initAppl = std::make_shared<Op>("INIT", init_args);

    SharedSMTRef clause = makeOp("=>", inAppl, initAppl);
    auto forall = std::make_shared<smt::Forall>(funDecl->args, clause);

    return make_shared<smt::Assert>(forall);
}
