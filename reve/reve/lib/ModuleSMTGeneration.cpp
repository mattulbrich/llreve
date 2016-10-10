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
#include "FunctionSMTGeneration.h"
#include "Helper.h"
#include "Invariant.h"
#include "Memory.h"

#include "llvm/IR/Constants.h"

using std::make_shared;
using std::make_unique;
using std::shared_ptr;
using std::string;
using std::vector;
using std::set;

using smt::CheckSat;
using smt::Forall;
using smt::FunDef;
using smt::GetModel;
using smt::Op;
using smt::Query;
using smt::SetLogic;
using smt::SharedSMTRef;
using smt::SMTRef;
using smt::SortedVar;
using smt::VarDecl;
using smt::makeOp;
using smt::stringExpr;

vector<SharedSMTRef>
generateSMT(MonoPair<shared_ptr<llvm::Module>> modules,
            vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
            FileOptions fileOpts) {
    std::vector<SharedSMTRef> declarations;
    std::vector<SortedVar> variableDeclarations;

    if (SMTGenerationOpts::getInstance().MuZ) {
        vector<string> args;
        declarations.push_back(
            make_shared<smt::FunDecl>("END_QUERY", args, "Bool"));
    }
    std::vector<SharedSMTRef> assertions;
    std::vector<SharedSMTRef> smtExprs;
    if (!SMTGenerationOpts::getInstance().MuZ &&
        !SMTGenerationOpts::getInstance().Invert) {
        smtExprs.push_back(std::make_shared<SetLogic>("HORN"));
    }

    if (doesAccessMemory(*modules.first) || doesAccessMemory(*modules.second)) {
        SMTGenerationOpts::getInstance().Heap = true;
    }

    SMTGenerationOpts &smtOpts = SMTGenerationOpts::getInstance();

    externDeclarations(*modules.first, *modules.second, declarations,
                       fileOpts.FunctionConditions);
    if (smtOpts.MainFunction == "" && !preprocessedFuns.empty()) {
        smtOpts.MainFunction = preprocessedFuns.at(0).first.fun->getName();
    }

    auto globalDecls = globalDeclarations(*modules.first, *modules.second);
    smtExprs.insert(smtExprs.end(), globalDecls.begin(), globalDecls.end());

    for (auto &funPair : preprocessedFuns) {
        // Main function
        if (funPair.first.fun->getName() == smtOpts.MainFunction) {
            auto inInv = inInvariant(
                makeMonoPair(funPair.first.fun, funPair.second.fun),
                fileOpts.InRelation, *modules.first, *modules.second,
                smtOpts.GlobalConstants, fileOpts.AdditionalInRelation);
            smtExprs.push_back(inInv);
            smtExprs.push_back(outInvariant(
                functionArgs(*funPair.first.fun, *funPair.second.fun),
                fileOpts.OutRelation, funPair.first.fun->getReturnType()));
            if (smtOpts.InitPredicate) {
                smtExprs.push_back(initPredicate(inInv));
                smtExprs.push_back(initPredicateComment(inInv));
                assertions.push_back(initImplication(inInv));
            }
            auto newSmtExprs =
                mainAssertion(funPair, declarations, variableDeclarations,
                              smtOpts.OnlyRecursive);
            assertions.insert(assertions.end(), newSmtExprs.begin(),
                              newSmtExprs.end());
        }
        // Other functions used by the main function or the main function if
        // it’s recursive
        if (funPair.first.fun->getName() != smtOpts.MainFunction ||
            (!(doesNotRecurse(*funPair.first.fun) &&
               doesNotRecurse(*funPair.second.fun)) ||
             smtOpts.OnlyRecursive)) {
            if (funPair.first.fun->getName() == "__criterion") {
                auto newSmtExprs = slicingAssertion(funPair);
                assertions.insert(assertions.end(), newSmtExprs.begin(),
                                  newSmtExprs.end());
            } else {
                auto newSmtExprs = functionAssertion(funPair, declarations,
                                                     variableDeclarations);
                assertions.insert(assertions.end(), newSmtExprs.begin(),
                                  newSmtExprs.end());
            }
        }
    }
    smtExprs.insert(smtExprs.end(), declarations.begin(), declarations.end());
    set<string> declaredVariables;
    for (const auto &var : variableDeclarations) {
        if (declaredVariables.find(var.name) == declaredVariables.end()) {
            declaredVariables.insert(var.name);
            smtExprs.push_back(make_shared<VarDecl>(var.name, var.type));
        }
    }
    smtExprs.insert(smtExprs.end(), assertions.begin(), assertions.end());
    if (SMTGenerationOpts::getInstance().MuZ) {
        smtExprs.push_back(make_shared<Query>("END_QUERY"));
    } else {
        smtExprs.push_back(make_shared<CheckSat>());
        smtExprs.push_back(make_shared<GetModel>());
    }
    return smtExprs;
}

void externDeclarations(llvm::Module &mod1, llvm::Module &mod2,
                        std::vector<SharedSMTRef> &declarations,
                        std::multimap<string, string> funCondMap) {
    for (auto &fun1 : mod1) {
        if (fun1.isDeclaration() && !fun1.isIntrinsic()) {
            auto fun2P = mod2.getFunction(fun1.getName());
            if (fun2P && fun1.getName() != "__mark" &&
                fun1.getName() != "__splitmark") {
                llvm::Function &fun2 = *fun2P;
                // Calculate the number of varargs used in function calls
                set<uint32_t> varArgs = getVarArgs(fun1);
                set<uint32_t> varArgs2 = getVarArgs(fun2);
                for (auto el : varArgs2) {
                    varArgs.insert(el);
                }
                for (auto argNum : varArgs) {
                    std::vector<SortedVar> args;
                    auto funArgs1 = funArgs(fun1, "arg1_", argNum);
                    for (auto arg : funArgs1) {
                        args.push_back(arg);
                    }
                    if (SMTGenerationOpts::getInstance().Heap) {
                        args.push_back(SortedVar("HEAP$1", arrayType()));
                    }
                    auto funArgs2 = funArgs(fun2, "arg2_", argNum);
                    for (auto arg : funArgs2) {
                        args.push_back(arg);
                    }
                    if (SMTGenerationOpts::getInstance().Heap) {
                        args.push_back(SortedVar("HEAP$2", arrayType()));
                    }
                    std::string funName = invariantName(
                        ENTRY_MARK, ProgramSelection::Both,
                        fun1.getName().str(), InvariantAttr::NONE, argNum);
                    // TODO Use the correct return types
                    args.push_back(SortedVar("res1", "Int"));
                    args.push_back(SortedVar("res2", "Int"));
                    if (SMTGenerationOpts::getInstance().Heap) {
                        args.push_back(SortedVar("HEAP$1_res", arrayType()));
                        args.push_back(SortedVar("HEAP$2_res", arrayType()));
                    }
                    SharedSMTRef body = makeOp("=", "res1", "res2");
                    if (SMTGenerationOpts::getInstance().Heap) {
                        SharedSMTRef heapOutEqual =
                            makeOp("=", "HEAP$1_res", "HEAP$2_res");
                        body = makeOp("and", body, heapOutEqual);
                    }
                    std::vector<SharedSMTRef> equalOut;
                    auto range = funCondMap.equal_range(fun1.getName());
                    for (auto i = range.first; i != range.second; ++i) {
                        equalOut.push_back(stringExpr(i->second));
                    }
                    if (!equalOut.empty()) {
                        equalOut.push_back(body);
                        body = make_shared<Op>("and", equalOut);
                    }
                    std::vector<SharedSMTRef> equal;
                    for (auto it1 = funArgs1.begin(), it2 = funArgs2.begin();
                         it1 != funArgs1.end() && it2 != funArgs2.end();
                         ++it1) {
                        equal.push_back(makeOp("=", it1->name, it2->name));
                        ++it2;
                    }
                    if (SMTGenerationOpts::getInstance().Heap) {
                        std::vector<SortedVar> forallArgs = {
                            SortedVar("i", "Int")};
                        SharedSMTRef heapInEqual =
                            makeOp("=", "HEAP$1", "HEAP$2");
                        equal.push_back(heapInEqual);
                    }
                    body = makeOp("=>", make_shared<Op>("and", equal), body);
                    SharedSMTRef mainInv =
                        make_shared<FunDef>(funName, args, "Bool", body);
                    declarations.push_back(mainInv);
                }
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Stack) {
        declarations.push_back(select_Declaration());
        declarations.push_back(store_Declaration());
    }
    for (auto &fun1 : mod1) {
        if (fun1.isDeclaration() && !fun1.isIntrinsic() &&
            fun1.getName() != "__mark" && fun1.getName() != "__splitmark") {
            auto decls = externFunDecl(fun1, 1);
            declarations.insert(declarations.end(), decls.begin(), decls.end());
        }
    }
    for (auto &fun2 : mod2) {
        if (fun2.isDeclaration() && !fun2.isIntrinsic() &&
            fun2.getName() != "__mark" && fun2.getName() != "__splitmark") {
            auto decls = externFunDecl(fun2, 2);
            declarations.insert(declarations.end(), decls.begin(), decls.end());
        }
    }
}

SMTRef select_Declaration() {
    SharedSMTRef body =
        makeOp("ite", "onStack", makeOp("select", "stack", "pointer"),
               makeOp("select", "heap", "pointer"));
    vector<SortedVar> args = {{"heap", arrayType()},
                              {"stack", arrayType()},
                              {"pointer", "Int"},
                              {"onStack", "Bool"}};
    return make_unique<FunDef>("select_", std::move(args), "Int", body);
}

SMTRef store_Declaration() {
    SharedSMTRef body =
        makeOp("ite", "onStack", makeOp("store", "stack", "pointer", "val"),
               makeOp("store", "heap", "pointer", "val"));
    vector<SortedVar> args = {{"heap", arrayType()},
                              {"stack", arrayType()},
                              {"pointer", "Int"},
                              {"onStack", "Bool"},
                              {"val", "Int"}};
    return make_unique<FunDef>("store_", std::move(args), arrayType(), body);
}

std::set<uint32_t> getVarArgs(llvm::Function &fun) {
    std::set<uint32_t> varArgs;
    for (auto User : fun.users()) {
        if (const auto callInst = llvm::dyn_cast<llvm::CallInst>(User)) {
            varArgs.insert(callInst->getNumArgOperands() -
                           fun.getFunctionType()->getNumParams());
        } else {
            logWarningData("Unsupported use of function\n", *User);
        }
    }
    return varArgs;
}

std::vector<SortedVar> funArgs(llvm::Function &fun, std::string prefix,
                               uint32_t varArgs) {
    std::vector<SortedVar> args;
    int argIndex = 0;
    for (auto &arg : fun.getArgumentList()) {
        if (arg.getName().empty()) {
            arg.setName(prefix + std::to_string(argIndex++));
        }
        args.push_back(SortedVar(arg.getName(), "Int"));
    }
    for (uint32_t i = 0; i < varArgs; ++i) {
        args.push_back(SortedVar("var" + prefix + std::to_string(i), "Int"));
    }
    return args;
}

std::vector<SharedSMTRef> externFunDecl(llvm::Function &fun, int program) {
    std::vector<SharedSMTRef> decls;
    set<uint32_t> varArgs = getVarArgs(fun);
    for (auto argNum : varArgs) {
        std::vector<SortedVar> args = funArgs(fun, "arg_", argNum);
        if (SMTGenerationOpts::getInstance().Heap) {
            args.push_back(SortedVar("HEAP", "(Array Int Int)"));
        }
        args.push_back(SortedVar("res", "Int"));
        if (SMTGenerationOpts::getInstance().Heap) {
            args.push_back(SortedVar("HEAP_res", "(Array Int Int)"));
        }
        std::string funName =
            invariantName(ENTRY_MARK, program == 1 ? ProgramSelection::First
                                                   : ProgramSelection::Second,
                          fun.getName().str(), InvariantAttr::NONE, argNum);
        SharedSMTRef body = stringExpr("true");
        decls.push_back(make_shared<FunDef>(funName, args, "Bool", body));
    }
    return decls;
}

// this does not actually check if the function recurses but the next version of
// llvm provides a function for that and I’m too lazy to implement it myself
bool doesNotRecurse(llvm::Function &fun) {
    for (auto &bb : fun) {
        for (auto &inst : bb) {
            if (const auto callInst = llvm::dyn_cast<llvm::CallInst>(&inst)) {
                const auto calledFun = callInst->getCalledFunction();
                if (calledFun && !calledFun->isDeclaration()) {
                    return false;
                }
            }
        }
    }
    return true;
}

bool doesAccessMemory(const llvm::Module &mod) {
    for (auto &fun : mod) {
        for (auto &bb : fun) {
            for (auto &instr : bb) {
                if (llvm::isa<llvm::LoadInst>(&instr) ||
                    llvm::isa<llvm::StoreInst>(&instr)) {
                    return true;
                }
            }
        }
    }
    return false;
}

vector<SharedSMTRef> globalDeclarationsForMod(int globalPointer,
                                              llvm::Module &mod,
                                              llvm::Module &modOther,
                                              int program) {
    std::vector<SharedSMTRef> declarations;
    for (auto &global1 : mod.globals()) {
        std::string globalName = global1.getName();
        if (!modOther.getNamedGlobal(globalName)) {
            // we want the size of string constants not the size of the pointer
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
            auto constDef1 = make_shared<FunDef>(
                globalName + "$" + std::to_string(program), empty, "Int",
                makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
        }
    }
    return declarations;
}
std::vector<SharedSMTRef> globalDeclarations(llvm::Module &mod1,
                                             llvm::Module &mod2) {
    // First match globals with the same name to make sure that they get the
    // same pointer, then match globals that only exist in one module
    std::vector<SharedSMTRef> declarations;
    int globalPointer = 1;
    for (auto &global1 : mod1.globals()) {
        std::string globalName = global1.getName();
        if (mod2.getNamedGlobal(globalName)) {
            // we want the size of string constants not the size of the pointer
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
                make_shared<FunDef>(globalName + "$1", empty, "Int",
                                    makeOp("-", std::to_string(globalPointer)));
            auto constDef2 =
                make_shared<FunDef>(globalName + "$2", empty, "Int",
                                    makeOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
            declarations.push_back(constDef2);
        }
    }
    auto decls1 = globalDeclarationsForMod(globalPointer, mod1, mod2, 1);
    auto decls2 = globalDeclarationsForMod(globalPointer, mod2, mod1, 2);
    declarations.insert(declarations.end(), decls1.begin(), decls1.end());
    declarations.insert(declarations.end(), decls2.begin(), decls2.end());
    for (auto &global1 : mod1.globals()) {
        global1.setName(global1.getName() + "$1");
    }
    for (auto &global2 : mod2.globals()) {
        global2.setName(global2.getName() + "$2");
    }
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
                               SharedSMTRef body, const llvm::Module &mod1,
                               const llvm::Module &mod2, bool strings,
                               bool additionalIn) {

    vector<SharedSMTRef> args;
    const auto funArgsPair =
        functionArgs(*funs.first, *funs.second)
            .indexedMap<vector<smt::SortedVar>>(
                [](vector<smt::SortedVar> args,
                   int index) -> vector<smt::SortedVar> {
                    if (SMTGenerationOpts::getInstance().Heap) {
                        args.push_back(SortedVar(heapName(index), arrayType()));
                    }
                    if (SMTGenerationOpts::getInstance().Stack) {
                        args.push_back(SortedVar(stackPointerName(index),
                                                 stackPointerType()));
                        args.push_back(
                            SortedVar(stackName(index), arrayType()));
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
        for (const auto &var : args) {
            funArgs.push_back({var.name, getSMTType(var.type)});
        }
    });

    for (auto argPair : makeZip(Args1, Args2)) {
        args.push_back(makeOp("=", argPair.first, argPair.second));
    }
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

    return make_shared<FunDef>("IN_INV", funArgs, "Bool", body);
}

SharedSMTRef outInvariant(MonoPair<vector<smt::SortedVar>> functionArgs,
                          SharedSMTRef body, const llvm::Type *returnType) {
    vector<SortedVar> funArgs = {
        toSMTSortedVar(SortedVar("result$1", llvmTypeToSMTSort(returnType))),
        toSMTSortedVar(SortedVar("result$2", llvmTypeToSMTSort(returnType)))};
    std::sort(functionArgs.first.begin(), functionArgs.first.end());
    std::sort(functionArgs.second.begin(), functionArgs.second.end());
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : functionArgs.first) {
            funArgs.push_back(toSMTSortedVar(arg));
        }
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        funArgs.push_back(SortedVar("HEAP$1", arrayType()));
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : functionArgs.second) {
            funArgs.push_back(toSMTSortedVar(arg));
        }
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        funArgs.push_back(SortedVar("HEAP$2", arrayType()));
    }
    if (body == nullptr) {
        body = makeOp("=", "result$1", "result$2");
        if (SMTGenerationOpts::getInstance().Heap) {
            body = makeOp("and", body, makeOp("=", "HEAP$1", "HEAP$2"));
        }
    }

    return make_shared<FunDef>("OUT_INV", funArgs, "Bool", body);
}

SharedSMTRef initPredicate(shared_ptr<const FunDef> inInv) {

    vector<string> funArgs;
    for (auto var : inInv->args) {
        funArgs.push_back(var.type);
    }

    return make_shared<smt::FunDecl>("INIT", funArgs, "Bool");
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
        ininv_args.push_back(stringExpr(var.name));
        if (var.type == "(Array Int Int)") {
            string newvar = "$i_" + std::to_string(quantified_vars.size());
            quantified_vars.push_back(SortedVar(newvar, "Int"));
            init_args.push_back(makeOp("select", var.name, newvar));
            init_args.push_back(stringExpr(newvar));
        } else {
            init_args.push_back(stringExpr(var.name));
        }
    }

    SharedSMTRef inAppl = std::make_shared<Op>("IN_INV", ininv_args);
    SharedSMTRef initAppl = std::make_shared<Op>("INIT", init_args);

    if (!quantified_vars.empty()) {
        initAppl = std::make_shared<smt::Forall>(quantified_vars, initAppl);
    }
    SharedSMTRef clause = makeOp("=>", inAppl, initAppl);
    auto forall = std::make_shared<smt::Forall>(funDecl->args, clause);

    return make_shared<smt::Assert>(forall);
}
