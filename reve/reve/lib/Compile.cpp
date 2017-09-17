/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Compile.h"

#include "Helper.h"

#include "clang/Driver/Compilation.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"

using clang::CodeGenAction;
using clang::CompilerInstance;
using clang::CompilerInvocation;
using clang::DiagnosticsEngine;
using clang::driver::Compilation;
using clang::driver::Driver;
using clang::driver::JobList;
using llvm::ErrorOr;
using llvm::IntrusiveRefCntPtr;
using llvm::opt::ArgStringList;
using std::shared_ptr;
using std::string;
using std::unique_ptr;

using namespace llreve::opts;

MonoPair<unique_ptr<llvm::Module>>
compileToModules(const char *exeName, InputOpts &opts,
                 std::pair<CodeGenAction &, CodeGenAction &> actions) {
    executeCodeGenActions(exeName, opts, actions);

    unique_ptr<llvm::Module> mod1 = actions.first.takeModule();
    unique_ptr<llvm::Module> mod2 = actions.second.takeModule();
    if (!mod1 || !mod2) {
        logError("Module was not successful\n");
        exit(1);
    }
    return {std::move(mod1), std::move(mod2)};
}

/// Compile the inputs to llvm assembly and return the corresponding
/// CodeGenActions
void executeCodeGenActions(
    const char *exeName, InputOpts &opts,
    std::pair<CodeGenAction &, CodeGenAction &> actions) {
    auto diags = initializeDiagnostics();
    auto driver = initializeDriver(*diags);
    auto args = initializeArgs(exeName, opts);

    unique_ptr<Compilation> comp(driver->BuildCompilation(args));
    if (!comp) {
        logError("Couldn’t initiate compilation\n");
        exit(1);
    }

    auto cmdArgsOrError = getCmd(*comp, *diags);
    if (!cmdArgsOrError) {
        logError("Couldn’t get cmd args\n");
        exit(1);
    }
    auto cmdArgs = cmdArgsOrError.get();

    executeCodeGenAction(cmdArgs.first, *diags, actions.first);
    executeCodeGenAction(cmdArgs.second, *diags, actions.second);
}

static ArgStringList filterCC1Args(const ArgStringList &ccArgs) {
    ArgStringList newCcArgs;
    llvm::StringSet<> ignoredArgs = {"-discard-value-names"};
    for (auto &arg : ccArgs) {
        if (ignoredArgs.find(arg) == ignoredArgs.end()) {
            newCcArgs.push_back(arg);
        }
    }
    return newCcArgs;
}

/// Build the CodeGenAction corresponding to the arguments
void executeCodeGenAction(const ArgStringList &ccArgs,
                          clang::DiagnosticsEngine &diags, CodeGenAction &act) {
    ArgStringList filteredCcArgs = filterCC1Args(ccArgs);
    auto ci = std::make_unique<CompilerInvocation>();
    CompilerInvocation::CreateFromArgs(
        *ci, filteredCcArgs.data(),
        filteredCcArgs.data() + filteredCcArgs.size(), diags);
    ci->getFrontendOpts().DisableFree = false;
    CompilerInstance clang;
    clang.setInvocation(std::move(ci));
    clang.createDiagnostics();
    if (!clang.hasDiagnostics()) {
        logError("Couldn’t enable diagnostics\n");
        exit(1);
    }
    if (!clang.ExecuteAction(act)) {
        logError("Couldn’t execute action\n");
        exit(1);
    }
}

/// Initialize the argument vector to produce the llvm assembly for
/// the two C files
std::vector<const char *> initializeArgs(const char *exeName, InputOpts &opts) {
    std::vector<const char *> args;
    args.push_back(exeName); // add executable name
    args.push_back("-xc");   // force language to C
    args.push_back("-std=c99");

    if (!opts.Includes.empty()) {
        for (string &value : opts.Includes) {
            args.push_back("-I");
            args.push_back(value.c_str());
        }
    }
    if (!opts.ResourceDir.empty()) {
        args.push_back("-resource-dir");
        args.push_back(opts.ResourceDir.c_str());
    }
    args.push_back(opts.FileNames.first.c_str());  // add input file
    args.push_back(opts.FileNames.second.c_str()); // add input file
    args.push_back("-fsyntax-only"); // don't do more work than necessary
    return args;
}

/// Set up the diagnostics engine
unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts =
        new clang::DiagnosticOptions();
    auto diagClient =
        new clang::TextDiagnosticPrinter(llvm::errs(), &*diagOpts);
    const IntrusiveRefCntPtr<clang::DiagnosticIDs> diagId(
        new clang::DiagnosticIDs());
    return std::make_unique<DiagnosticsEngine>(diagId, &*diagOpts, diagClient);
}

/// Initialize the driver
unique_ptr<Driver> initializeDriver(DiagnosticsEngine &diags) {
    string tripleStr = llvm::sys::getProcessTriple();
    llvm::Triple triple(tripleStr);
    auto driver =
        std::make_unique<clang::driver::Driver>("clang", triple.str(), diags);
    driver->setTitle("reve");
    driver->setCheckInputsExist(false);
    // Builtin includes may not be found, a possible but bad solution would be
    // to hardcode them:
    // driver->ResourceDir =
    // "/usr/local/stow/clang-3.8.0/bin/../lib/clang/3.8.0";
    // To find the correct path on linux the following comand can be used:
    // clang '-###' -c foo.c 2>&1 | tr ' ' '\n' | grep -A1 resource
    return driver;
}

/// This creates the compilations commands to compile to assembly
ErrorOr<MonoPair<ArgStringList>> getCmd(Compilation &comp,
                                        DiagnosticsEngine &diags) {
    const JobList &jobs = comp.getJobs();

    // there should be exactly two jobs
    if (jobs.size() != 2) {
        llvm::SmallString<256> msg;
        llvm::raw_svector_ostream os(msg);
        jobs.Print(os, "; ", true);
        diags.Report(clang::diag::err_fe_expected_compiler_job) << os.str();
        return ErrorOr<MonoPair<ArgStringList>>(std::error_code());
    }

    return makeErrorOr(makeMonoPair(jobs.begin()->getArguments(),
                                    std::next(jobs.begin())->getArguments()));
}

/// Wrapper function to allow inferenece of template parameters
template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }
