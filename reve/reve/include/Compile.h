/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "MonoPair.h"
#include "Opts.h"

#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Driver.h"
#include "llvm/IR/Module.h"
#include "llvm/Option/Option.h"

/// compiles the input files to llvm modules
/// \param exeName should be argv[0] in most cases
/// This calls exit internally if it is not successful
/// IMPORTANT: The lifetime of the module is tied to the lifetime of the
/// codegenactions, so make sure they stay alive if you don’t want to spend
/// hours debugging really weird segfaults.
auto compileToModules(const char *exeName, InputOpts &opts,
                      MonoPair<std::shared_ptr<clang::CodeGenAction>> acts)
    -> MonoPair<std::unique_ptr<llvm::Module>>;
auto executeCodeGenActions(const char *exeName, InputOpts &opts,
                           MonoPair<std::shared_ptr<clang::CodeGenAction>> acts)
    -> void;
auto executeCodeGenAction(const llvm::opt::ArgStringList &ccArgs,
                          clang::DiagnosticsEngine &diags,
                          std::shared_ptr<clang::CodeGenAction> act) -> void;
auto initializeArgs(const char *exeName, InputOpts &opts)
    -> std::vector<const char *>;
auto initializeDiagnostics(void) -> std::unique_ptr<clang::DiagnosticsEngine>;
auto initializeDriver(clang::DiagnosticsEngine &diags)
    -> std::unique_ptr<clang::driver::Driver>;
auto getCmd(clang::driver::Compilation &comp, clang::DiagnosticsEngine &diags)
    -> llvm::ErrorOr<MonoPair<llvm::opt::ArgStringList>>;
template <typename T> auto makeErrorOr(T Arg) -> llvm::ErrorOr<T>;
