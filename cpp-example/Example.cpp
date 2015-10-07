#include <iostream>
#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Driver/Compilation.h"
#include "clang/Driver/Driver.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include "Example.h"
#include "UniqueNamePass.h"

using clang::CodeGenAction;
using clang::CompilerInstance;
using clang::CompilerInvocation;
using clang::DiagnosticsEngine;

using clang::driver::ArgStringList;
using clang::driver::Command;
using clang::driver::Compilation;
using clang::driver::Driver;
using clang::driver::JobList;

using llvm::ErrorOr;
using llvm::errs;
using llvm::IntrusiveRefCntPtr;

using std::unique_ptr;

static llvm::cl::opt<std::string> FileName(llvm::cl::Positional,
                                           llvm::cl::desc("Input file"),
                                           llvm::cl::Required);

template <int N>
llvm::SmallVector<const char *, N> initializeArgs(const char *ExeName,
                                                  std::string Input) {
    llvm::SmallVector<const char *, N> Args;
    Args.push_back(ExeName);         // add executable name
    Args.push_back("-xc");           // force language to C
    Args.push_back(Input.c_str());   // add input file
    Args.push_back("-fsyntax-only"); // don't do more work than necessary
    return Args;
}

unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts =
        new clang::DiagnosticOptions();
    auto diagClient =
        new clang::TextDiagnosticPrinter(llvm::errs(), &*diagOpts);
    const IntrusiveRefCntPtr<clang::DiagnosticIDs> diagID(
        new clang::DiagnosticIDs());
    return std::make_unique<DiagnosticsEngine>(diagID, &*diagOpts, diagClient);
}

unique_ptr<Driver> initializeDriver(DiagnosticsEngine &Diags) {
    std::string TripleStr = llvm::sys::getProcessTriple();
    llvm::Triple Triple(TripleStr);
    auto Driver = std::make_unique<clang::driver::Driver>("/usr/bin/clang",
                                                          Triple.str(), Diags);
    Driver->setTitle("clang/llvm example");
    Driver->setCheckInputsExist(false);
    return Driver;
}

ErrorOr<const Command &> getCmd(Compilation &Comp, DiagnosticsEngine &Diags) {
    const JobList &Jobs = Comp.getJobs();

    // there should be only one job
    if (Jobs.size() != 1) {
        llvm::SmallString<256> Msg;
        llvm::raw_svector_ostream OS(Msg);
        Jobs.Print(OS, "; ", true);
        Diags.Report(clang::diag::err_fe_expected_compiler_job) << OS.str();
        return ErrorOr<const Command &>(std::error_code());
    }

    const Command &Cmd = llvm::cast<Command>(*Jobs.begin());
    if (StringRef(Cmd.getCreator().getName()) != "clang") {
        Diags.Report(clang::diag::err_fe_expected_clang_command);
        return ErrorOr<const Command &>(std::error_code());
    }
    return makeErrorOr(Cmd);
}

template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }

unique_ptr<clang::CodeGenAction> getModule(const char *ExeName,
                                           std::string Input) {
    auto Diags = initializeDiagnostics();
    auto Driver = initializeDriver(*Diags);
    auto Args = initializeArgs<16>(ExeName, Input);

    std::unique_ptr<Compilation> Comp(Driver->BuildCompilation(Args));
    if (!Comp) {
        return nullptr;
    }

    auto CmdOrError = getCmd(*Comp, *Diags);
    if (!CmdOrError) {
        return nullptr;
    }
    auto Cmd = CmdOrError.get();

    const ArgStringList &CCArgs = Cmd.getArguments();
    auto CI = std::make_unique<CompilerInvocation>();
    CompilerInvocation::CreateFromArgs(
        *CI, const_cast<const char **>(CCArgs.data()),
        const_cast<const char **>(CCArgs.data()) + CCArgs.size(), *Diags);

    // Create a compiler instance to handle the actual work.
    CompilerInstance Clang;
    Clang.setInvocation(CI.release());

    // Create the compilers actual diagnostics engine.
    Clang.createDiagnostics();
    if (!Clang.hasDiagnostics()) {
        std::cout << "Couldn't enable diagnostics\n";
        return nullptr;
    }

    std::unique_ptr<CodeGenAction> Act =
        std::make_unique<clang::EmitLLVMOnlyAction>();

    if (!Clang.ExecuteAction(*Act)) {
        std::cout << "Couldn't execute action\n";
        return nullptr;
    }
    return Act;
}

int main(int Argc, const char **Argv) {
    llvm::cl::ParseCommandLineOptions(Argc, Argv, "reve\n");

    auto Act = getModule(Argv[0], FileName);
    if (!Act) {
        return 1;
    }

    auto Mod = Act->takeModule();
    if (!Mod) {
        return 1;
    }

    ErrorOr<llvm::Function &> FunOrError = getFunction(*Mod);
    if (!FunOrError) {
        errs() << "Couldn't find a function\n";
        return 1;
    }

    doAnalysis(FunOrError.get());

    llvm::llvm_shutdown();

    return 0;
}

void doAnalysis(llvm::Function &Fun) {
    llvm::FunctionAnalysisManager Fam(true); // enable debug log
    Fam.registerPass(llvm::DominatorTreeAnalysis());
    Fam.registerPass(llvm::LoopAnalysis());
    Fam.registerPass(llvm::TargetIRAnalysis());
    Fam.registerPass(llvm::AssumptionAnalysis());

    llvm::FunctionPassManager Fpm(true); // enable debug log

    Fpm.addPass(llvm::PrintFunctionPass(errs())); // dump function
    Fpm.addPass(llvm::SimplifyCFGPass());
    Fpm.addPass(llvm::PrintFunctionPass(errs()));
    Fpm.addPass(UniqueNamePass());
    Fpm.addPass(llvm::PrintFunctionPass(errs()));
    Fpm.run(Fun, &Fam);

    Fam.getResult<llvm::LoopAnalysis>(Fun).print(errs());
}

ErrorOr<llvm::Function &> getFunction(llvm::Module &Mod) {
    if (Mod.getFunctionList().size() == 0) {
        return ErrorOr<llvm::Function &>(std::error_code());
    }
    llvm::Function &Fun = Mod.getFunctionList().front();
    if (Mod.getFunctionList().size() > 1) {
        llvm::errs() << "Warning: There is more than one function in the "
                        "module, choosing “"
                     << Fun.getName() << "”\n";
    }
    return ErrorOr<llvm::Function &>(Fun);
}
