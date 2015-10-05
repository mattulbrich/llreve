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
#include "llvm/Analysis/LoopInfo.h"
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

#include "example.h"

using namespace clang;
using namespace clang::driver;
using namespace llvm;
using namespace std;

template <int N>
SmallVector<const char *, N> initializeArgs(const char **argv, int argc) {
    SmallVector<const char *, N> args;
    args.push_back(argv[0]);            // add executable name
    args.push_back("-xc");              // force language to C
    args.append(argv + 1, argv + argc); // add remaining args
    args.push_back("-fsyntax-only");    // don't do more work than necessary
    return args;
}

unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<DiagnosticOptions> diagOpts =
        new DiagnosticOptions();
    auto diagClient = new TextDiagnosticPrinter(llvm::errs(), &*diagOpts);
    const IntrusiveRefCntPtr<DiagnosticIDs> diagID(new DiagnosticIDs());
    return std::make_unique<DiagnosticsEngine>(diagID, &*diagOpts, diagClient);
}

unique_ptr<Driver> initializeDriver(DiagnosticsEngine &Diags) {
    std::string tripleStr = llvm::sys::getProcessTriple();
    llvm::Triple triple(tripleStr);
    auto driver =
        std::make_unique<Driver>("/usr/bin/clang", triple.str(), Diags);
    driver->setTitle("clang/llvm example");
    driver->setCheckInputsExist(false);
    return driver;
}

ErrorOr<const driver::Command &> getCmd(Compilation &Comp,
                                        DiagnosticsEngine &Diags) {
    const driver::JobList &jobs = Comp.getJobs();

    // there should be only one job
    if (jobs.size() != 1) {
        SmallString<256> Msg;
        llvm::raw_svector_ostream OS(Msg);
        jobs.Print(OS, "; ", true);
        Diags.Report(diag::err_fe_expected_compiler_job) << OS.str();
        return ErrorOr<const driver::Command &>(error_code());
    }

    const driver::Command &Cmd = cast<driver::Command>(*jobs.begin());
    if (StringRef(Cmd.getCreator().getName()) != "clang") {
        Diags.Report(diag::err_fe_expected_clang_command);
        return ErrorOr<const driver::Command &>(error_code());
    }
    return makeErrorOr(Cmd);
}

template <typename T> ErrorOr<T> makeErrorOr(T Arg) {
    return ErrorOr<T>(Arg);
}

int main(int argc, const char **argv) {
    auto diags = initializeDiagnostics();
    auto driver = initializeDriver(*diags);
    auto args = initializeArgs<16>(argv, argc);

    std::unique_ptr<Compilation> comp(driver->BuildCompilation(args));
    if (!comp) {
        return 1;
    }

    auto CmdOrError = getCmd(*comp, *diags);
    if (!CmdOrError) {
        return 1;
    }
    auto Cmd = CmdOrError.get();

    const driver::ArgStringList &CCArgs = Cmd.getArguments();
    std::unique_ptr<CompilerInvocation> CI(new CompilerInvocation);
    CompilerInvocation::CreateFromArgs(
        *CI, const_cast<const char **>(CCArgs.data()),
        const_cast<const char **>(CCArgs.data()) + CCArgs.size(), *diags);

    // Create a compiler instance to handle the actual work.
    CompilerInstance Clang;
    Clang.setInvocation(CI.release());

    // Create the compilers actual diagnostics engine.
    Clang.createDiagnostics();
    if (!Clang.hasDiagnostics()) {
        cout << "Couldn't enable diagnostics\n";
        return 1;
    }

    // Create and execute the frontend to generate an LLVM bitcode module.
    std::unique_ptr<CodeGenAction> act(new EmitLLVMOnlyAction());
    if (!Clang.ExecuteAction(*act)) {
        cout << "Couldn't execute action\n";
        return 1;
    }

    unique_ptr<llvm::Module> mod = act->takeModule();
    if (!mod) {
        cerr << "Error taking module\n";
        return 1;
    }

    ErrorOr<llvm::Function &> funOrError = getFunction(*mod);
    if (!funOrError) {
        errs() << "Couldn't find a function\n";
        return 1;
    }

    doAnalysis(funOrError.get());

    llvm::llvm_shutdown();

    return 0;
}

void doAnalysis(llvm::Function &fun) {
    FunctionAnalysisManager fam(true); // enable debug log
    fam.registerPass(DominatorTreeAnalysis());
    fam.registerPass(LoopAnalysis());

    FunctionPassManager fpm(true); // enable debug log

    fpm.addPass(PrintFunctionPass(errs())); // dump function
    auto results = fpm.run(fun, &fam);

    fam.getResult<LoopAnalysis>(fun).print(errs());
}

ErrorOr<Function &> getFunction(llvm::Module &mod) {
    if (mod.getFunctionList().size() == 0) {
        return ErrorOr<Function &>(error_code());
    }
    Function &fun = mod.getFunctionList().front();
    if (mod.getFunctionList().size() > 1) {
        llvm::errs() << "Warning: There is more than one function in the "
                        "module, choosing “"
                     << fun.getName() << "”\n";
    }
    return ErrorOr<Function &>(fun);
}
