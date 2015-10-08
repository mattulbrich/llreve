#include <iostream>
#include <tuple>

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
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include "AnnotStackPass.h"
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

static llvm::cl::opt<std::string> FileName1(llvm::cl::Positional,
                                            llvm::cl::desc("Input file 1"),
                                            llvm::cl::Required);
static llvm::cl::opt<std::string> FileName2(llvm::cl::Positional,
                                            llvm::cl::desc("Input file 2"),
                                            llvm::cl::Required);

template <int N>
llvm::SmallVector<const char *, N>
initializeArgs(const char *ExeName, std::string Input1, std::string Input2) {
    llvm::SmallVector<const char *, N> Args;
    Args.push_back(ExeName);        // add executable name
    Args.push_back("-xc");          // force language to C
    Args.push_back(Input1.c_str()); // add input file
    Args.push_back(Input2.c_str());
    Args.push_back("-fsyntax-only"); // don't do more work than necessary
    return Args;
}

unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts =
        new clang::DiagnosticOptions();
    auto  diagClient =
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

ErrorOr<std::tuple<ArgStringList, ArgStringList>>
getCmd(Compilation &Comp, DiagnosticsEngine &Diags) {
    const JobList &Jobs = Comp.getJobs();

    // there should be exactly two jobs
    if (Jobs.size() != 2) {
        llvm::SmallString<256> Msg;
        llvm::raw_svector_ostream OS(Msg);
        Jobs.Print(OS, "; ", true);
        Diags.Report(clang::diag::err_fe_expected_compiler_job) << OS.str();
        return ErrorOr<std::tuple<ArgStringList, ArgStringList>>(
            std::error_code());
    }

    std::vector<ArgStringList> Args;
    for (auto &Cmd : Jobs) {
        Args.push_back(Cmd.getArguments());
    }

    return makeErrorOr(std::make_tuple(
        Jobs.begin()->getArguments(), std::next(Jobs.begin())->getArguments()));
}

template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }

std::tuple<unique_ptr<clang::CodeGenAction>, unique_ptr<clang::CodeGenAction>>
getModule(const char *ExeName, std::string Input1, std::string Input2) {
    auto Diags = initializeDiagnostics();
    auto Driver = initializeDriver(*Diags);
    auto Args = initializeArgs<16>(ExeName, Input1, Input2);

    std::unique_ptr<Compilation> Comp(Driver->BuildCompilation(Args));
    if (!Comp) {
        return std::make_tuple(nullptr, nullptr);
    }

    auto CmdArgsOrError = getCmd(*Comp, *Diags);
    if (!CmdArgsOrError) {
        return std::make_tuple(nullptr, nullptr);
    }
    auto CmdArgs = CmdArgsOrError.get();

    auto Act1 = getAction(std::get<0>(CmdArgs), *Diags);
    auto Act2 = getAction(std::get<1>(CmdArgs), *Diags);
    if (!Act1 || !Act2) {
        return std::make_tuple(nullptr, nullptr);
    }

    return std::make_tuple(std::move(Act1), std::move(Act2));
}

std::unique_ptr<CodeGenAction> getAction(const ArgStringList &CCArgs,
                                         clang::DiagnosticsEngine &Diags) {
    auto CI = std::make_unique<CompilerInvocation>();
    CompilerInvocation::CreateFromArgs(
        *CI, const_cast<const char **>(CCArgs.data()),
        const_cast<const char **>(CCArgs.data()) + CCArgs.size(), Diags);
    CompilerInstance Clang;
    Clang.setInvocation(CI.release());
    Clang.createDiagnostics();
    if (!Clang.hasDiagnostics()) {
        std::cerr << "Couldn't enable diagnostics\n";
        return nullptr;
    }
    std::unique_ptr<CodeGenAction> Act =
        std::make_unique<clang::EmitLLVMOnlyAction>();
    if (!Clang.ExecuteAction(*Act)) {
        std::cerr << "Couldn't execute action\n";
        return nullptr;
    }
    return Act;
}

int main(int Argc, const char **Argv) {
    llvm::cl::ParseCommandLineOptions(Argc, Argv, "reve\n");

    auto ActTuple = getModule(Argv[0], FileName1, FileName2);
    auto Act1 = std::move(std::get<0>(ActTuple));
    auto Act2 = std::move(std::get<1>(ActTuple));
    if (!Act1 || !Act2) {
        return 1;
    }

    auto Mod1 = Act1->takeModule();
    auto Mod2 = Act2->takeModule();
    if (!Mod1 || !Mod2) {
        return 1;
    }

    ErrorOr<llvm::Function &> FunOrError1 = getFunction(*Mod1);
    ErrorOr<llvm::Function &> FunOrError2 = getFunction(*Mod2);

    if (!FunOrError1 || !FunOrError2) {
        errs() << "Couldn't find a function\n";
        return 1;
    }

    doAnalysis(FunOrError1.get());
    doAnalysis(FunOrError2.get());

    llvm::llvm_shutdown();

    return 0;
}

void doAnalysis(llvm::Function &Fun) {
    llvm::FunctionAnalysisManager Fam(true); // enable debug log
    Fam.registerPass(llvm::DominatorTreeAnalysis());
    Fam.registerPass(llvm::LoopAnalysis());

    llvm::FunctionPassManager Fpm(true); // enable debug log

    Fpm.addPass(UniqueNamePass("1___")); // prefix register names
    Fpm.addPass(AnnotStackPass()); // annotate load/store of stack variables
    Fpm.addPass(llvm::PrintFunctionPass(errs())); // dump function
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
