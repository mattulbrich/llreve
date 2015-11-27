#include "Reve.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "PathAnalysis.h"
#include "RemoveMarkPass.h"
#include "SExpr.h"
#include "SMT.h"
#include "SMTGeneration.h"
#include "UnifyFunctionExitNodes.h"
#include "UniqueNamePass.h"

#include "clang/Driver/Compilation.h"
#include "clang/Driver/Driver.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"

#include "llvm/ADT/SmallString.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include <fstream>
#include <iostream>
#include <tuple>

using clang::CodeGenAction;
using clang::CompilerInstance;
using clang::CompilerInvocation;
using clang::DiagnosticsEngine;

using clang::driver::ArgStringList;
using clang::driver::Command;
using clang::driver::Compilation;
using clang::driver::Driver;
using clang::driver::JobList;

using llvm::CmpInst;
using llvm::ErrorOr;
using llvm::errs;
using llvm::Instruction;
using llvm::IntrusiveRefCntPtr;

using std::unique_ptr;
using std::make_shared;
using std::string;
using std::placeholders::_1;

static llvm::cl::opt<string> FileName1(llvm::cl::Positional,
                                       llvm::cl::desc("Input file 1"),
                                       llvm::cl::Required);
static llvm::cl::opt<string> FileName2(llvm::cl::Positional,
                                       llvm::cl::desc("Input file 2"),
                                       llvm::cl::Required);
static llvm::cl::opt<string>
    OutputFileName("o", llvm::cl::desc("SMT output filename"),
                   llvm::cl::value_desc("filename"));
static llvm::cl::opt<bool> ShowCFG("show-cfg", llvm::cl::desc("Show cfg"));
static llvm::cl::opt<bool>
    OffByN("off-by-n", llvm::cl::desc("Allow loops to be off by n iterations"));
static llvm::cl::opt<bool>
    OnlyRec("only-rec", llvm::cl::desc("Only generate recursive invariants"));
static llvm::cl::opt<bool> Heap("heap", llvm::cl::desc("Enable heaps"));

/// Initialize the argument vector to produce the llvm assembly for
/// the two C files
template <int N>
llvm::SmallVector<const char *, N>
initializeArgs(const char *ExeName, string Input1, string Input2) {
    llvm::SmallVector<const char *, N> Args;
    Args.push_back(ExeName);        // add executable name
    Args.push_back("-xc");          // force language to C
    Args.push_back(Input1.c_str()); // add input file
    Args.push_back(Input2.c_str());
    Args.push_back("-fsyntax-only"); // don't do more work than necessary
    return Args;
}

/// Set up the diagnostics engine
unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<clang::DiagnosticOptions> DiagOpts =
        new clang::DiagnosticOptions();
    auto DiagClient =
        new clang::TextDiagnosticPrinter(llvm::errs(), &*DiagOpts);
    const IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(
        new clang::DiagnosticIDs());
    return llvm::make_unique<DiagnosticsEngine>(DiagID, &*DiagOpts, DiagClient);
}

/// Initialize the driver
unique_ptr<Driver> initializeDriver(DiagnosticsEngine &Diags) {
    string TripleStr = llvm::sys::getProcessTriple();
    llvm::Triple Triple(TripleStr);
    // TODO(moritz): Find the correct path instead of hardcoding it
    auto Driver = llvm::make_unique<clang::driver::Driver>("/usr/bin/clang",
                                                           Triple.str(), Diags);
    Driver->setTitle("reve");
    Driver->setCheckInputsExist(false);
    return Driver;
}

/// This creates the compilations commands to compile to assembly
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

/// Wrapper function to allow inferenece of template parameters
template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }

/// Compile the inputs to llvm assembly and return those modules
std::tuple<unique_ptr<clang::CodeGenAction>, unique_ptr<clang::CodeGenAction>>
getModule(const char *ExeName, string Input1, string Input2) {
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

    auto Act1 = getCodeGenAction(std::get<0>(CmdArgs), *Diags);
    auto Act2 = getCodeGenAction(std::get<1>(CmdArgs), *Diags);
    if (!Act1 || !Act2) {
        return std::make_tuple(nullptr, nullptr);
    }

    return std::make_tuple(std::move(Act1), std::move(Act2));
}

/// Build the CodeGenAction corresponding to the arguments
std::unique_ptr<CodeGenAction>
getCodeGenAction(const ArgStringList &CCArgs, clang::DiagnosticsEngine &Diags) {
    auto CI = llvm::make_unique<CompilerInvocation>();
    CompilerInvocation::CreateFromArgs(*CI, (CCArgs.data()),
                                       (CCArgs.data()) + CCArgs.size(), Diags);
    CompilerInstance Clang;
    Clang.setInvocation(CI.release());
    Clang.createDiagnostics();
    if (!Clang.hasDiagnostics()) {
        std::cerr << "Couldn't enable diagnostics\n";
        return nullptr;
    }
    std::unique_ptr<CodeGenAction> Act =
        llvm::make_unique<clang::EmitLLVMOnlyAction>();
    if (!Clang.ExecuteAction(*Act)) {
        std::cerr << "Couldn't execute action\n";
        return nullptr;
    }
    return Act;
}

std::pair<SMTRef, SMTRef> parseInOutInvs(std::string FileName1,
                                         std::string FileName2) {
    SMTRef In = nullptr;
    SMTRef Out = nullptr;
    std::ifstream InFile1(FileName1);
    if (InFile1.is_open()) {
        string Line1;
        getline(InFile1, Line1);
        processLine(Line1, In, Out);
        string Line2;
        getline(InFile1, Line2);
        processLine(Line2, In, Out);
    }
    std::ifstream InFile2(FileName2);
    if (InFile2.is_open()) {
        string Line1;
        getline(InFile2, Line1);
        processLine(Line1, In, Out);
        string Line2;
        getline(InFile2, Line2);
        processLine(Line2, In, Out);
    }

    return std::make_pair(In, Out);
}

void processLine(std::string Line, SMTRef &In, SMTRef &Out) {
    if (Line.length() > 4) {
        if (Line.substr(4, 6) == "rel_in" && In == nullptr) {
            In = name(Line.substr(11, Line.length() - 11 - 4));
        }
        if (Line.substr(4, 7) == "rel_out" && Out == nullptr) {
            In = name(Line.substr(12, Line.length() - 12 - 4));
        }
    }
}

int main(int Argc, const char **Argv) {
    // The actual arguments are declared statically so we don't need
    // to pass those in here
    llvm::cl::ParseCommandLineOptions(Argc, Argv, "reve\n");

    auto ActTuple = getModule(Argv[0], FileName1, FileName2);
    const auto Act1 = std::move(std::get<0>(ActTuple));
    const auto Act2 = std::move(std::get<1>(ActTuple));
    if (!Act1 || !Act2) {
        return 1;
    }

    const auto Mod1 = Act1->takeModule();
    const auto Mod2 = Act2->takeModule();
    if (!Mod2 || !Mod2) {
        return 1;
    }

    ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>> Funs =
        zipFunctions(*Mod1, *Mod2);

    if (!Funs) {
        errs() << "Couldn't find matching functions\n";
        return 1;
    }

    std::vector<SMTRef> Declarations;
    std::vector<SMTRef> Assertions;
    std::vector<SMTRef> SMTExprs;
    SMTExprs.push_back(std::make_shared<SetLogic>("HORN"));

    std::pair<SMTRef, SMTRef> InOutInvs = parseInOutInvs(FileName1, FileName2);

    bool Main = true;
    for (auto FunPair : Funs.get()) {
        auto Fam1 = preprocessModule(*FunPair.first, "1");
        auto Fam2 = preprocessModule(*FunPair.second, "2");
        if (Main) {
            SMTExprs.push_back(inInvariant(*FunPair.first, *FunPair.second,
                                           InOutInvs.first, Heap));
            SMTExprs.push_back(outInvariant(InOutInvs.second, Heap));
            auto NewSMTExprs =
                mainAssertion(*FunPair.first, *FunPair.second, Fam1, Fam2,
                              OffByN, Declarations, OnlyRec, Heap);
            Assertions.insert(Assertions.end(), NewSMTExprs.begin(),
                              NewSMTExprs.end());
            Main = false;
        }
        auto NewSMTExprs = convertToSMT(*FunPair.first, *FunPair.second, Fam1,
                                        Fam2, OffByN, Declarations, Heap);
        Assertions.insert(Assertions.end(), NewSMTExprs.begin(),
                          NewSMTExprs.end());
    }
    SMTExprs.insert(SMTExprs.end(), Declarations.begin(), Declarations.end());
    SMTExprs.insert(SMTExprs.end(), Assertions.begin(), Assertions.end());
    SMTExprs.push_back(make_shared<CheckSat>());
    SMTExprs.push_back(make_shared<GetModel>());

    // write to file or to stdout
    std::streambuf *Buf;
    std::ofstream OFStream;

    if (!OutputFileName.empty()) {
        OFStream.open(OutputFileName);
        Buf = OFStream.rdbuf();
    } else {
        Buf = std::cout.rdbuf();
    }

    std::ostream OutFile(Buf);

    for (auto &SMT : SMTExprs) {
        OutFile << *SMT->compressLets()->toSExpr();
        OutFile << "\n";
    }

    if (!OutputFileName.empty()) {
        OFStream.close();
    }

    llvm::llvm_shutdown();

    return 0;
}

shared_ptr<llvm::FunctionAnalysisManager> preprocessModule(llvm::Function &Fun,
                                                           string Prefix) {
    llvm::PassBuilder PB;
    auto FAM =
        make_shared<llvm::FunctionAnalysisManager>(true); // enable debug log
    PB.registerFunctionAnalyses(*FAM); // register basic analyses
    FAM->registerPass(MarkAnalysis());
    FAM->registerPass(UnifyFunctionExitNodes());
    FAM->registerPass(PathAnalysis());

    llvm::FunctionPassManager FPM(true); // enable debug log

    FPM.addPass(AnnotStackPass()); // annotate load/store of stack variables
    FPM.addPass(PromotePass());    // mem2reg
    // FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(UniqueNamePass(Prefix)); // prefix register names
    FPM.addPass(RemoveMarkPass());
    if (ShowCFG) {
        FPM.addPass(CFGViewerPass()); // show cfg
    }
    FPM.addPass(llvm::VerifierPass());
    FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    FPM.run(Fun, FAM.get());

    return FAM;
}

ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>
zipFunctions(llvm::Module &Mod1, llvm::Module &Mod2) {
    std::vector<std::pair<llvm::Function *, llvm::Function *>> Funs;
    if (Mod1.size() != Mod2.size()) {
        llvm::errs() << "Error: unequal number of functions\n";
        return ErrorOr<
            std::vector<std::pair<llvm::Function *, llvm::Function *>>>(
            std::error_code());
    }
    for (auto &Fun1 : Mod1) {
        if (Fun1.isDeclaration()) {
            continue;
        }
        auto Fun2 = Mod2.getFunction(Fun1.getName());
        if (!Fun2) {
            llvm::errs() << "Error: no corresponding function for "
                         << Fun1.getName() << "\n";
            return ErrorOr<
                std::vector<std::pair<llvm::Function *, llvm::Function *>>>(
                std::error_code());
        }
        Funs.push_back(std::make_pair(&Fun1, Fun2));
    }
    return ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>(
        Funs);
}
