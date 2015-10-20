#include "Reve.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "Mem2Reg.h"
#include "SExpr.h"
#include "SMT.h"
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
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

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
using std::string;

static llvm::cl::opt<std::string> FileName1(llvm::cl::Positional,
                                            llvm::cl::desc("Input file 1"),
                                            llvm::cl::Required);
static llvm::cl::opt<std::string> FileName2(llvm::cl::Positional,
                                            llvm::cl::desc("Input file 2"),
                                            llvm::cl::Required);

/// Initialize the argument vector to produce the llvm assembly for
/// the two C files
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
    std::string TripleStr = llvm::sys::getProcessTriple();
    llvm::Triple Triple(TripleStr);
    // TODO: Find the correct path instead of hardcoding it
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

int main(int Argc, const char **Argv) {
    // The actual arguments are declared statically so we don't need
    // to pass those in here
    llvm::cl::ParseCommandLineOptions(Argc, Argv, "reve\n");

    auto ActTuple = getModule(Argv[0], FileName1, FileName2);
    const auto Act_1 = std::move(std::get<0>(ActTuple));
    const auto Act_2 = std::move(std::get<1>(ActTuple));
    if (!Act_1 || !Act_2) {
        return 1;
    }

    const auto Mod_1 = Act_1->takeModule();
    const auto Mod_2 = Act_2->takeModule();
    if (!Mod_2 || !Mod_2) {
        return 1;
    }

    ErrorOr<llvm::Function &> FunOrError_1 = getFunction(*Mod_1);
    ErrorOr<llvm::Function &> FunOrError_2 = getFunction(*Mod_2);

    if (!FunOrError_1 || !FunOrError_2) {
        errs() << "Couldn't find a function\n";
        return 1;
    }

    auto FAM_1 = preprocessModule(FunOrError_1.get(), "1");
    auto FAM_2 = preprocessModule(FunOrError_2.get(), "2");

    convertToSMT(FunOrError_1.get(), FunOrError_2.get(), std::move(FAM_1),
                 std::move(FAM_2));

    llvm::llvm_shutdown();

    return 0;
}

unique_ptr<llvm::FunctionAnalysisManager> preprocessModule(llvm::Function &Fun,
                                                           std::string Prefix) {
    llvm::PassBuilder PB;
    auto FAM = llvm::make_unique<llvm::FunctionAnalysisManager>(
        true);                         // enable debug log
    PB.registerFunctionAnalyses(*FAM); // register basic analyses

    llvm::FunctionPassManager FPM(true); // enable debug log

    FPM.addPass(AnnotStackPass()); // annotate load/store of stack variables
    FPM.addPass(PromotePass());    // mem2reg
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(UniqueNamePass(Prefix)); // prefix register names
    FPM.addPass(llvm::VerifierPass());
    FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    // FPM.addPass(CFGViewerPass());                 // show cfg
    FPM.run(Fun, FAM.get());

    FAM->getResult<llvm::LoopAnalysis>(Fun).print(errs());
    return FAM;
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

void convertToSMT(llvm::Function &Fun_1, llvm::Function &Fun_2,
                  unique_ptr<llvm::FunctionAnalysisManager> FAM_1,
                  unique_ptr<llvm::FunctionAnalysisManager> FAM_2) {
    errs() << "Converting so SMT\n";

    // Print loop detection
    errs() << "Loops in program 1\n\t";
    FAM_1->getResult<llvm::LoopAnalysis>(Fun_1).print(errs());
    errs() << "Loops in program 2\n\t";
    FAM_2->getResult<llvm::LoopAnalysis>(Fun_2).print(errs());

    std::vector<SMTRef> SMT;

    // Set logic to horn
    SetLogic A("HORN");
    SMT.push_back(llvm::make_unique<SetLogic>("HORN"));

    std::vector<string> FunArgs_1;
    std::vector<string> FunArgs_2;

    // Forall quantifier over input variables
    std::vector<SortedVar> Vars;
    for (auto &Arg : Fun_1.args()) {
        Vars.push_back(SortedVar(Arg.getName(), "Int"));
        FunArgs_1.push_back(Arg.getName());
    }
    for (auto &Arg : Fun_2.args()) {
        Vars.push_back(SortedVar(Arg.getName(), "Int"));
        FunArgs_2.push_back(Arg.getName());
    }

    // Force input values to be the same
    std::vector<std::tuple<std::string, SMTRef>> Defs;
    for (auto I1 = Fun_1.args().begin(), I2 = Fun_2.args().begin(),
              E1 = Fun_1.args().end(), E2 = Fun_2.args().end();
         I1 != E1 && I2 != E2; ++I1, ++I2) {
        Defs.push_back(std::make_tuple(I1->getName(), name(I2->getName())));
    }

    // trivial implication
    std::vector<size_t> Funs;
    SMTRef MainClause =
        walkCFG(&Fun_1.getEntryBlock(), &Fun_2.getEntryBlock(),
                &FAM_1->getResult<llvm::LoopAnalysis>(Fun_1),
                &FAM_2->getResult<llvm::LoopAnalysis>(Fun_2), nullptr, nullptr,
                1, Funs, FunArgs_1, FunArgs_2);

    SMTRef Impl = makeBinOp("=>", name("true"), std::move(MainClause));

    SMTRef Forall = llvm::make_unique<const class Forall>(
        Vars, llvm::make_unique<Let>(std::move(Defs), std::move(Impl)));

    // Declare invariants
    int i = 0;
    for (auto ArgCount : Funs) {
        std::vector<string> InTypes(ArgCount, "Int");
        SMT.push_back(llvm::make_unique<Fun>("INV_" + std::to_string(i),
                                             InTypes, "Bool"));
        ++i;
    }

    SMTRef Assert = llvm::make_unique<const class Assert>(std::move(Forall));
    SMT.push_back(std::move(Assert));

    SMT.push_back(llvm::make_unique<CheckSat>());
    SMT.push_back(llvm::make_unique<GetModel>());
    for (auto &Expr : SMT) {
        std::cout << *Expr->toSExpr();
        std::cout << std::endl;
    }
}

SMTRef stepCFG(const llvm::BasicBlock *CurrentBB,
               const llvm::BasicBlock *OtherBB, llvm::LoopInfo *LoopInfo_1,
               llvm::LoopInfo *LoopInfo_2,
               const llvm::BasicBlock *PrevCurrentBB,
               const llvm::BasicBlock *PrevOtherBB, int Program,
               std::vector<size_t> &Funs, std::vector<string> CurrentFunArgs,
               std::vector<string> OtherFunArgs) {
    std::vector<std::tuple<std::string, SMTRef>> Defs =
        instrToDefs(CurrentBB, PrevCurrentBB, false);

    auto TermInst = CurrentBB->getTerminator();
    SMTRef Clause;
    if (auto BranchInst = llvm::dyn_cast<llvm::BranchInst>(TermInst)) {
        if (BranchInst->isUnconditional()) {
            assert(BranchInst->getNumSuccessors() == 1);
            Clause = walkCFG(BranchInst->getSuccessor(0), OtherBB, LoopInfo_1,
                             LoopInfo_2, CurrentBB, PrevOtherBB, Program, Funs,
                             CurrentFunArgs, OtherFunArgs);
        } else {
            assert(BranchInst->getNumSuccessors() == 2);
            auto CondName = BranchInst->getCondition()->getName();
            Clause = makeBinOp(
                "and", makeBinOp("=>", name(CondName),
                                 walkCFG(BranchInst->getSuccessor(0), OtherBB,
                                         LoopInfo_1, LoopInfo_2, CurrentBB,
                                         PrevOtherBB, Program, Funs,
                                         CurrentFunArgs, OtherFunArgs)),
                makeBinOp("=>", makeUnaryOp("not", CondName),
                          walkCFG(BranchInst->getSuccessor(1), OtherBB,
                                  LoopInfo_1, LoopInfo_2, CurrentBB,
                                  PrevOtherBB, Program, Funs, CurrentFunArgs,
                                  OtherFunArgs)));
        }
    } else if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(TermInst)) {
        std::vector<std::tuple<std::string, SMTRef>> ResultDef;
        ResultDef.push_back(std::make_tuple(
            "result$" + std::to_string(Program),
            name(getInstrNameOrValue(RetInst->getReturnValue()))));
        Clause = llvm::make_unique<const Let>(
            std::move(ResultDef),
            walkCFG(OtherBB, nullptr, LoopInfo_2, LoopInfo_1, PrevOtherBB,
                    CurrentBB, swapIndex(Program), Funs, OtherFunArgs,
                    CurrentFunArgs));
    } else {
        errs() << "Unsupported terminator instruction\n";
        Clause = name("DUMMY");
    }

    return nestLets(std::move(Clause), std::move(Defs));
}

SMTRef stepLoopBlock(
    const llvm::BasicBlock *CurrentBB, llvm::LoopInfo *LoopInfo,
    const llvm::BasicBlock *PrevCurrentBB, std::vector<string> CurrentFunArgs,
    std::function<SMTRef()> InvariantCont,
    std::function<SMTRef(const llvm::BasicBlock *BB, llvm::LoopInfo *LoopInfo,
                         const llvm::BasicBlock *PrevBB)> ExitCont) {
    // we are at the exit of the loop
    if (!LoopInfo->getLoopFor(CurrentBB)) {
        return ExitCont(CurrentBB, LoopInfo, PrevCurrentBB);
    }

    // we are back at the header
    if (LoopInfo->getLoopFor(PrevCurrentBB) &&
        LoopInfo->isLoopHeader(CurrentBB)) {
        return InvariantCont();
    }

    std::vector<std::tuple<std::string, SMTRef>> Defs =
        instrToDefs(CurrentBB, PrevCurrentBB, true);

    auto TermInst = CurrentBB->getTerminator();
    SMTRef Clause;
    if (auto BranchInst = llvm::dyn_cast<llvm::BranchInst>(TermInst)) {
        if (BranchInst->isUnconditional()) {
            assert(BranchInst->getNumSuccessors() == 1);
            Clause =
                stepLoopBlock(BranchInst->getSuccessor(0), LoopInfo, CurrentBB,
                              CurrentFunArgs, InvariantCont, ExitCont);
        } else {
            assert(BranchInst->getNumSuccessors() == 2);
            auto CondName = BranchInst->getCondition()->getName();
            Clause = makeBinOp(
                "and",
                makeBinOp("=>", name(CondName),
                          stepLoopBlock(BranchInst->getSuccessor(0), LoopInfo,
                                        CurrentBB, CurrentFunArgs,
                                        InvariantCont, ExitCont)),
                makeBinOp("=>", makeUnaryOp("not", CondName),
                          stepLoopBlock(BranchInst->getSuccessor(1), LoopInfo,
                                        CurrentBB, CurrentFunArgs,
                                        InvariantCont, ExitCont)));
        }
    } else if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(TermInst)) {
        std::vector<std::tuple<std::string, SMTRef>> ResultDef;
        ResultDef.push_back(std::make_tuple(
            "result$1", name(getInstrNameOrValue(RetInst->getReturnValue()))));
        Clause =
            llvm::make_unique<const Let>(std::move(ResultDef), name("DUMMY"));
    } else {
        errs() << "Unsupported terminator instruction\n";
        Clause = name("DUMMY");
    }

    return nestLets(std::move(Clause), std::move(Defs));
}

SMTRef walkCFG(const llvm::BasicBlock *CurrentBB,
               const llvm::BasicBlock *OtherBB, llvm::LoopInfo *LoopInfo_1,
               llvm::LoopInfo *LoopInfo_2,
               const llvm::BasicBlock *PrevCurrentBB,
               const llvm::BasicBlock *PrevOtherBB, int Program,
               std::vector<size_t> &Funs, std::vector<string> CurrentFunArgs,
               std::vector<string> OtherFunArgs) {
    if (CurrentBB && !LoopInfo_1->isLoopHeader(CurrentBB)) {
        return stepCFG(CurrentBB, OtherBB, LoopInfo_1, LoopInfo_2,
                       PrevCurrentBB, PrevOtherBB, Program, Funs,
                       CurrentFunArgs, OtherFunArgs);
    } else if (OtherBB && !LoopInfo_2->isLoopHeader(OtherBB)) {
        return stepCFG(OtherBB, CurrentBB, LoopInfo_2, LoopInfo_1, PrevOtherBB,
                       PrevCurrentBB, swapIndex(Program), Funs, OtherFunArgs,
                       CurrentFunArgs);
    } else if (!CurrentBB && OtherBB) {
        errs() << "LOOP at OtherBB\n"; // TODO: implement;
    } else if (CurrentBB && !OtherBB) {
        const llvm::Loop *Loop = LoopInfo_1->getLoopFor(CurrentBB);
        assert(Loop);
        auto PhiNodes = extractPhiNodes(*Loop);
        Funs.push_back(CurrentFunArgs.size() + OtherFunArgs.size() +
                       PhiNodes.size());
        std::vector<string> InitialArgs;
        std::vector<string> PreCondArgs;
        std::vector<string> PostCondArgs;

        InitialArgs.insert(InitialArgs.end(), CurrentFunArgs.begin(),
                           CurrentFunArgs.end());
        InitialArgs.insert(InitialArgs.end(), OtherFunArgs.begin(),
                           OtherFunArgs.end());

        calcInvArgs(PhiNodes, PreCondArgs, InitialArgs, PostCondArgs, Loop);

        std::string InvName = "INV_" + std::to_string(Funs.size() - 1);
        std::vector<SMTRef> Clauses;
        Clauses.push_back(makeOp(InvName, InitialArgs));

        std::vector<SortedVar> Vars;
        for (auto Arg : PreCondArgs) {
            Vars.push_back(SortedVar(Arg, "Int"));
        }

        PreCondArgs.insert(PreCondArgs.begin(), OtherFunArgs.begin(),
                           OtherFunArgs.end());
        PreCondArgs.insert(PreCondArgs.begin(), CurrentFunArgs.begin(),
                           CurrentFunArgs.end());
        PostCondArgs.insert(PostCondArgs.begin(), OtherFunArgs.begin(),
                            OtherFunArgs.end());
        PostCondArgs.insert(PostCondArgs.begin(), CurrentFunArgs.begin(),
                            CurrentFunArgs.end());

        SMTRef Forall = llvm::make_unique<const class Forall>(
            Vars,
            makeBinOp("=>", makeOp(InvName, PreCondArgs),
                      stepLoopBlock(
                          CurrentBB, LoopInfo_1, PrevCurrentBB, CurrentFunArgs,
                          [InvName, PostCondArgs]() {
                              return makeOp(InvName, PostCondArgs);
                          },
                          [OtherBB, LoopInfo_2, PrevOtherBB, Funs,
                           CurrentFunArgs, OtherFunArgs,
                           Program](const llvm::BasicBlock *BB,
                                    llvm::LoopInfo *LoopInfo,
                                    const llvm::BasicBlock *PrevBB) mutable {
                              return walkCFG(BB, OtherBB, LoopInfo, LoopInfo_2,
                                             PrevBB, PrevOtherBB, Program, Funs,
                                             CurrentFunArgs, OtherFunArgs);
                          })));
        Clauses.push_back(std::move(Forall));
        return llvm::make_unique<Op>("and", std::move(Clauses));
    } else if (CurrentBB && OtherBB) {
        const llvm::Loop *Loop_1 = LoopInfo_1->getLoopFor(CurrentBB);
        const llvm::Loop *Loop_2 = LoopInfo_2->getLoopFor(OtherBB);
        assert(Loop_1 && Loop_2);

        auto PhiNodes_1 = extractPhiNodes(*Loop_1);
        auto PhiNodes_2 = extractPhiNodes(*Loop_2);
        Funs.push_back(CurrentFunArgs.size() + OtherFunArgs.size() +
                       PhiNodes_1.size() + PhiNodes_2.size());
        std::vector<string> InitialArgs;
        std::vector<string> PreCondArgs;
        std::vector<string> PostCondArgs;

        InitialArgs.insert(InitialArgs.end(), CurrentFunArgs.begin(),
                           CurrentFunArgs.end());
        InitialArgs.insert(InitialArgs.end(), OtherFunArgs.begin(),
                           OtherFunArgs.end());

        calcInvArgs(PhiNodes_1, PreCondArgs, InitialArgs, PostCondArgs, Loop_1);
        calcInvArgs(PhiNodes_2, PreCondArgs, InitialArgs, PostCondArgs, Loop_2);

        std::string InvName = "INV_" + std::to_string(Funs.size() - 1);
        std::vector<SMTRef> Clauses;
        Clauses.push_back(makeOp(InvName, InitialArgs));

        std::vector<SortedVar> Vars;
        for (auto Arg : PreCondArgs) {
            Vars.push_back(SortedVar(Arg, "Int"));
        }

        PreCondArgs.insert(PreCondArgs.begin(), OtherFunArgs.begin(),
                           OtherFunArgs.end());
        PreCondArgs.insert(PreCondArgs.begin(), CurrentFunArgs.begin(),
                           CurrentFunArgs.end());
        PostCondArgs.insert(PostCondArgs.begin(), OtherFunArgs.begin(),
                            OtherFunArgs.end());
        PostCondArgs.insert(PostCondArgs.begin(), CurrentFunArgs.begin(),
                            CurrentFunArgs.end());

        SMTRef Forall = llvm::make_unique<const class Forall>(
            Vars,
            makeBinOp(
                "=>", makeOp(InvName, PreCondArgs),
                stepLoopBlock(
                    CurrentBB, LoopInfo_1, PrevCurrentBB, CurrentFunArgs,
                    [OtherBB, LoopInfo_2, PrevOtherBB, OtherFunArgs, InvName,
                     PostCondArgs, Funs, CurrentFunArgs, CurrentBB, Program,
                     PrevCurrentBB, LoopInfo_1]() {
                        return stepLoopBlock(
                            OtherBB, LoopInfo_2, PrevOtherBB, OtherFunArgs,
                            [InvName, PostCondArgs]() {
                                return makeOp(InvName, PostCondArgs);
                            },
                            [OtherBB, LoopInfo_2, PrevOtherBB, Funs,
                             CurrentFunArgs, OtherFunArgs, CurrentBB,
                             PrevCurrentBB, LoopInfo_1,
                             Program](const llvm::BasicBlock *BB,
                                      llvm::LoopInfo *LoopInfo,
                                      const llvm::BasicBlock *PrevBB) mutable {
                                return name("true"); // we only allow
                                                     // simultanous loop
                                                     // stepping for now
                            });
                    },
                    [OtherBB, LoopInfo_2, PrevOtherBB, Funs, CurrentFunArgs,
                     OtherFunArgs,
                     Program](const llvm::BasicBlock *CurrentBB,
                              llvm::LoopInfo *LoopInfo_1,
                              const llvm::BasicBlock *PrevCurrentBB) mutable {
                        return stepLoopBlock(
                            OtherBB, LoopInfo_2, PrevOtherBB, OtherFunArgs,
                            []() { return name("true"); }, // we only allow
                                                           // simulatnous loop
                                                           // stepping for now
                            [Program, Funs, CurrentFunArgs, OtherFunArgs,
                             CurrentBB, LoopInfo_1, PrevCurrentBB](
                                const llvm::BasicBlock *OtherBB,
                                llvm::LoopInfo *LoopInfo_2,
                                const llvm::BasicBlock *PrevOtherBB) mutable {
                                return walkCFG(CurrentBB, OtherBB, LoopInfo_1,
                                               LoopInfo_2, PrevCurrentBB,
                                               PrevOtherBB, Program, Funs,
                                               CurrentFunArgs, OtherFunArgs);
                            });
                    })));
        Clauses.push_back(std::move(Forall));
        return llvm::make_unique<Op>("and", std::move(Clauses));
    } else {
        return makeBinOp("=", "result$1", "result$2");
    }
    errs() << "\n---\n\n";
    return name("DUMMY");
}

std::tuple<std::string, SMTRef> toDef(const llvm::Instruction &Instr,
                                      const llvm::BasicBlock *PrevBB) {
    if (auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        return std::make_tuple(
            BinOp->getName(),
            makeBinOp(getOpName(*BinOp),
                      getInstrNameOrValue(BinOp->getOperand(0)),
                      getInstrNameOrValue(BinOp->getOperand(1))));
    }
    if (auto CmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto Cmp = makeBinOp(getPredName(CmpInst->getPredicate()),
                             getInstrNameOrValue(CmpInst->getOperand(0)),
                             getInstrNameOrValue(CmpInst->getOperand(1)));
        return std::make_tuple(CmpInst->getName(), std::move(Cmp));
    }
    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return std::make_tuple(PhiInst->getName(),
                               name(getInstrNameOrValue(Val)));
    }
    if (auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        return std::make_tuple(
            SelectInst->getName(),
            makeOp("ite", {getInstrNameOrValue(SelectInst->getCondition()),
                           getInstrNameOrValue(SelectInst->getTrueValue()),
                           getInstrNameOrValue(SelectInst->getFalseValue())}));
    }
    errs() << Instr << "\n";
    errs() << "Couldn't convert instruction to def\n";
    return std::make_tuple("UNKNOWN INSTRUCTION", name("UNKNOWN ARGS"));
}

std::vector<const llvm::PHINode *> extractPhiNodes(const llvm::Loop &Loop) {
    std::vector<const llvm::PHINode *> PhiNodes;
    for (auto &BB : Loop.getBlocks()) {
        for (auto &Inst : *BB) {
            if (auto PhiNode = llvm::dyn_cast<llvm::PHINode>(&Inst)) {
                PhiNodes.push_back(PhiNode);
            }
        }
    }
    return PhiNodes;
}

std::string getOpName(const llvm::BinaryOperator &Op) {
    switch (Op.getOpcode()) {
    case Instruction::Add:
        return "+";
    case Instruction::Sub:
        return "-";
    default:
        return Op.getOpcodeName();
    }
}

std::string getPredName(llvm::CmpInst::Predicate Pred) {
    switch (Pred) {
    case CmpInst::ICMP_SLT:
        return "<=";
    default:
        return "unsupported predicate";
    }
}

std::string getInstrNameOrValue(const llvm::Value *Val) {
    if (auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        return ConstInt->getValue().toString(10, 1);
    }
    return Val->getName();
}

int swapIndex(int i) {
    assert(i == 1 || i == 2);
    return i == 1 ? 2 : 1;
}

void calcInvArgs(std::vector<const llvm::PHINode *> PhiNodes,
                 std::vector<std::string> &PreCondArgs,
                 std::vector<std::string> &InitialArgs,
                 std::vector<std::string> &PostCondArgs,
                 const llvm::Loop *Loop) {
    for (auto PhiNode : PhiNodes) {
        // Variable name
        PreCondArgs.push_back(PhiNode->getName());
        for (auto I = PhiNode->block_begin(), E = PhiNode->block_end(); I != E;
             ++I) {
            if (!Loop->contains(*I)) {
                // Find initial value
                InitialArgs.push_back(
                    getInstrNameOrValue(PhiNode->getIncomingValueForBlock(*I)));
            } else {
                PostCondArgs.push_back(
                    getInstrNameOrValue(PhiNode->getIncomingValueForBlock(*I)));
            }
        }
    }
}

SMTRef nestLets(SMTRef Clause,
                std::vector<std::tuple<std::string, SMTRef>> Defs) {
    SMTRef Lets = std::move(Clause);
    for (auto I = Defs.rbegin(), E = Defs.rend(); I != E; ++I) {
        std::vector<std::tuple<std::string, SMTRef>> Def;
        Def.push_back(std::move(*I));
        Lets = llvm::make_unique<const Let>(std::move(Def), std::move(Lets));
    }
    return Lets;
}

std::vector<std::tuple<std::string, SMTRef>>
instrToDefs(const llvm::BasicBlock *BB, const llvm::BasicBlock *PrevBB,
            bool Loop) {
    std::vector<std::tuple<std::string, SMTRef>> Defs;
    assert(BB->size() >=
           1); // There should be at least a terminator instruction
    for (auto Instr = BB->begin(), E = std::prev(BB->end(), 1); Instr != E;
         ++Instr) {
        assert(!Instr->getType()->isVoidTy());
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!Loop || !llvm::isa<llvm::PHINode>(Instr)) {
            Defs.push_back(toDef(*Instr, PrevBB));
        }
    }
    return Defs;
}
