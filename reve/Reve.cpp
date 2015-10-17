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

using llvm::ErrorOr;
using llvm::errs;
using llvm::IntrusiveRefCntPtr;
using llvm::CmpInst;

using std::unique_ptr;

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

    std::vector<std::unique_ptr<const SMTExpr>> SMT;

    // Set logic to horn
    SetLogic A("HORN");
    SMT.push_back(llvm::make_unique<SetLogic>("HORN"));

    // Forall quantifier over input variables
    std::vector<SortedVar> Vars;
    for (auto &Arg : Fun_1.args()) {
        Vars.push_back(SortedVar(Arg.getName(), "Int"));
    }
    for (auto &Arg : Fun_2.args()) {
        Vars.push_back(SortedVar(Arg.getName(), "Int"));
    }

    // Force input values to be the same
    std::vector<std::tuple<std::string, std::unique_ptr<const SMTExpr>>> Defs;
    for (auto I1 = Fun_1.args().begin(), I2 = Fun_2.args().begin(),
              E1 = Fun_1.args().end(), E2 = Fun_2.args().end();
         I1 != E1 && I2 != E2; ++I1, ++I2) {
        Defs.push_back(std::make_tuple(I1->getName(), name(I2->getName())));
    }

    // trivial implication
    std::vector<std::unique_ptr<const SMTExpr>> Args;
    Args.push_back(name("true"));
    std::unique_ptr<const SMTExpr> MainClause =
        walkCFG(Fun_1.getEntryBlock(), Fun_2.getEntryBlock(),
                FAM_1->getResult<llvm::LoopAnalysis>(Fun_1),
                FAM_2->getResult<llvm::LoopAnalysis>(Fun_2), nullptr, nullptr);
    Args.push_back(std::move(MainClause));

    std::unique_ptr<const SMTExpr> Impl =
        llvm::make_unique<const Op>("=>", std::move(Args));

    std::unique_ptr<const SMTExpr> Forall =
        llvm::make_unique<const class Forall>(
            Vars, llvm::make_unique<Let>(std::move(Defs), std::move(Impl)));

    std::unique_ptr<const SMTExpr> Assert =
        llvm::make_unique<const class Assert>(std::move(Forall));
    SMT.push_back(std::move(Assert));

    SMT.push_back(llvm::make_unique<CheckSat>());
    SMT.push_back(llvm::make_unique<GetModel>());
    for (auto &Expr : SMT) {
        std::cout << *Expr->toSExpr();
        std::cout << std::endl;
    }
}

std::unique_ptr<const SMTExpr>
walkCFG(const llvm::BasicBlock &BB_1, const llvm::BasicBlock &BB_2,
        llvm::LoopInfo &LoopInfo_1, llvm::LoopInfo &LoopInfo_2,
        const llvm::BasicBlock *PrevBB_1, const llvm::BasicBlock *PrevBB_2) {
    if (!LoopInfo_1.isLoopHeader(&BB_1)) {
        std::vector<std::tuple<std::string, std::unique_ptr<const SMTExpr>>>
            Defs;
        for (auto Instr = BB_1.begin(), E = std::prev(BB_1.end(), 1);
             Instr != E; ++Instr) {
            if (!Instr->getType()->isVoidTy()) {
                Defs.push_back(toDef(*Instr, PrevBB_1));
            } else {
                errs() << "Void instruction\n";
            }
        }
        auto TermInst = BB_1.getTerminator();
        std::unique_ptr<const SMTExpr> Clause;
        if (auto BranchInst = llvm::dyn_cast<llvm::BranchInst>(TermInst)) {
            if (BranchInst->isUnconditional()) {
                assert(BranchInst->getNumSuccessors() == 1);
                Clause = walkCFG(*BranchInst->getSuccessor(0), BB_2, LoopInfo_1,
                                 LoopInfo_2, &BB_1, &BB_2);
            } else {
                assert(BranchInst->getNumSuccessors() == 2);
                auto CondName = BranchInst->getCondition()->getName();
                Clause = makeBinOp(
                    "and",
                    makeBinOp("=>", name(CondName),
                              walkCFG(*BranchInst->getSuccessor(0), BB_2,
                                      LoopInfo_1, LoopInfo_2, &BB_1, &BB_2)),
                    makeBinOp("=>", makeUnaryOp("not", CondName),
                              walkCFG(*BranchInst->getSuccessor(1), BB_2,
                                      LoopInfo_1, LoopInfo_2, &BB_1, &BB_2)));
            }
        } else if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(TermInst)) {
            std::vector<std::tuple<std::string, std::unique_ptr<const SMTExpr>>>
                ResultDef;
            ResultDef.push_back(std::make_tuple(
                "result$1",
                name(getInstrNameOrValue(RetInst->getReturnValue()))));
            Clause = llvm::make_unique<const Let>(std::move(ResultDef),
                                                  name("DUMMY"));
        } else {
            errs() << "Unsupported terminator instruction\n";
            Clause = name("DUMMY");
        }
        return llvm::make_unique<const Let>(std::move(Defs), std::move(Clause));
    }
    return name("DUMMY");
}

std::tuple<std::string, std::unique_ptr<const SMTExpr>>
toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB) {
    if (auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        errs() << BinOp->getOpcodeName();
        errs() << "Binary operator\n";
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
    errs() << "Couldn't convert instruction to def\n";
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
