#include "Reve.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "MarkAnalysis.h"
#include "Mem2Reg.h"
#include "PathAnalysis.h"
#include "RemoveMarkPass.h"
#include "SExpr.h"
#include "SMT.h"
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
                                                           string Prefix) {
    llvm::PassBuilder PB;
    auto FAM = llvm::make_unique<llvm::FunctionAnalysisManager>(
        true);                         // enable debug log
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
    FPM.addPass(llvm::VerifierPass());
    FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    // FPM.addPass(CFGViewerPass());                 // show cfg
    FPM.run(Fun, FAM.get());

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
    // TODO: check that the marks are the same
    auto PathMap_1 = FAM_1->getResult<PathAnalysis>(Fun_1);
    auto PathMap_2 = FAM_2->getResult<PathAnalysis>(Fun_2);
    auto Marked_1 = FAM_1->getResult<MarkAnalysis>(Fun_1);
    auto Marked_2 = FAM_2->getResult<MarkAnalysis>(Fun_2);
    std::map<int, set<string>> FreeVarsMap = freeVarsMap(PathMap_1, PathMap_2);
    std::vector<SMTRef> SMTExprs;
    std::vector<SMTRef> PathExprs;

    SMTExprs.push_back(std::make_shared<SetLogic>("HORN"));

    for (auto &PathMapIt : PathMap_1) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != -1) {
            // ignore entry node
            SMTExprs.push_back(
                invariantDef(StartIndex, FreeVarsMap.at(StartIndex)));
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            auto Paths = PathMap_2.at(StartIndex).at(EndIndex);
            for (auto &Path_1 : InnerPathMapIt.second) {
                for (auto &Path_2 : Paths) {
                    auto SMT_2 = pathToSMT(
                        Path_2, invariant(EndIndex, FreeVarsMap.at(EndIndex)),
                        2);
                    PathExprs.push_back(std::make_shared<Assert>(
                        wrapForall(pathToSMT(Path_1, SMT_2, 1), StartIndex,
                                   FreeVarsMap.at(StartIndex))));
                }
            }
        }
    }

    // generate forbidden paths
    for (auto &PathMapIt : PathMap_1) {
        int StartIndex = PathMapIt.first;
        for (auto &InnerPathMapIt_1 : PathMapIt.second) {
            int EndIndex = InnerPathMapIt_1.first;
            for (auto &InnerPathMapIt_2 : PathMap_2.at(StartIndex)) {
                if (EndIndex != InnerPathMapIt_2.first) {
                    for (auto &Path_1 : InnerPathMapIt_1.second) {
                        for (auto &Path_2 : InnerPathMapIt_2.second) {
                            auto SMT_2 = pathToSMT(Path_2, name("false"), 2);
                            PathExprs.push_back(std::make_shared<Assert>(
                                wrapForall(pathToSMT(Path_1, SMT_2, 1),
                                           StartIndex,
                                           FreeVarsMap.at(StartIndex))));
                        }
                    }
                }
            }
        }
    }

    SMTExprs.insert(SMTExprs.end(), PathExprs.begin(), PathExprs.end());
    SMTExprs.push_back(make_shared<CheckSat>());
    SMTExprs.push_back(make_shared<GetModel>());

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
}

SMTRef pathToSMT(Path Path, SMTRef EndClause, int Program) {
    SMTRef Clause = EndClause;
    for (auto It = Path.Edges.rbegin(), E = Path.Edges.rend(); It != E; ++It) {
        auto PrevIt = std::next(It, 1);
        auto Prev = Path.Start;
        if (PrevIt != E) {
            Prev = PrevIt->Block;
        }
        auto Defs = instrToDefs(It->Block, Prev, false, Program);
        Clause = nestLets(Clause, Defs);
        if (It->Condition) {
            Clause = makeBinOp("=>", It->Condition, Clause);
        }
    }
    auto Defs = instrToDefs(Path.Start, nullptr, true, Program);
    Clause = nestLets(Clause, Defs);
    return Clause;
}

std::tuple<string, SMTRef> toDef(const llvm::Instruction &Instr,
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
        return std::make_tuple(CmpInst->getName(), Cmp);
    }
    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return std::make_tuple(PhiInst->getName(), getInstrNameOrValue(Val));
    }
    if (auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        std::vector<SMTRef> Args = {
            getInstrNameOrValue(SelectInst->getCondition()),
            getInstrNameOrValue(SelectInst->getTrueValue()),
            getInstrNameOrValue(SelectInst->getFalseValue())};
        return std::make_tuple(SelectInst->getName(),
                               std::make_shared<class Op>("ite", Args));
    }
    errs() << Instr << "\n";
    errs() << "Couldn't convert instruction to def\n";
    return std::make_tuple("UNKNOWN INSTRUCTION", name("UNKNOWN ARGS"));
}

string getOpName(const llvm::BinaryOperator &Op) {
    switch (Op.getOpcode()) {
    case Instruction::Add:
        return "+";
    case Instruction::Sub:
        return "-";
    default:
        return Op.getOpcodeName();
    }
}

string getPredName(llvm::CmpInst::Predicate Pred) {
    switch (Pred) {
    case CmpInst::ICMP_SLT:
        return "<";
    case CmpInst::ICMP_SLE:
        return "<=";
    case CmpInst::ICMP_EQ:
        return "=";
    case CmpInst::ICMP_SGE:
        return ">=";
    case CmpInst::ICMP_SGT:
        return ">";
    default:
        return "unsupported predicate";
    }
}

SMTRef getInstrNameOrValue(const llvm::Value *Val) {
    if (auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        auto ApInt = ConstInt->getValue();
        if (ApInt.isNegative()) {
            return makeUnaryOp(
                "-", name(ApInt.toString(10, 1).substr(1, string::npos)));
        }
        return name(ApInt.toString(10, 1));
    }
    return name(Val->getName());
}

int swapIndex(int i) {
    assert(i == 1 || i == 2);
    return i == 1 ? 2 : 1;
}

std::vector<std::tuple<string, SMTRef>>
instrToDefs(const llvm::BasicBlock *BB, const llvm::BasicBlock *PrevBB,
            bool IgnorePhis, int Program) {
    std::vector<std::tuple<string, SMTRef>> Defs;
    assert(BB->size() >=
           1); // There should be at least a terminator instruction
    for (auto Instr = BB->begin(), E = std::prev(BB->end(), 1); Instr != E;
         ++Instr) {
        assert(!Instr->getType()->isVoidTy());
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!IgnorePhis || !llvm::isa<llvm::PHINode>(Instr)) {
            Defs.push_back(toDef(*Instr, PrevBB));
        }
    }
    if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(BB->getTerminator())) {
        Defs.push_back(
            std::make_tuple("result$" + std::to_string(Program),
                            name(RetInst->getReturnValue()->getName())));
    }
    return Defs;
}

SMTRef invariant(int BlockIndex, set<string> Args) {
    if (BlockIndex == -2) {
        return makeBinOp("=", "result$1", "result$2");
    }
    std::vector<string> ArgsVect;
    ArgsVect.insert(ArgsVect.begin(), Args.begin(), Args.end());
    return makeOp(invName(BlockIndex), ArgsVect);
}

SMTRef invariantDef(int BlockIndex, set<string> FreeVars) {
    std::vector<string> Args(FreeVars.size(), "Int");

    return std::make_shared<class Fun>(invName(BlockIndex), Args, "Bool");
}

string invName(int Index) {
    if (Index == -1) {
        return "INV_ENTRY";
    }
    return "INV_" + std::to_string(Index);
}

SMTRef wrapForall(SMTRef Clause, int BlockIndex, set<string> FreeVars) {
    std::vector<SortedVar> Vars;
    for (auto &Arg : FreeVars) {
        // TODO: detect type
        Vars.push_back(SortedVar(Arg, "Int"));
    }
    // no entry invariant
    if (BlockIndex != -1) {
        Clause = makeBinOp("=>", invariant(BlockIndex, FreeVars), Clause);
    }
    return llvm::make_unique<Forall>(Vars, Clause);
}

set<string> freeVars(std::map<int, Paths> PathMap) {
    set<string> FreeVars;
    for (auto &Paths : PathMap) {
        for (auto &Path : Paths.second) {
            set<string> Constructed;

            // the first block is special since we can't resolve phi
            // nodes here
            for (auto &Instr : *Path.Start) {
                Constructed.insert(Instr.getName());
                if (llvm::isa<llvm::PHINode>(Instr)) {
                    FreeVars.insert(Instr.getName());
                    continue;
                }
                for (auto Op : Instr.operand_values()) {
                    if (Constructed.find(Op->getName()) == Constructed.end() &&
                        !Op->getName().empty()) {
                        FreeVars.insert(Op->getName());
                    }
                }
            }

            // now deal with the rest and ignore phi nodes
            for (auto &Edge : Path.Edges) {
                for (auto &Instr : *Edge.Block) {
                    Constructed.insert(Instr.getName());
                    if (llvm::isa<llvm::PHINode>(Instr)) {
                        continue;
                    }
                    for (auto Op : Instr.operand_values()) {
                        if (Constructed.find(Op->getName()) ==
                                Constructed.end() &&
                            !Op->getName().empty()) {
                            FreeVars.insert(Op->getName());
                        }
                    }
                }
            }
        }
    }
    return FreeVars;
}

std::map<int, set<string>> freeVarsMap(PathMap Map_1, PathMap Map_2) {
    std::map<int, set<string>> FreeVarsMap;
    for (auto &It : Map_1) {
        int Index = It.first;
        auto FreeVars_1 = freeVars(Map_1.at(Index));
        auto FreeVars_2 = freeVars(Map_2.at(Index));
        set<string> FreeVars;
        set_union(FreeVars_1.begin(), FreeVars_1.end(), FreeVars_2.begin(),
                  FreeVars_2.end(), inserter(FreeVars, FreeVars.begin()));
        FreeVarsMap.insert(make_pair(Index, FreeVars));
    }
    FreeVarsMap.insert(make_pair(-2, set<string>()));
    return FreeVarsMap;
}
