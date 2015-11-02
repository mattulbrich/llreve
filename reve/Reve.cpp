#include "Reve.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "PathAnalysis.h"
#include "RemoveMarkPass.h"
#include "SExpr.h"
#include "SMT.h"
#include "UnifyFunctionExitNodes.h"
#include "UniqueNamePass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/PassManager.h"

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

    ErrorOr<llvm::Function &> FunOrError1 = getFunction(*Mod1);
    ErrorOr<llvm::Function &> FunOrError2 = getFunction(*Mod2);

    if (!FunOrError1 || !FunOrError2) {
        errs() << "Couldn't find a function\n";
        return 1;
    }

    auto Fam1 = preprocessModule(FunOrError1.get(), "1");
    auto Fam2 = preprocessModule(FunOrError2.get(), "2");

    convertToSMT(FunOrError1.get(), FunOrError2.get(), std::move(Fam1),
                 std::move(Fam2));

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
    FPM.addPass(CFGViewerPass());                 // show cfg
    FPM.addPass(llvm::VerifierPass());
    FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
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

std::pair<set<string>, set<string>> functionArgs(llvm::Function &Fun1,
                                                 llvm::Function &Fun2) {
    set<string> Args1;
    for (auto &Arg : Fun1.args()) {
        Args1.insert(Arg.getName());
    }
    set<string> Args2;
    for (auto &Arg : Fun2.args()) {
        Args2.insert(Arg.getName());
    }
    return std::make_pair(Args1, Args2);
}

SMTRef makeFunArgsEqual(SMTRef Clause, set<string> Args1, set<string> Args2) {
    std::vector<SMTRef> Args;
    if (Args1.size() != Args2.size()) {
        llvm::errs() << "Warning: different number of arguments\n";
    }
    auto It = Args2.begin();
    for (auto Arg : Args1) {
        Args.push_back(makeBinOp("=", Arg, *It));
        ++It;
    }

    auto And = make_shared<Op>("and", Args);

    return makeBinOp("=>", And, Clause);
}

void convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                  unique_ptr<llvm::FunctionAnalysisManager> Fam1,
                  unique_ptr<llvm::FunctionAnalysisManager> Fam2) {
    // TODO(moritz): check that the marks are the same
    auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    std::pair<set<string>, set<string>> FunArgsPair = functionArgs(Fun1, Fun2);
    set<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.insert(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.insert(Arg);
    }
    std::map<int, set<string>> FreeVarsMap =
        freeVarsMap(PathMap1, PathMap2, FunArgs);
    std::vector<SMTRef> SMTExprs;
    std::vector<SMTRef> PathExprs;

    SMTExprs.push_back(std::make_shared<SetLogic>("HORN"));

    SMTExprs.push_back(invariantDef(-1, FunArgs));

    auto SynchronizedPaths = synchronizedPaths(PathMap1, PathMap2, FreeVarsMap);

    // add invariant defs
    SMTExprs.insert(SMTExprs.end(), SynchronizedPaths.first.begin(),
                    SynchronizedPaths.first.end());

    // assert equal outputs for equal inputs
    SMTExprs.push_back(equalInputsEqualOutputs(FunArgs, FunArgsPair.first,
                                               FunArgsPair.second));

    // add actual path smts
    PathExprs.insert(PathExprs.end(), SynchronizedPaths.second.begin(),
                     SynchronizedPaths.second.end());

    // TODO (moritz): Figure out what to do about that

    // generate forbidden paths
    // PathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    // auto ForbiddenPaths =
    //     forbiddenPaths(PathMap1, PathMap2, FreeVarsMap, FunArgs,
    //                    FunArgsPair.first, FunArgsPair.second);
    // PathExprs.insert(PathExprs.end(), ForbiddenPaths.begin(),
    //                  ForbiddenPaths.end());

    SMTExprs.insert(SMTExprs.end(), PathExprs.begin(), PathExprs.end());

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
}

std::pair<std::vector<SMTRef>, std::vector<SMTRef>>
synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                  std::map<int, set<string>> FreeVarsMap) {
    std::vector<SMTRef> InvariantDefs;
    std::vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != -1) {
            // ignore entry node
            InvariantDefs.push_back(
                invariantDef(StartIndex, FreeVarsMap.at(StartIndex)));
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            auto Paths = PathMap2.at(StartIndex).at(EndIndex);
            for (auto &Path1 : InnerPathMapIt.second) {
                for (auto &Path2 : Paths) {
                    auto EndInvariant = invariant(StartIndex, EndIndex,
                                                  FreeVarsMap.at(StartIndex),
                                                  FreeVarsMap.at(EndIndex));
                    auto Defs1 = pathToSMT(Path1, 1, FreeVarsMap.at(EndIndex), EndIndex == -2);
                    auto Defs2 = pathToSMT(Path2, 2, FreeVarsMap.at(EndIndex), EndIndex == -2);
                    PathExprs.push_back(std::make_shared<Assert>(
                        wrapForall(interleaveSMT(EndInvariant, Defs1, Defs2),
                                   FreeVarsMap.at(StartIndex))));
                    ;
                }
            }
        }
    }
    return make_pair(InvariantDefs, PathExprs);
}

// std::vector<SMTRef> forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
//                                    std::map<int, set<string>> FreeVarsMap) {
//     std::vector<SMTRef> PathExprs;
//     for (auto &PathMapIt : PathMap1) {
//         int StartIndex = PathMapIt.first;
//         for (auto &InnerPathMapIt1 : PathMapIt.second) {
//             int EndIndex = InnerPathMapIt1.first;
//             for (auto &InnerPathMapIt2 : PathMap2.at(StartIndex)) {
//                 if (EndIndex != InnerPathMapIt2.first) {
//                     for (auto &Path1 : InnerPathMapIt1.second) {
//                         for (auto &Path2 : InnerPathMapIt2.second) {
//                             auto Smt2 = pathToSMT(Path2, name("false"), 2,
//                                                   FreeVarsMap.at(EndIndex));
//                             PathExprs.push_back(std::make_shared<Assert>(
//                                 wrapForall(pathToSMT(Path1, Smt2, 1,
//                                                      FreeVarsMap.at(EndIndex)),
//                                            FreeVarsMap.at(StartIndex))));
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     return PathExprs;
// }

SMTRef wrapToplevelForall(SMTRef Clause, set<string> Args) {
    std::vector<SortedVar> VecArgs;
    for (auto Arg : Args) {
        // TODO(moritz): don't hardcode type
        VecArgs.push_back(SortedVar(Arg, "Int"));
    }
    return make_shared<Forall>(VecArgs, Clause);
}

std::pair<std::vector<std::vector<CleanAssignments>>, std::vector<CallInfo>>
splitAssignments(std::vector<Assignments> AssignmentsList) {
    std::vector<std::vector<CleanAssignments>> CleanAssignmentsReturn;
    std::vector<CallInfo> CallInfos;
    std::vector<struct CleanAssignments> CurrentAssignmentsList;
    for (auto Assignments : AssignmentsList) {
        SMTRef Condition = Assignments.Condition;
        std::vector<Assignment> CurrentDefinitions;
        for (auto DefOrCall : Assignments.Definitions) {
            if (DefOrCall.Tag == Def) {
                CurrentDefinitions.push_back(*DefOrCall.Definition);
            } else {
                CurrentAssignmentsList.push_back(
                    CleanAssignments(CurrentDefinitions, Condition));
                CleanAssignmentsReturn.push_back(CurrentAssignmentsList);
                CurrentAssignmentsList.clear();
                Condition = nullptr;
                CallInfos.push_back(*DefOrCall.CallInfo);
            }
        }
        CurrentAssignmentsList.push_back(
            CleanAssignments(CurrentDefinitions, Condition));
    }
    CleanAssignmentsReturn.push_back(CurrentAssignmentsList);
    return make_pair(CleanAssignmentsReturn, CallInfos);
}
SMTRef interleaveSMT(SMTRef EndClause, std::vector<Assignments> Assignments1,
                     std::vector<Assignments> Assignments2) {
    SMTRef Clause = EndClause;
    auto SplitAssignments1 = splitAssignments(Assignments1);
    auto SplitAssignments2 = splitAssignments(Assignments2);
    auto CleanAssignments1 = SplitAssignments1.first;
    auto CleanAssignments2 = SplitAssignments2.first;
    auto CallInfo1 = SplitAssignments1.second;
    auto CallInfo2 = SplitAssignments2.second;
    assert(CleanAssignments1.size() == CleanAssignments2.size());
    assert(CallInfo1.size() == CallInfo2.size());
    assert(CleanAssignments1.size() == CallInfo1.size() + 1);
    assert(Assignments1.size() >= 1);
    bool first = true;
    auto CallIt1 = CallInfo1.rbegin();
    auto CallIt2 = CallInfo2.rbegin();
    for (auto It1 = CleanAssignments1.rbegin(), E1 = CleanAssignments1.rend(),
              It2 = CleanAssignments2.rbegin();
         It1 != E1; ++It1, ++It2) {
        if (first) {
            first = false;
        } else {
            Clause = recursiveForall(Clause, CallIt1->Args, CallIt2->Args,
                                     CallIt1->AssignedTo, CallIt2->AssignedTo);
            ++CallIt1;
            ++CallIt2;
        }
        for (auto InnerIt2 = It2->rbegin(), InnerE2 = It2->rend();
             InnerIt2 != InnerE2; ++InnerIt2) {
            auto Assgns = *InnerIt2;
            Clause = nestLets(Clause, Assgns.Definitions);
            if (Assgns.Condition) {
                Clause = makeBinOp("=>", Assgns.Condition, Clause);
            }
        }
        for (auto InnerIt1 = It1->rbegin(), InnerE1 = It1->rend();
             InnerIt1 != InnerE1; ++InnerIt1) {
            auto Assgns = *InnerIt1;
            Clause = nestLets(Clause, Assgns.Definitions);
            if (Assgns.Condition) {
                Clause = makeBinOp("=>", Assgns.Condition, Clause);
            }
        }
    }
    return Clause;
}

SMTRef recursiveForall(SMTRef Clause, std::vector<SMTRef> Args1,
                       std::vector<SMTRef> Args2, std::string Ret1,
                       std::string Ret2) {
    // TODO: fix order
    std::vector<SortedVar> Args;
    Args.push_back(SortedVar(Ret1, "Int"));
    Args.push_back(SortedVar(Ret2, "Int"));
    std::vector<SMTRef> ImplArgs;
    for (auto Arg : Args1) {
        ImplArgs.push_back(Arg);
    }
    for (auto Arg : Args2) {
        ImplArgs.push_back(Arg);
    }
    ImplArgs.push_back(name(Ret1));
    ImplArgs.push_back(name(Ret2));
    Clause =
        makeBinOp("=>", std::make_shared<Op>(invName(-1), ImplArgs), Clause);
    return make_shared<Forall>(Args, Clause);
}

std::vector<Assignments> pathToSMT(Path Path, int Program,
                                   std::set<std::string> FreeVars, bool ToEnd) {
    auto FilteredFreeVars = filterVars(Program, FreeVars);

    std::vector<Assignments> AllDefs;
    set<string> Constructed;
    std::vector<CallInfo> CallInfos;

    auto StartDefs =
        instrToDefs(Path.Start, nullptr, true, false, Program, Constructed);
    AllDefs.push_back(Assignments(StartDefs, nullptr));

    auto Prev = Path.Start;

    unsigned int i = 0;
    for (auto Edge : Path.Edges) {
        i++;
        bool last = i == Path.Edges.size();
        auto Defs =
            instrToDefs(Edge.Block, Prev, false, last && !ToEnd, Program, Constructed);
        AllDefs.push_back(Assignments(Defs, Edge.Condition));
        Prev = Edge.Block;
    }

    std::vector<DefOrCallInfo> OldDefs;
    for (auto Var : FilteredFreeVars) {
        if (Constructed.find(Var) == Constructed.end()) {
            // Set the new value to the old value, if it hasn't already been set
            OldDefs.push_back(DefOrCallInfo(
                std::make_shared<Assignment>(Var, name(Var + "_old"))));
        }
    }
    AllDefs.push_back(Assignments(OldDefs, nullptr));
    return AllDefs;
}

/// Filter vars to only include the ones from Program
set<string> filterVars(int Program, set<string> Vars) {
    set<string> FilteredVars;
    string ProgramName = std::to_string(Program);
    for (auto Var : Vars) {
        auto Pos = Var.rfind("$");
        if (Var.substr(Pos + 1, ProgramName.length()) == ProgramName) {
            FilteredVars.insert(Var);
        }
    }
    return FilteredVars;
}

/// Convert a single instruction to an assignment
std::shared_ptr<std::tuple<string, SMTRef>>
toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
      set<string> &Constructed) {
    if (auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        return make_shared<std::tuple<string, SMTRef>>(
            BinOp->getName(),
            makeBinOp(getOpName(*BinOp),
                      getInstrNameOrValue(BinOp->getOperand(0),
                                          BinOp->getOperand(0)->getType(),
                                          Constructed),
                      getInstrNameOrValue(BinOp->getOperand(1),
                                          BinOp->getOperand(1)->getType(),
                                          Constructed)));
    }
    if (auto CmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto Cmp = makeBinOp(
            getPredName(CmpInst->getPredicate()),
            getInstrNameOrValue(CmpInst->getOperand(0),
                                CmpInst->getOperand(0)->getType(), Constructed),
            getInstrNameOrValue(CmpInst->getOperand(1),
                                CmpInst->getOperand(0)->getType(),
                                Constructed));
        return make_shared<std::tuple<string, SMTRef>>(CmpInst->getName(), Cmp);
    }
    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return make_shared<std::tuple<string, SMTRef>>(
            PhiInst->getName(),
            getInstrNameOrValue(Val, Val->getType(), Constructed));
    }
    if (auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        auto Cond = SelectInst->getCondition();
        auto TrueVal = SelectInst->getTrueValue();
        auto FalseVal = SelectInst->getFalseValue();
        std::vector<SMTRef> Args = {
            getInstrNameOrValue(Cond, Cond->getType(), Constructed),
            getInstrNameOrValue(TrueVal, TrueVal->getType(), Constructed),
            getInstrNameOrValue(FalseVal, FalseVal->getType(), Constructed)};
        return make_shared<std::tuple<string, SMTRef>>(
            SelectInst->getName(), std::make_shared<class Op>("ite", Args));
    }
    // errs() << Instr << "\n";
    // errs() << "Couldn't convert instruction to def\n";
    return make_shared<std::tuple<string, SMTRef>>("UNKNOWN INSTRUCTION",
                                                   name("UNKNOWN ARGS"));
}

/// Convert an LLVM op to an SMT op
string getOpName(const llvm::BinaryOperator &Op) {
    switch (Op.getOpcode()) {
    case Instruction::Add:
        return "+";
    case Instruction::Sub:
        return "-";
    case Instruction::Mul:
        return "*";
    case Instruction::SDiv:
        return "div";
    default:
        return Op.getOpcodeName();
    }
}

/// Convert an LLVM predicate to an SMT predicate
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
    case CmpInst::ICMP_NE:
        return "distinct";
    default:
        return "unsupported predicate";
    }
}

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef getInstrNameOrValue(const llvm::Value *Val, const llvm::Type *Ty,
                           set<string> &Constructed) {
    if (auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        auto ApInt = ConstInt->getValue();
        if (ApInt.isIntN(1) && Ty->isIntegerTy(1)) {
            return name(ApInt.getBoolValue() ? "true" : "false");
        }
        if (ApInt.isNegative()) {
            return makeUnaryOp(
                "-", name(ApInt.toString(10, true).substr(1, string::npos)));
        }
        return name(ApInt.toString(10, true));
    }
    if (Constructed.find(Val->getName()) == Constructed.end()) {
        string Name = Val->getName();
        return name(Name + "_old");
    }
    return name(Val->getName());
}

/// Swap the program index
int swapIndex(int I) {
    assert(I == 1 || I == 2);
    return I == 1 ? 2 : 1;
}

/// Convert a basic block to a list of assignments
std::vector<DefOrCallInfo> instrToDefs(const llvm::BasicBlock *BB,
                                       const llvm::BasicBlock *PrevBB,
                                       bool IgnorePhis, bool OnlyPhis,
                                       int Program, set<string> &Constructed) {
    std::vector<DefOrCallInfo> Definitions;
    assert(BB->size() >=
           1); // There should be at least a terminator instruction
    for (auto Instr = BB->begin(), E = std::prev(BB->end(), 1); Instr != E;
         ++Instr) {
        assert(!Instr->getType()->isVoidTy());
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!IgnorePhis && llvm::isa<llvm::PHINode>(Instr)) {
            Definitions.push_back(
                DefOrCallInfo(toDef(*Instr, PrevBB, Constructed)));
            Constructed.insert(Instr->getName());
        }
        if (!OnlyPhis && !llvm::isa<llvm::PHINode>(Instr)) {
            if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(Instr)) {
                Definitions.push_back(
                    DefOrCallInfo(toCallInfo(CallInst->getName(), CallInst)));
            } else {
                Definitions.push_back(
                    DefOrCallInfo(toDef(*Instr, PrevBB, Constructed)));
            }
            Constructed.insert(Instr->getName());
        }
    }
    if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(BB->getTerminator())) {
        string RetName = RetInst->getReturnValue()->getName();
        if (Constructed.find(RetName) == Constructed.end()) {
            RetName += "_old";
        }
        Definitions.push_back(
            DefOrCallInfo(make_shared<std::tuple<string, SMTRef>>(
                "result$" + std::to_string(Program), name(RetName))));
    }
    return Definitions;
}

SMTRef invariant(int StartIndex, int EndIndex, set<string> InputArgs,
                 set<string> EndArgs) {
    // This is the actual invariant we want to establish
    std::vector<string> EndArgsVect;
    for (auto Arg : InputArgs) {
        EndArgsVect.push_back(Arg + "_old");
    }
    EndArgsVect.push_back("result$1");
    EndArgsVect.push_back("result$2");
    auto EndInvariant = makeOp(invName(StartIndex), EndArgsVect);
    auto Clause = EndInvariant;

    if (EndIndex != -2) {
        // We require the result of another call to establish our invariant so
        // make sure that it satisfies the invariant of the other call and then
        // assert our own invariant
        std::vector<SortedVar> ForallArgs;
        ForallArgs.push_back(SortedVar("result$1", "Int"));
        ForallArgs.push_back(SortedVar("result$2", "Int"));
        std::vector<string> UsingArgsVect;
        UsingArgsVect.insert(UsingArgsVect.begin(), EndArgs.begin(),
                             EndArgs.end());
        UsingArgsVect.push_back("result$1");
        UsingArgsVect.push_back("result$2");
        Clause = make_shared<Forall>(
            ForallArgs,
            makeBinOp("=>", makeOp(invName(EndIndex), UsingArgsVect), Clause));
    }
    return Clause;
}

/// Declare an invariant
SMTRef invariantDef(int BlockIndex, set<string> FreeVars) {
    // Add two arguments for the result args
    auto NumArgs = FreeVars.size() + 2;
    std::vector<string> Args(NumArgs, "Int");

    return std::make_shared<class Fun>(invName(BlockIndex), Args, "Bool");
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(set<string> FunArgs, set<string> FunArgs1,
                               set<string> FunArgs2) {
    std::vector<SortedVar> ForallArgs;
    std::vector<string> Args;
    Args.insert(Args.end(), FunArgs.begin(), FunArgs.end());
    for (auto Arg : FunArgs) {
        ForallArgs.push_back(SortedVar(Arg, "Int"));
    }
    ForallArgs.push_back(SortedVar("result$1", "Int"));
    ForallArgs.push_back(SortedVar("result$2", "Int"));
    Args.push_back("result$1");
    Args.push_back("result$2");
    auto EqualResults = makeBinOp("=>", makeOp(invName(-1), Args),
                                  makeBinOp("=", "result$1", "result$2"));
    auto EqualArgs = makeFunArgsEqual(EqualResults, FunArgs1, FunArgs2);
    auto ForallInputs = make_shared<Forall>(ForallArgs, EqualArgs);
    return make_shared<Assert>(ForallInputs);
}

/// Return the invariant name, special casing the entry block
string invName(int Index) {
    if (Index == -1) {
        return "INV_REC";
    }
    return "INV_" + std::to_string(Index);
}

/// Wrap the clause in a forall
SMTRef wrapForall(SMTRef Clause, set<string> FreeVars) {
    std::vector<SortedVar> Vars;
    for (auto &Arg : FreeVars) {
        // TODO(moritz): detect type
        Vars.push_back(SortedVar(Arg + "_old", "Int"));
    }

    if (Vars.empty()) {
        return Clause;
    }
    return llvm::make_unique<Forall>(Vars, Clause);
}

/// Collect the free variables for the entry block of the PathMap
/// A variable is free if we use it but didn't create it
std::pair<set<string>, std::map<int, set<string>>>
freeVars(std::map<int, Paths> PathMap) {
    set<string> FreeVars;
    std::map<int, set<string>> ConstructedIntersection;
    // set<string> ConstructedIntersection;
    for (auto &Paths : PathMap) {
        for (auto &Path : Paths.second) {
            llvm::BasicBlock *Prev = Path.Start;
            set<string> Constructed;

            // the first block is special since we can't resolve phi
            // nodes here
            for (auto &Instr : *Path.Start) {
                Constructed.insert(Instr.getName());
                if (llvm::isa<llvm::PHINode>(Instr)) {
                    FreeVars.insert(Instr.getName());
                    continue;
                }
                if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                    for (unsigned int i = 0; i < CallInst->getNumArgOperands();
                         i++) {
                        auto Arg = CallInst->getArgOperand(i);
                        if (!Arg->getName().empty() &&
                            Constructed.find(Arg->getName()) ==
                                Constructed.end()) {
                            FreeVars.insert(Arg->getName());
                        }
                    }
                    continue;
                }
                for (auto Op : Instr.operand_values()) {
                    if (Constructed.find(Op->getName()) == Constructed.end() &&
                        !Op->getName().empty()) {
                        FreeVars.insert(Op->getName());
                    }
                }
            }

            // now deal with the rest
            for (auto &Edge : Path.Edges) {
                for (auto &Instr : *Edge.Block) {
                    Constructed.insert(Instr.getName());
                    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
                        auto Incoming = PhiInst->getIncomingValueForBlock(Prev);
                        if (Constructed.find(Incoming->getName()) ==
                                Constructed.end() &&
                            !Incoming->getName().empty()) {
                            FreeVars.insert(Incoming->getName());
                        }
                        continue;
                    }
                    if (auto CallInst =
                            llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                        for (unsigned int i = 0;
                             i < CallInst->getNumArgOperands(); i++) {
                            auto Arg = CallInst->getArgOperand(i);
                            if (!Arg->getName().empty() &&
                                Constructed.find(Arg->getName()) ==
                                    Constructed.end()) {
                                FreeVars.insert(Arg->getName());
                            }
                        }
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
                Prev = Edge.Block;
            }

            set<string> NewConstructedIntersection;
            if (ConstructedIntersection.find(Paths.first) ==
                ConstructedIntersection.end()) {
                ConstructedIntersection.insert(
                    make_pair(Paths.first, Constructed));
                ;
            } else {
                std::set_intersection(
                    Constructed.begin(), Constructed.end(),
                    ConstructedIntersection.at(Paths.first).begin(),
                    ConstructedIntersection.at(Paths.first).end(),
                    inserter(NewConstructedIntersection,
                             NewConstructedIntersection.begin()));
                ConstructedIntersection.insert(
                    make_pair(Paths.first, NewConstructedIntersection));
            }
        }
    }
    return std::make_pair(FreeVars, ConstructedIntersection);
}

std::map<int, set<string>> freeVarsMap(PathMap Map1, PathMap Map2,
                                       set<string> FunArgs) {
    std::map<int, set<string>> FreeVarsMap;
    std::map<int, std::map<int, set<string>>> Constructed;
    for (auto &It : Map1) {
        int Index = It.first;
        auto FreeVars1 = freeVars(Map1.at(Index));
        auto FreeVars2 = freeVars(Map2.at(Index));
        for (auto Var : FreeVars2.first) {
            FreeVars1.first.insert(Var);
        }
        FreeVarsMap.insert(make_pair(Index, FreeVars1.first));

        // constructed variables
        for (auto MapIt : FreeVars2.second) {
            for (auto Var : MapIt.second) {
                FreeVars1.second.at(MapIt.first).insert(Var);
            }
        }

        Constructed.insert(make_pair(Index, FreeVars1.second));
    }

    for (auto Arg : FunArgs) {
        FreeVarsMap.at(-1).insert(Arg);
    }
    FreeVarsMap.insert(make_pair(-2, set<string>()));

    // search for a least fixpoint
    // don't tell anyone I wrote that
    bool Changed = true;
    while (Changed) {
        Changed = false;
        for (auto &It : Map1) {
            int StartIndex = It.first;
            for (auto &ItInner : It.second) {
                int EndIndex = ItInner.first;
                for (auto Var : FreeVarsMap.at(EndIndex)) {
                    if (Constructed.at(StartIndex).at(EndIndex).find(Var) ==
                        Constructed.at(StartIndex).at(EndIndex).end()) {
                        auto Inserted = FreeVarsMap.at(StartIndex).insert(Var);
                        Changed = Inserted.second;
                    }
                }
            }
        }
    }

    return FreeVarsMap;
}

std::shared_ptr<CallInfo> toCallInfo(string AssignedTo,
                                     const llvm::CallInst *CallInst) {
    std::vector<SMTRef> Args;
    set<string> Constructed;
    unsigned int i = 0;
    auto FunTy = CallInst->getFunctionType();
    for (auto &Arg : CallInst->arg_operands()) {

        Args.push_back(
            getInstrNameOrValue(Arg, FunTy->getParamType(i), Constructed));
        ++i;
    }
    return make_shared<CallInfo>(AssignedTo, "unknown function", Args);
}
