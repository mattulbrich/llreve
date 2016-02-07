#include "Reve.h"

#include "ADCE.h"
#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "Compat.h"
#include "ConstantProp.h"
#include "Helper.h"
#include "PathAnalysis.h"
#include "InlinePass.h"
#include "InstCombine.h"
#include "RemoveMarkPass.h"
#include "RemoveMarkRefsPass.h"
#include "SExpr.h"
#include "SMT.h"
#include "SMTGeneration.h"
#include "SplitEntryBlockPass.h"
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
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include <fstream>
#include <iostream>

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
using std::vector;

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
    ShowMarkedCFG("show-marked-cfg",
                  llvm::cl::desc("Show cfg before mark removal"));
static llvm::cl::opt<bool>
    OffByN("off-by-n", llvm::cl::desc("Allow loops to be off by n iterations"));
static llvm::cl::opt<bool>
    OnlyRec("only-rec", llvm::cl::desc("Only generate recursive invariants"));
static llvm::cl::opt<bool> Heap("heap", llvm::cl::desc("Enable heaps"));
static llvm::cl::opt<bool> Stack("stack", llvm::cl::desc("Enable stacks"));
static llvm::cl::opt<bool> Strings("strings",
                                   llvm::cl::desc("Enable string constants"));
static llvm::cl::opt<string>
    Fun("fun", llvm::cl::desc("Function which should be verified"));
static llvm::cl::opt<string> Include("I", llvm::cl::desc("Include path"));
static llvm::cl::opt<bool>
    Signed("signed",
           llvm::cl::desc("Treat all operations as signed operatons"));
static llvm::cl::opt<bool> DontNest("dont-nest",
                                    llvm::cl::desc("Don’t nest clauses"));

/// Initialize the argument vector to produce the llvm assembly for
/// the two C files
std::vector<const char *> initializeArgs(const char *ExeName, string Input1,
                                         string Input2) {
    std::vector<const char *> Args;
    Args.push_back(ExeName); // add executable name
    Args.push_back("-xc");   // force language to C
    Args.push_back("-std=c99");
    if (!Include.empty()) {
        char *NewInclude = static_cast<char *>(malloc(Include.length() + 1));
        memcpy(static_cast<void *>(NewInclude), Include.data(),
               Include.length() + 1);
        Args.push_back("-I");
        Args.push_back(NewInclude);
    }
    // archlinux migrated to the new gcc api and something is completely broken
    // so don’t use c_str here but instead allocate a new string and leak it
    // like a boss
    char *NewInput1 = static_cast<char *>(malloc(Input1.length() + 1));
    memcpy(static_cast<void *>(NewInput1), Input1.data(), Input1.length() + 1);
    char *NewInput2 = static_cast<char *>(malloc(Input2.length() + 1));
    memcpy(static_cast<void *>(NewInput2), Input2.data(), Input2.length() + 1);
    Args.push_back(NewInput1);       // add input file
    Args.push_back(NewInput2);       // add input file
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
    auto Driver =
        llvm::make_unique<clang::driver::Driver>("clang", Triple.str(), Diags);
    Driver->setTitle("reve");
    Driver->setCheckInputsExist(false);
    return Driver;
}

/// This creates the compilations commands to compile to assembly
ErrorOr<std::pair<ArgStringList, ArgStringList>>
getCmd(Compilation &Comp, DiagnosticsEngine &Diags) {
    const JobList &Jobs = Comp.getJobs();

    // there should be exactly two jobs
    if (Jobs.size() != 2) {
        llvm::SmallString<256> Msg;
        llvm::raw_svector_ostream OS(Msg);
        Jobs.Print(OS, "; ", true);
        Diags.Report(clang::diag::err_fe_expected_compiler_job) << OS.str();
        return ErrorOr<std::pair<ArgStringList, ArgStringList>>(
            std::error_code());
    }

    return makeErrorOr(std::make_pair(Jobs.begin()->getArguments(),
                                      std::next(Jobs.begin())->getArguments()));
}

/// Wrapper function to allow inferenece of template parameters
template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }

/// Compile the inputs to llvm assembly and return those modules
std::pair<unique_ptr<clang::CodeGenAction>, unique_ptr<clang::CodeGenAction>>
getModule(const char *ExeName, string Input1, string Input2) {
    auto Diags = initializeDiagnostics();
    auto Driver = initializeDriver(*Diags);
    auto Args = initializeArgs(ExeName, Input1, Input2);

    std::unique_ptr<Compilation> Comp(Driver->BuildCompilation(Args));
    if (!Comp) {
        return std::make_pair(nullptr, nullptr);
    }

    auto CmdArgsOrError = getCmd(*Comp, *Diags);
    if (!CmdArgsOrError) {
        return std::make_pair(nullptr, nullptr);
    }
    auto CmdArgs = CmdArgsOrError.get();

    auto Act1 = getCodeGenAction(CmdArgs.first, *Diags);
    auto Act2 = getCodeGenAction(CmdArgs.second, *Diags);
    if (!Act1 || !Act2) {
        return std::make_pair(nullptr, nullptr);
    }

    return std::make_pair(std::move(Act1), std::move(Act2));
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
        logError("Couldn’t enable diagnostics\n");
        exit(1);
    }
    std::unique_ptr<CodeGenAction> Act =
        llvm::make_unique<clang::EmitLLVMOnlyAction>();
    if (!Clang.ExecuteAction(*Act)) {
        logError("Couldn’t execute action\n");
        exit(1);
    }
    return Act;
}

std::pair<SMTRef, SMTRef> parseInOutInvs(std::string FileName1,
                                         std::string FileName2) {
    SMTRef In = nullptr;
    SMTRef Out = nullptr;
    std::ifstream FileStream1(FileName1);
    std::string FileString1((std::istreambuf_iterator<char>(FileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream FileStream2(FileName2);
    std::string FileString2((std::istreambuf_iterator<char>(FileStream2)),
                            std::istreambuf_iterator<char>());

    processFile(FileString1, In, Out);
    processFile(FileString2, In, Out);

    return std::make_pair(In, Out);
}

void processFile(std::string File, SMTRef &In, SMTRef &Out) {
    std::regex RelinRegex(
        "/\\*@\\s*rel_in\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::regex ReloutRegex(
        "/\\*@\\s*rel_out\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::smatch Match;
    if (std::regex_search(File, Match, RelinRegex) && In == nullptr) {
        std::string MatchStr = Match[2];
        In = name("(" + MatchStr + ")");
    }
    if (std::regex_search(File, Match, ReloutRegex) && Out == nullptr) {
        std::string MatchStr = Match[2];
        Out = name("(" + MatchStr + ")");
    }
}

int main(int Argc, const char **Argv) {
    // The actual arguments are declared statically so we don't need
    // to pass those in here
    llvm::cl::ParseCommandLineOptions(Argc, Argv, "reve\n");

    auto ActPair = getModule(Argv[0], FileName1, FileName2);
    const auto Act1 = std::move(ActPair.first);
    const auto Act2 = std::move(ActPair.second);
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

    std::vector<std::pair<std::shared_ptr<llvm::FunctionAnalysisManager>,
                          std::shared_ptr<llvm::FunctionAnalysisManager>>> Fams;
    for (auto FunPair : Funs.get()) {
        auto Fam1 = preprocessFunction(*FunPair.first, "1");
        auto Fam2 = preprocessFunction(*FunPair.second, "2");
        Fams.push_back(make_pair(Fam1, Fam2));
    }

    Memory Mem = 0;
    if (Heap || doesAccessMemory(*Mod1) || doesAccessMemory(*Mod2)) {
        Mem |= HEAP_MASK;
    }
    if (Stack) {
        Mem |= STACK_MASK;
    }

    std::pair<SMTRef, SMTRef> InOutInvs = parseInOutInvs(FileName1, FileName2);

    auto FunCondMap = collectFunConds();

    externDeclarations(*Mod1, *Mod2, Declarations, Mem, FunCondMap);
    if (Fun == "" && !Funs.get().empty()) {
        Fun = Funs.get().at(0).first->getName();
    }

    auto GlobalDeclarations = globalDeclarations(*Mod1, *Mod2);
    SMTExprs.insert(SMTExprs.end(), GlobalDeclarations.begin(),
                    GlobalDeclarations.end());

    for (auto FunPair : makeZip(Funs.get(), Fams)) {
        if (FunPair.first.first->getName() == Fun) {
            SMTExprs.push_back(
                inInvariant(*FunPair.first.first, *FunPair.first.second,
                            InOutInvs.first, Mem, *Mod1, *Mod2, Strings));
            SMTExprs.push_back(outInvariant(InOutInvs.second, Mem));
            auto NewSMTExprs = mainAssertion(
                *FunPair.first.first, *FunPair.first.second,
                FunPair.second.first, FunPair.second.second, OffByN,
                Declarations, OnlyRec, Mem, Signed, DontNest);
            Assertions.insert(Assertions.end(), NewSMTExprs.begin(),
                              NewSMTExprs.end());
        }
        if (FunPair.first.first->getName() != Fun ||
            (!(doesNotRecurse(*FunPair.first.first) &&
               doesNotRecurse(*FunPair.first.second)) ||
             OnlyRec)) {
            auto NewSMTExprs =
                convertToSMT(*FunPair.first.first, *FunPair.first.second,
                             FunPair.second.first, FunPair.second.second,
                             OffByN, Declarations, Mem, Signed);
            Assertions.insert(Assertions.end(), NewSMTExprs.begin(),
                              NewSMTExprs.end());
        }
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

shared_ptr<llvm::FunctionAnalysisManager>
preprocessFunction(llvm::Function &Fun, string Prefix) {
    llvm::PassBuilder PB;
    auto FAM =
        make_shared<llvm::FunctionAnalysisManager>(true); // enable debug log
    PB.registerFunctionAnalyses(*FAM); // register basic analyses
    FAM->registerPass(UnifyFunctionExitNodes());

    llvm::FunctionPassManager FPM(true); // enable debug log

    FPM.addPass(InlinePass());
    FPM.addPass(PromotePass()); // mem2reg
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(SplitEntryBlockPass());
    FAM->registerPass(MarkAnalysis());
    FPM.addPass(RemoveMarkRefsPass());
    FPM.addPass(InstCombinePass());
    FPM.addPass(ADCEPass());
    FPM.addPass(ConstantProp());
    FAM->registerPass(PathAnalysis());
    FPM.addPass(UniqueNamePass(Prefix)); // prefix register names
    if (ShowMarkedCFG) {
        FPM.addPass(CFGViewerPass()); // show marked cfg
    }
    FPM.addPass(RemoveMarkPass());
    if (ShowCFG) {
        FPM.addPass(CFGViewerPass()); // show cfg
    }
    FPM.addPass(AnnotStackPass()); // annotate load/store of stack variables
    FPM.addPass(llvm::VerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    FPM.run(Fun, FAM.get());

    return FAM;
}

ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>
zipFunctions(llvm::Module &Mod1, llvm::Module &Mod2) {
    std::vector<std::pair<llvm::Function *, llvm::Function *>> Funs;
    int Size1 = 0;
    int Size2 = 0;
    for (auto &Fun : Mod1) {
        if (!Fun.isDeclaration()) {
            ++Size1;
        }
    }
    for (auto &Fun : Mod2) {
        if (!Fun.isDeclaration()) {
            ++Size2;
        }
    }
    if (Size1 != Size2) {
        logWarning("Number of functions is not equal\n");
    }
    for (auto &Fun1 : Mod1) {
        if (Fun1.isDeclaration()) {
            continue;
        }
        auto Fun2 = Mod2.getFunction(Fun1.getName());
        if (!Fun2) {
            logWarning("No corresponding function for " + Fun1.getName() +
                       "\n");
            continue;
        }
        Funs.push_back(std::make_pair(&Fun1, Fun2));
    }
    return ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>(
        Funs);
}

void externDeclarations(llvm::Module &Mod1, llvm::Module &Mod2,
                        std::vector<SMTRef> &Declarations, Memory Mem,
                        std::multimap<string, string> FunCondMap) {
    for (auto &Fun1 : Mod1) {
        if (Fun1.isDeclaration() && !Fun1.isIntrinsic()) {
            auto Fun2P = Mod2.getFunction(Fun1.getName());
            if (Fun2P && Fun1.getName() != "__mark") {
                llvm::Function &Fun2 = *Fun2P;
                // Calculate the number of varargs used in function calls
                set<uint32_t> VarArgs = varArgs(Fun1);
                set<uint32_t> VarArgs2 = varArgs(Fun2);
                for (auto El : VarArgs2) {
                    VarArgs.insert(El);
                }
                for (auto ArgNum : VarArgs) {
                    std::vector<SortedVar> Args;
                    auto FunArgs1 = funArgs(Fun1, "arg1_", ArgNum);
                    for (auto Arg : FunArgs1) {
                        Args.push_back(Arg);
                    }
                    if (Mem & HEAP_MASK) {
                        Args.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
                    }
                    auto FunArgs2 = funArgs(Fun2, "arg2_", ArgNum);
                    for (auto Arg : FunArgs2) {
                        Args.push_back(Arg);
                    }
                    if (Mem) {
                        Args.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
                    }
                    std::string FunName = invariantName(
                        ENTRY_MARK, Program::Both, Fun1.getName().str(), ArgNum);
                    Args.push_back(SortedVar("res1", "Int"));
                    Args.push_back(SortedVar("res2", "Int"));
                    if (Mem & HEAP_MASK) {
                        Args.push_back(
                            SortedVar("HEAP$1_res", "(Array Int Int)"));
                        Args.push_back(
                            SortedVar("HEAP$2_res", "(Array Int Int)"));
                    }
                    SMTRef Body = makeBinOp("=", "res1", "res2");
                    if (Mem & HEAP_MASK) {
                        std::vector<SortedVar> ForallArgs = {
                            SortedVar("i", "Int")};
                        SMTRef HeapOutEqual = make_shared<Forall>(
                            ForallArgs,
                            makeBinOp("=",
                                      makeBinOp("select", "HEAP$1_res", "i"),
                                      makeBinOp("select", "HEAP$2_res", "i")));
                        Body = makeBinOp("and", Body, HeapOutEqual);
                    }
                    std::vector<SMTRef> EqualOut;
                    auto Range = FunCondMap.equal_range(Fun1.getName());
                    for (auto I = Range.first; I != Range.second; ++I) {
                        EqualOut.push_back(name(I->second));
                    }
                    if (!EqualOut.empty()) {
                        EqualOut.push_back(Body);
                        Body = make_shared<Op>("and", EqualOut);
                    }
                    std::vector<SMTRef> Equal;
                    for (auto It1 = FunArgs1.begin(), It2 = FunArgs2.begin();
                         It1 != FunArgs1.end() && It2 != FunArgs2.end();
                         ++It1) {
                        Equal.push_back(makeBinOp("=", It1->Name, It2->Name));
                        ++It2;
                    }
                    if (Mem & HEAP_MASK) {
                        std::vector<SortedVar> ForallArgs = {
                            SortedVar("i", "Int")};
                        SMTRef HeapInEqual = make_shared<Forall>(
                            ForallArgs,
                            makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                      makeBinOp("select", "HEAP$2", "i")));
                        Equal.push_back(HeapInEqual);
                    }
                    Body = makeBinOp("=>", make_shared<Op>("and", Equal), Body);
                    SMTRef MainInv =
                        make_shared<FunDef>(FunName, Args, "Bool", Body);
                    Declarations.push_back(MainInv);
                }
            }
        }
    }
    for (auto &Fun1 : Mod1) {
        if (Fun1.isDeclaration() && !Fun1.isIntrinsic() &&
            Fun1.getName() != "__mark") {
            auto Decls = externFunDecl(Fun1, 1, Mem);
            Declarations.insert(Declarations.end(), Decls.begin(), Decls.end());
        }
    }
    for (auto &Fun2 : Mod2) {
        if (Fun2.isDeclaration() && !Fun2.isIntrinsic() &&
            Fun2.getName() != "__mark") {
            auto Decls = externFunDecl(Fun2, 2, Mem);
            Declarations.insert(Declarations.end(), Decls.begin(), Decls.end());
        }
    }
}

std::set<uint32_t> varArgs(llvm::Function &Fun) {
    std::set<uint32_t> VarArgs;
    for (auto User : Fun.users()) {
        if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(User)) {
            VarArgs.insert(CallInst->getNumArgOperands() -
                           Fun.getFunctionType()->getNumParams());
        } else {
            logWarningData("Unsupported use of function\n", *User);
        }
    }
    return VarArgs;
}

std::vector<SortedVar> funArgs(llvm::Function &Fun, std::string Prefix,
                               uint32_t VarArgs) {
    std::vector<SortedVar> Args;
    int ArgIndex = 0;
    for (auto &Arg : Fun.getArgumentList()) {
        if (Arg.getName().empty()) {
            Arg.setName(Prefix + std::to_string(ArgIndex++));
        }
        Args.push_back(SortedVar(Arg.getName(), "Int"));
    }
    for (uint32_t i = 0; i < VarArgs; ++i) {
        Args.push_back(SortedVar("var" + Prefix + std::to_string(i), "Int"));
    }
    return Args;
}

std::vector<SMTRef> externFunDecl(llvm::Function &Fun, int Program,
                                  Memory Mem) {
    std::vector<SMTRef> Decls;
    set<uint32_t> VarArgs = varArgs(Fun);
    for (auto ArgNum : VarArgs) {
        std::vector<SortedVar> Args = funArgs(Fun, "arg_", ArgNum);
        if (Mem) {
            Args.push_back(SortedVar("HEAP", "(Array Int Int)"));
        }
        Args.push_back(SortedVar("res", "Int"));
        Args.push_back(SortedVar("HEAP_res", "(Array Int Int)"));
        std::string FunName = invariantName(
            ENTRY_MARK, Program == 1 ? Program::First : Program::Second,
            Fun.getName().str(), ArgNum);
        SMTRef Body = name("true");
        Decls.push_back(make_shared<FunDef>(FunName, Args, "Bool", Body));
    }
    return Decls;
}

// this does not actually check if the function recurses but the next version of
// llvm provides a function for that and I’m too lazy to implement it myself
bool doesNotRecurse(llvm::Function &Fun) {
    for (auto &BB : Fun) {
        for (auto &Inst : BB) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                const auto CalledFun = CallInst->getCalledFunction();
                if (CalledFun && !CalledFun->isDeclaration()) {
                    return false;
                }
            }
        }
    }
    return true;
}

bool doesAccessMemory(const llvm::Module &Mod) {
    for (auto &Fun : Mod) {
        for (auto &BB : Fun) {
            for (auto &Instr : BB) {
                if (llvm::isa<llvm::LoadInst>(&Instr) ||
                    llvm::isa<llvm::StoreInst>(&Instr)) {
                    return true;
                }
            }
        }
    }
    return false;
}

vector<SMTRef> globalDeclarationsForMod(int GlobalPointer, llvm::Module &Mod,
                                        llvm::Module &ModOther, int Program) {
    std::vector<SMTRef> Declarations;
    for (auto &Global1 : Mod.globals()) {
        std::string GlobalName = Global1.getName();
        if (!ModOther.getNamedGlobal(GlobalName)) {
            // we want the size of string constants not the size of the pointer
            // pointing to them
            if (const auto PointerTy =
                    llvm::dyn_cast<llvm::PointerType>(Global1.getType())) {
                GlobalPointer += typeSize(PointerTy->getElementType());
            } else {
                GlobalPointer += typeSize(Global1.getType());
            }
            std::vector<SortedVar> Empty;
            auto ConstDef1 = make_shared<FunDef>(
                GlobalName + "$" + std::to_string(Program), Empty, "Int",
                makeUnaryOp("-", std::to_string(GlobalPointer)));
            Declarations.push_back(ConstDef1);
        }
    }
    return Declarations;
}
std::vector<SMTRef> globalDeclarations(llvm::Module &Mod1, llvm::Module &Mod2) {
    // First match globals with the same name to make sure that they get the
    // same pointer, then match globals that only exist in one module
    std::vector<SMTRef> Declarations;
    int GlobalPointer = 1;
    for (auto &Global1 : Mod1.globals()) {
        std::string GlobalName = Global1.getName();
        if (Mod2.getNamedGlobal(GlobalName)) {
            // we want the size of string constants not the size of the pointer
            // pointing to them
            if (const auto PointerTy =
                    llvm::dyn_cast<llvm::PointerType>(Global1.getType())) {
                GlobalPointer += typeSize(PointerTy->getElementType());
            } else {
                GlobalPointer += typeSize(Global1.getType());
            }
            std::vector<SortedVar> Empty;
            auto ConstDef1 = make_shared<FunDef>(
                GlobalName + "$1", Empty, "Int",
                makeUnaryOp("-", std::to_string(GlobalPointer)));
            auto ConstDef2 = make_shared<FunDef>(
                GlobalName + "$2", Empty, "Int",
                makeUnaryOp("-", std::to_string(GlobalPointer)));
            Declarations.push_back(ConstDef1);
            Declarations.push_back(ConstDef2);
        }
    }
    auto Decls1 = globalDeclarationsForMod(GlobalPointer, Mod1, Mod2, 1);
    auto Decls2 = globalDeclarationsForMod(GlobalPointer, Mod2, Mod1, 2);
    Declarations.insert(Declarations.end(), Decls1.begin(), Decls1.end());
    Declarations.insert(Declarations.end(), Decls2.begin(), Decls2.end());
    for (auto &Global1 : Mod1.globals()) {
        Global1.setName(Global1.getName() + "$1");
    }
    for (auto &Global2 : Mod2.globals()) {
        Global2.setName(Global2.getName() + "$2");
    }
    return Declarations;
}

std::multimap<string, string> collectFunConds() {
    std::multimap<string, string> Map;
    std::ifstream FileStream1(FileName1);
    std::string FileString1((std::istreambuf_iterator<char>(FileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream FileStream2(FileName2);
    std::string FileString2((std::istreambuf_iterator<char>(FileStream2)),
                            std::istreambuf_iterator<char>());
    auto Map1 = collectFunCondsInFile(FileString1);
    auto Map2 = collectFunCondsInFile(FileString2);
    std::merge(Map1.begin(), Map1.end(), Map2.begin(), Map2.end(),
               std::inserter(Map, std::end(Map)));
    return Map;
}

std::multimap<string, string> collectFunCondsInFile(std::string File) {
    std::multimap<string, string> Map;
    std::regex CondRegex(
        "/\\*@\\s*addfuncond\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    for (std::sregex_iterator
             I = std::sregex_iterator(File.begin(), File.end(), CondRegex),
             E = std::sregex_iterator();
         I != E; ++I) {
        std::smatch match = *I;
        std::string match_str = match[2];
        Map.insert(make_pair(match[1], "(" + match_str + ")"));
    }
    return Map;
}
