#include "Reve.h"

#include "ADCE.h"
#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "Compat.h"
#include "ConstantProp.h"
#include "Helper.h"
#include "InlinePass.h"
#include "InstCombine.h"
#include "Invariant.h"
#include "RemoveMarkPass.h"
#include "RemoveMarkRefsPass.h"
#include "SMTGeneration.h"
#include "SplitEntryBlockPass.h"
#include "UnifyFunctionExitNodes.h"
#include "UniqueNamePass.h"

#include "clang/Driver/Compilation.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"

#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/Constants.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/TargetSelect.h"
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

static llvm::cl::opt<string> fileName1(llvm::cl::Positional,
                                       llvm::cl::desc("Input file 1"),
                                       llvm::cl::Required);
static llvm::cl::opt<string> fileName2(llvm::cl::Positional,
                                       llvm::cl::desc("Input file 2"),
                                       llvm::cl::Required);
static llvm::cl::opt<string>
    outputFileName("o", llvm::cl::desc("SMT output filename"),
                   llvm::cl::value_desc("filename"));
static llvm::cl::opt<bool> showCfg("show-cfg", llvm::cl::desc("Show cfg"));
static llvm::cl::opt<bool>
    showMarkedCfg("show-marked-cfg",
                  llvm::cl::desc("Show cfg before mark removal"));
static llvm::cl::opt<bool>
    offByN("off-by-n", llvm::cl::desc("Allow loops to be off by n iterations"));
static llvm::cl::opt<bool>
    onlyRec("only-rec", llvm::cl::desc("Only generate recursive invariants"));
static llvm::cl::opt<bool> heap("heap", llvm::cl::desc("Enable heaps"));
static llvm::cl::opt<bool> stack("stack", llvm::cl::desc("Enable stacks"));
static llvm::cl::opt<bool> strings("strings",
                                   llvm::cl::desc("Enable string constants"));
static llvm::cl::opt<string>
    fun("fun", llvm::cl::desc("Function which should be verified"));
static llvm::cl::opt<string> include("I", llvm::cl::desc("Include path"));
static llvm::cl::opt<bool> EverythingSigned(
    "signed", llvm::cl::desc("Treat all operations as signed operatons"));
static llvm::cl::opt<bool> dontNest("dont-nest",
                                    llvm::cl::desc("Don’t nest clauses"));

/// Initialize the argument vector to produce the llvm assembly for
/// the two C files
std::vector<const char *> initializeArgs(const char *exeName, string input1,
                                         string input2) {
    std::vector<const char *> args;
    args.push_back(exeName); // add executable name
    args.push_back("-xc");   // force language to C
    args.push_back("-std=c99");
    if (!include.empty()) {
        char *newInclude = static_cast<char *>(malloc(include.length() + 1));
        memcpy(static_cast<void *>(newInclude), include.data(),
               include.length() + 1);
        args.push_back("-I");
        args.push_back(newInclude);
    }
    // archlinux migrated to the new gcc api and something is completely broken
    // so don’t use c_str here but instead allocate a new string and leak it
    // like a boss
    char *newInput1 = static_cast<char *>(malloc(input1.length() + 1));
    memcpy(static_cast<void *>(newInput1), input1.data(), input1.length() + 1);
    char *newInput2 = static_cast<char *>(malloc(input2.length() + 1));
    memcpy(static_cast<void *>(newInput2), input2.data(), input2.length() + 1);
    args.push_back(newInput1);       // add input file
    args.push_back(newInput2);       // add input file
    args.push_back("-fsyntax-only"); // don't do more work than necessary
    return args;
}

/// Set up the diagnostics engine
unique_ptr<DiagnosticsEngine> initializeDiagnostics() {
    const IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts =
        new clang::DiagnosticOptions();
    auto diagClient =
        new clang::TextDiagnosticPrinter(llvm::errs(), &*diagOpts);
    const IntrusiveRefCntPtr<clang::DiagnosticIDs> diagId(
        new clang::DiagnosticIDs());
    return llvm::make_unique<DiagnosticsEngine>(diagId, &*diagOpts, diagClient);
}

/// Initialize the driver
unique_ptr<Driver> initializeDriver(DiagnosticsEngine &diags) {
    string tripleStr = llvm::sys::getProcessTriple();
    llvm::Triple triple(tripleStr);
    auto driver =
        llvm::make_unique<clang::driver::Driver>("clang", triple.str(), diags);
    driver->setTitle("reve");
    driver->setCheckInputsExist(false);
    return driver;
}

/// This creates the compilations commands to compile to assembly
ErrorOr<std::pair<ArgStringList, ArgStringList>>
getCmd(Compilation &comp, DiagnosticsEngine &diags) {
    const JobList &jobs = comp.getJobs();

    // there should be exactly two jobs
    if (jobs.size() != 2) {
        llvm::SmallString<256> msg;
        llvm::raw_svector_ostream os(msg);
        jobs.Print(os, "; ", true);
        diags.Report(clang::diag::err_fe_expected_compiler_job) << os.str();
        return ErrorOr<std::pair<ArgStringList, ArgStringList>>(
            std::error_code());
    }

    return makeErrorOr(std::make_pair(jobs.begin()->getArguments(),
                                      std::next(jobs.begin())->getArguments()));
}

/// Wrapper function to allow inferenece of template parameters
template <typename T> ErrorOr<T> makeErrorOr(T Arg) { return ErrorOr<T>(Arg); }

/// Compile the inputs to llvm assembly and return those modules
std::pair<unique_ptr<clang::CodeGenAction>, unique_ptr<clang::CodeGenAction>>
getModule(const char *exeName, string input1, string input2) {
    auto diags = initializeDiagnostics();
    auto driver = initializeDriver(*diags);
    auto args = initializeArgs(exeName, input1, input2);

    std::unique_ptr<Compilation> comp(driver->BuildCompilation(args));
    if (!comp) {
        return std::make_pair(nullptr, nullptr);
    }

    auto cmdArgsOrError = getCmd(*comp, *diags);
    if (!cmdArgsOrError) {
        return std::make_pair(nullptr, nullptr);
    }
    auto cmdArgs = cmdArgsOrError.get();

    auto act1 = getCodeGenAction(cmdArgs.first, *diags);
    auto act2 = getCodeGenAction(cmdArgs.second, *diags);
    if (!act1 || !act2) {
        return std::make_pair(nullptr, nullptr);
    }

    return std::make_pair(std::move(act1), std::move(act2));
}

/// Build the CodeGenAction corresponding to the arguments
std::unique_ptr<CodeGenAction>
getCodeGenAction(const ArgStringList &ccArgs, clang::DiagnosticsEngine &diags) {
    auto ci = llvm::make_unique<CompilerInvocation>();
    CompilerInvocation::CreateFromArgs(*ci, (ccArgs.data()),
                                       (ccArgs.data()) + ccArgs.size(), diags);
    CompilerInstance clang;
    clang.setInvocation(ci.release());
    clang.createDiagnostics();
    if (!clang.hasDiagnostics()) {
        logError("Couldn’t enable diagnostics\n");
        exit(1);
    }
    std::unique_ptr<CodeGenAction> act =
        llvm::make_unique<clang::EmitLLVMOnlyAction>();
    if (!clang.ExecuteAction(*act)) {
        logError("Couldn’t execute action\n");
        exit(1);
    }
    return act;
}

std::pair<SMTRef, SMTRef> parseInOutInvs(std::string fileName1,
                                         std::string fileName2) {
    SMTRef in = nullptr;
    SMTRef out = nullptr;
    std::ifstream fileStream1(fileName1);
    std::string fileString1((std::istreambuf_iterator<char>(fileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream fileStream2(fileName2);
    std::string fileString2((std::istreambuf_iterator<char>(fileStream2)),
                            std::istreambuf_iterator<char>());

    processFile(fileString1, in, out);
    processFile(fileString2, in, out);

    return std::make_pair(in, out);
}

void processFile(std::string file, SMTRef &in, SMTRef &out) {
    std::regex relinRegex(
        "/\\*@\\s*rel_in\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::regex reloutRegex(
        "/\\*@\\s*rel_out\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::smatch match;
    if (std::regex_search(file, match, relinRegex) && in == nullptr) {
        std::string matchStr = match[2];
        in = name("(" + matchStr + ")");
    }
    if (std::regex_search(file, match, reloutRegex) && out == nullptr) {
        std::string matchStr = match[2];
        out = name("(" + matchStr + ")");
    }
}

int main(int argc, const char **argv) {
    // The actual arguments are declared statically so we don't need
    // to pass those in here
    llvm::cl::ParseCommandLineOptions(argc, argv, "reve\n");

    auto actPair = getModule(argv[0], fileName1, fileName2);
    const auto act1 = std::move(actPair.first);
    const auto act2 = std::move(actPair.second);
    if (!act1 || !act2) {
        return 1;
    }

    const auto mod1 = act1->takeModule();
    const auto mod2 = act2->takeModule();
    if (!mod1 || !mod2) {
        return 1;
    }

    ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>> funs =
        zipFunctions(*mod1, *mod2);

    if (!funs) {
        errs() << "Couldn't find matching functions\n";
        return 1;
    }

    std::vector<SMTRef> declarations;
    std::vector<SMTRef> assertions;
    std::vector<SMTRef> smtExprs;
    smtExprs.push_back(std::make_shared<SetLogic>("HORN"));

    std::vector<std::pair<std::shared_ptr<llvm::FunctionAnalysisManager>,
                          std::shared_ptr<llvm::FunctionAnalysisManager>>> fams;
    for (auto funPair : funs.get()) {
        auto fam1 = preprocessFunction(*funPair.first, "1");
        auto fam2 = preprocessFunction(*funPair.second, "2");
        fams.push_back(make_pair(fam1, fam2));
    }

    Memory mem = 0;
    if (heap || doesAccessMemory(*mod1) || doesAccessMemory(*mod2)) {
        mem |= HEAP_MASK;
    }
    if (stack) {
        mem |= STACK_MASK;
    }

    std::pair<SMTRef, SMTRef> inOutInvs = parseInOutInvs(fileName1, fileName2);

    auto funCondMap = collectFunConds();

    externDeclarations(*mod1, *mod2, declarations, mem, funCondMap);
    if (fun == "" && !funs.get().empty()) {
        fun = funs.get().at(0).first->getName();
    }

    auto globalDecls = globalDeclarations(*mod1, *mod2);
    smtExprs.insert(smtExprs.end(), globalDecls.begin(), globalDecls.end());

    for (auto funPair : makeZip(funs.get(), fams)) {
        if (funPair.first.first->getName() == fun) {
            smtExprs.push_back(
                inInvariant(*funPair.first.first, *funPair.first.second,
                            inOutInvs.first, mem, *mod1, *mod2, strings));
            smtExprs.push_back(outInvariant(inOutInvs.second, mem));
            auto newSmtExprs = mainAssertion(
                *funPair.first.first, *funPair.first.second,
                funPair.second.first, funPair.second.second, offByN,
                declarations, onlyRec, mem, EverythingSigned, dontNest);
            assertions.insert(assertions.end(), newSmtExprs.begin(),
                              newSmtExprs.end());
        }
        if (funPair.first.first->getName() != fun ||
            (!(doesNotRecurse(*funPair.first.first) &&
               doesNotRecurse(*funPair.first.second)) ||
             onlyRec)) {
            auto newSmtExprs =
                convertToSMT(*funPair.first.first, *funPair.first.second,
                             funPair.second.first, funPair.second.second,
                             offByN, declarations, mem, EverythingSigned);
            assertions.insert(assertions.end(), newSmtExprs.begin(),
                              newSmtExprs.end());
        }
    }
    smtExprs.insert(smtExprs.end(), declarations.begin(), declarations.end());
    smtExprs.insert(smtExprs.end(), assertions.begin(), assertions.end());
    smtExprs.push_back(make_shared<CheckSat>());
    smtExprs.push_back(make_shared<GetModel>());

    // write to file or to stdout
    std::streambuf *buf;
    std::ofstream ofStream;

    if (!outputFileName.empty()) {
        ofStream.open(outputFileName);
        buf = ofStream.rdbuf();
    } else {
        buf = std::cout.rdbuf();
    }

    std::ostream outFile(buf);

    for (auto &smt : smtExprs) {
        outFile << *smt->compressLets()->toSExpr();
        outFile << "\n";
    }

    if (!outputFileName.empty()) {
        ofStream.close();
    }

    llvm::llvm_shutdown();

    return 0;
}

shared_ptr<llvm::FunctionAnalysisManager>
preprocessFunction(llvm::Function &fun, string prefix) {
    llvm::PassBuilder pb;
    auto fam =
        make_shared<llvm::FunctionAnalysisManager>(true); // enable debug log
    pb.registerFunctionAnalyses(*fam); // register basic analyses
    fam->registerPass(UnifyFunctionExitNodes());

    llvm::FunctionPassManager fpm(true); // enable debug log

    fpm.addPass(InlinePass());
    fpm.addPass(PromotePass()); // mem2reg
    fpm.addPass(llvm::SimplifyCFGPass());
    fpm.addPass(SplitEntryBlockPass());
    fam->registerPass(MarkAnalysis());
    fpm.addPass(RemoveMarkRefsPass());
    fpm.addPass(InstCombinePass());
    fpm.addPass(ADCEPass());
    fpm.addPass(ConstantProp());
    fam->registerPass(PathAnalysis());
    fpm.addPass(UniqueNamePass(prefix)); // prefix register names
    if (showMarkedCfg) {
        fpm.addPass(CFGViewerPass()); // show marked cfg
    }
    fpm.addPass(RemoveMarkPass());
    if (showCfg) {
        fpm.addPass(CFGViewerPass()); // show cfg
    }
    fpm.addPass(AnnotStackPass()); // annotate load/store of stack variables
    fpm.addPass(llvm::VerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    fpm.run(fun, fam.get());

    return fam;
}

ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>
zipFunctions(llvm::Module &mod1, llvm::Module &mod2) {
    std::vector<std::pair<llvm::Function *, llvm::Function *>> funs;
    int size1 = 0;
    int size2 = 0;
    for (auto &fun : mod1) {
        if (!fun.isDeclaration()) {
            ++size1;
        }
    }
    for (auto &fun : mod2) {
        if (!fun.isDeclaration()) {
            ++size2;
        }
    }
    if (size1 != size2) {
        logWarning("Number of functions is not equal\n");
    }
    for (auto &Fun1 : mod1) {
        if (Fun1.isDeclaration()) {
            continue;
        }
        auto fun2 = mod2.getFunction(Fun1.getName());
        if (!fun2) {
            logWarning("No corresponding function for " + Fun1.getName() +
                       "\n");
            continue;
        }
        funs.push_back(std::make_pair(&Fun1, fun2));
    }
    return ErrorOr<std::vector<std::pair<llvm::Function *, llvm::Function *>>>(
        funs);
}

void externDeclarations(llvm::Module &mod1, llvm::Module &mod2,
                        std::vector<SMTRef> &declarations, Memory mem,
                        std::multimap<string, string> funCondMap) {
    for (auto &fun1 : mod1) {
        if (fun1.isDeclaration() && !fun1.isIntrinsic()) {
            auto fun2P = mod2.getFunction(fun1.getName());
            if (fun2P && fun1.getName() != "__mark") {
                llvm::Function &fun2 = *fun2P;
                // Calculate the number of varargs used in function calls
                set<uint32_t> varArgs = getVarArgs(fun1);
                set<uint32_t> varArgs2 = getVarArgs(fun2);
                for (auto el : varArgs2) {
                    varArgs.insert(el);
                }
                for (auto argNum : varArgs) {
                    std::vector<SortedVar> args;
                    auto funArgs1 = funArgs(fun1, "arg1_", argNum);
                    for (auto arg : funArgs1) {
                        args.push_back(arg);
                    }
                    if (mem & HEAP_MASK) {
                        args.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
                    }
                    auto funArgs2 = funArgs(fun2, "arg2_", argNum);
                    for (auto arg : funArgs2) {
                        args.push_back(arg);
                    }
                    if (mem) {
                        args.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
                    }
                    std::string funName =
                        invariantName(ENTRY_MARK, ProgramSelection::Both,
                                      fun1.getName().str(), argNum);
                    args.push_back(SortedVar("res1", "Int"));
                    args.push_back(SortedVar("res2", "Int"));
                    if (mem & HEAP_MASK) {
                        args.push_back(
                            SortedVar("HEAP$1_res", "(Array Int Int)"));
                        args.push_back(
                            SortedVar("HEAP$2_res", "(Array Int Int)"));
                    }
                    SMTRef body = makeBinOp("=", "res1", "res2");
                    if (mem & HEAP_MASK) {
                        std::vector<SortedVar> forallArgs = {
                            SortedVar("i", "Int")};
                        SMTRef heapOutEqual = make_shared<Forall>(
                            forallArgs,
                            makeBinOp("=",
                                      makeBinOp("select", "HEAP$1_res", "i"),
                                      makeBinOp("select", "HEAP$2_res", "i")));
                        body = makeBinOp("and", body, heapOutEqual);
                    }
                    std::vector<SMTRef> equalOut;
                    auto range = funCondMap.equal_range(fun1.getName());
                    for (auto i = range.first; i != range.second; ++i) {
                        equalOut.push_back(name(i->second));
                    }
                    if (!equalOut.empty()) {
                        equalOut.push_back(body);
                        body = make_shared<Op>("and", equalOut);
                    }
                    std::vector<SMTRef> equal;
                    for (auto it1 = funArgs1.begin(), it2 = funArgs2.begin();
                         it1 != funArgs1.end() && it2 != funArgs2.end();
                         ++it1) {
                        equal.push_back(makeBinOp("=", it1->name, it2->name));
                        ++it2;
                    }
                    if (mem & HEAP_MASK) {
                        std::vector<SortedVar> forallArgs = {
                            SortedVar("i", "Int")};
                        SMTRef heapInEqual = make_shared<Forall>(
                            forallArgs,
                            makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                      makeBinOp("select", "HEAP$2", "i")));
                        equal.push_back(heapInEqual);
                    }
                    body = makeBinOp("=>", make_shared<Op>("and", equal), body);
                    SMTRef mainInv =
                        make_shared<FunDef>(funName, args, "Bool", body);
                    declarations.push_back(mainInv);
                }
            }
        }
    }
    for (auto &fun1 : mod1) {
        if (fun1.isDeclaration() && !fun1.isIntrinsic() &&
            fun1.getName() != "__mark") {
            auto decls = externFunDecl(fun1, 1, mem);
            declarations.insert(declarations.end(), decls.begin(), decls.end());
        }
    }
    for (auto &fun2 : mod2) {
        if (fun2.isDeclaration() && !fun2.isIntrinsic() &&
            fun2.getName() != "__mark") {
            auto decls = externFunDecl(fun2, 2, mem);
            declarations.insert(declarations.end(), decls.begin(), decls.end());
        }
    }
}

std::set<uint32_t> getVarArgs(llvm::Function &fun) {
    std::set<uint32_t> varArgs;
    for (auto User : fun.users()) {
        if (const auto callInst = llvm::dyn_cast<llvm::CallInst>(User)) {
            varArgs.insert(callInst->getNumArgOperands() -
                           fun.getFunctionType()->getNumParams());
        } else {
            logWarningData("Unsupported use of function\n", *User);
        }
    }
    return varArgs;
}

std::vector<SortedVar> funArgs(llvm::Function &fun, std::string prefix,
                               uint32_t varArgs) {
    std::vector<SortedVar> args;
    int argIndex = 0;
    for (auto &arg : fun.getArgumentList()) {
        if (arg.getName().empty()) {
            arg.setName(prefix + std::to_string(argIndex++));
        }
        args.push_back(SortedVar(arg.getName(), "Int"));
    }
    for (uint32_t i = 0; i < varArgs; ++i) {
        args.push_back(SortedVar("var" + prefix + std::to_string(i), "Int"));
    }
    return args;
}

std::vector<SMTRef> externFunDecl(llvm::Function &fun, int program,
                                  Memory mem) {
    std::vector<SMTRef> decls;
    set<uint32_t> varArgs = getVarArgs(fun);
    for (auto argNum : varArgs) {
        std::vector<SortedVar> args = funArgs(fun, "arg_", argNum);
        if (mem) {
            args.push_back(SortedVar("HEAP", "(Array Int Int)"));
        }
        args.push_back(SortedVar("res", "Int"));
        args.push_back(SortedVar("HEAP_res", "(Array Int Int)"));
        std::string funName =
            invariantName(ENTRY_MARK, program == 1 ? ProgramSelection::First
                                                   : ProgramSelection::Second,
                          fun.getName().str(), argNum);
        SMTRef body = name("true");
        decls.push_back(make_shared<FunDef>(funName, args, "Bool", body));
    }
    return decls;
}

// this does not actually check if the function recurses but the next version of
// llvm provides a function for that and I’m too lazy to implement it myself
bool doesNotRecurse(llvm::Function &fun) {
    for (auto &bb : fun) {
        for (auto &inst : bb) {
            if (const auto callInst = llvm::dyn_cast<llvm::CallInst>(&inst)) {
                const auto calledFun = callInst->getCalledFunction();
                if (calledFun && !calledFun->isDeclaration()) {
                    return false;
                }
            }
        }
    }
    return true;
}

bool doesAccessMemory(const llvm::Module &mod) {
    for (auto &fun : mod) {
        for (auto &bb : fun) {
            for (auto &instr : bb) {
                if (llvm::isa<llvm::LoadInst>(&instr) ||
                    llvm::isa<llvm::StoreInst>(&instr)) {
                    return true;
                }
            }
        }
    }
    return false;
}

vector<SMTRef> globalDeclarationsForMod(int globalPointer, llvm::Module &mod,
                                        llvm::Module &modOther, int program) {
    std::vector<SMTRef> declarations;
    for (auto &global1 : mod.globals()) {
        std::string globalName = global1.getName();
        if (!modOther.getNamedGlobal(globalName)) {
            // we want the size of string constants not the size of the pointer
            // pointing to them
            if (const auto pointerTy =
                    llvm::dyn_cast<llvm::PointerType>(global1.getType())) {
                globalPointer += typeSize(pointerTy->getElementType());
            } else {
                globalPointer += typeSize(global1.getType());
            }
            std::vector<SortedVar> empty;
            auto constDef1 = make_shared<FunDef>(
                globalName + "$" + std::to_string(program), empty, "Int",
                makeUnaryOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
        }
    }
    return declarations;
}
std::vector<SMTRef> globalDeclarations(llvm::Module &mod1, llvm::Module &mod2) {
    // First match globals with the same name to make sure that they get the
    // same pointer, then match globals that only exist in one module
    std::vector<SMTRef> declarations;
    int globalPointer = 1;
    for (auto &global1 : mod1.globals()) {
        std::string globalName = global1.getName();
        if (mod2.getNamedGlobal(globalName)) {
            // we want the size of string constants not the size of the pointer
            // pointing to them
            if (const auto pointerTy =
                    llvm::dyn_cast<llvm::PointerType>(global1.getType())) {
                globalPointer += typeSize(pointerTy->getElementType());
            } else {
                globalPointer += typeSize(global1.getType());
            }
            std::vector<SortedVar> empty;
            auto constDef1 = make_shared<FunDef>(
                globalName + "$1", empty, "Int",
                makeUnaryOp("-", std::to_string(globalPointer)));
            auto constDef2 = make_shared<FunDef>(
                globalName + "$2", empty, "Int",
                makeUnaryOp("-", std::to_string(globalPointer)));
            declarations.push_back(constDef1);
            declarations.push_back(constDef2);
        }
    }
    auto decls1 = globalDeclarationsForMod(globalPointer, mod1, mod2, 1);
    auto decls2 = globalDeclarationsForMod(globalPointer, mod2, mod1, 2);
    declarations.insert(declarations.end(), decls1.begin(), decls1.end());
    declarations.insert(declarations.end(), decls2.begin(), decls2.end());
    for (auto &global1 : mod1.globals()) {
        global1.setName(global1.getName() + "$1");
    }
    for (auto &global2 : mod2.globals()) {
        global2.setName(global2.getName() + "$2");
    }
    return declarations;
}

std::multimap<string, string> collectFunConds() {
    std::multimap<string, string> map;
    std::ifstream fileStream1(fileName1);
    std::string fileString1((std::istreambuf_iterator<char>(fileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream fileStream2(fileName2);
    std::string fileString2((std::istreambuf_iterator<char>(fileStream2)),
                            std::istreambuf_iterator<char>());
    auto map1 = collectFunCondsInFile(fileString1);
    auto map2 = collectFunCondsInFile(fileString2);
    std::merge(map1.begin(), map1.end(), map2.begin(), map2.end(),
               std::inserter(map, std::end(map)));
    return map;
}

std::multimap<string, string> collectFunCondsInFile(std::string file) {
    std::multimap<string, string> map;
    std::regex condRegex(
        "/\\*@\\s*addfuncond\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    for (std::sregex_iterator
             i = std::sregex_iterator(file.begin(), file.end(), condRegex),
             e = std::sregex_iterator();
         i != e; ++i) {
        std::smatch match = *i;
        std::string matchStr = match[2];
        map.insert(make_pair(match[1], "(" + matchStr + ")"));
    }
    return map;
}
