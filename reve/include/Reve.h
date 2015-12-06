#ifndef REVE_H
#define REVE_H

#include "PathAnalysis.h"
#include "SMT.h"

#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Driver.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Option/Option.h"

auto main(int Argc, const char **Argv) -> int;
auto zipFunctions(llvm::Module &Mod1, llvm::Module &Mod2) -> llvm::ErrorOr<
    std::vector<std::pair<llvm::Function *, llvm::Function *>>>;
template <int N>
auto initializeArgs(const char *ExeName, std::string Input1, std::string Input2)
    -> llvm::SmallVector<const char *, N>;
auto initializeDiagnostics(void) -> std::unique_ptr<clang::DiagnosticsEngine>;
auto initializeDriver(clang::DiagnosticsEngine &Diags)
    -> std::unique_ptr<clang::driver::Driver>;
auto preprocessModule(llvm::Function &Fun, std::string Prefix)
    -> std::shared_ptr<llvm::FunctionAnalysisManager>;
auto getCmd(clang::driver::Compilation &Comp, clang::DiagnosticsEngine &Diags)
    -> llvm::ErrorOr<
        std::tuple<llvm::opt::ArgStringList, llvm::opt::ArgStringList>>;
template <typename T> auto makeErrorOr(T Arg) -> llvm::ErrorOr<T>;
auto getModule(const char *ExeName, std::string Input1, std::string Input2)
    -> std::tuple<std::unique_ptr<clang::CodeGenAction>,
                  std::unique_ptr<clang::CodeGenAction>>;
auto getCodeGenAction(const llvm::opt::ArgStringList &CCArgs,
                      clang::DiagnosticsEngine &Diags)
    -> std::unique_ptr<clang::CodeGenAction>;
auto parseInOutInvs(std::string FileName1, std::string FileName2)
    -> std::pair<SMTRef, SMTRef>;
auto processLine(std::string Line, SMTRef &In, SMTRef &Out) -> void;
auto externDeclarations(llvm::Module &Mod1, llvm::Module &Mod2,
                        std::vector<SMTRef> &Declarations) -> void;
auto funArgs(llvm::Function &Fun, std::string Prefix) -> std::vector<SortedVar>;
auto externFunDecl(llvm::Function &Fun, int Program, bool Heap) -> SMTRef;
auto doesNotRecurse(llvm::Function &Fun) -> bool;

#endif // REVE_H
