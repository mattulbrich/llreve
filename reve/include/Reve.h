#ifndef REVE_H
#define REVE_H

#include "SMT.h"

#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Driver.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Option/Option.h"

auto main(int Argc, const char **Argv) -> int;
auto getFunction(llvm::Module &Mod) -> llvm::ErrorOr<llvm::Function &>;
template <int N>
auto initializeArgs(const char *ExeName, std::string Input1, std::string Input2)
    -> llvm::SmallVector<const char *, N>;
auto initializeDiagnostics(void) -> std::unique_ptr<clang::DiagnosticsEngine>;
auto initializeDriver(clang::DiagnosticsEngine &Diags)
    -> std::unique_ptr<clang::driver::Driver>;
auto preprocessModule(llvm::Function &Fun, std::string Prefix)
    -> std::unique_ptr<llvm::FunctionAnalysisManager>;
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
auto convertToSMT(llvm::Function &Mod1, llvm::Function &Mod2,
                  std::unique_ptr<llvm::FunctionAnalysisManager> FAM_1,
                  std::unique_ptr<llvm::FunctionAnalysisManager> FAM_2) -> void;
auto walkCFG(const llvm::BasicBlock &BB_1, const llvm::BasicBlock &BB_2,
             llvm::LoopInfo &LoopInfo_1, llvm::LoopInfo &LoopInfo_2,
             const llvm::BasicBlock *PrevBB_1, const llvm::BasicBlock *PrevBB_2)
    -> std::unique_ptr<const SMTExpr>;
auto toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB)
    -> std::tuple<std::string, std::unique_ptr<const SMTExpr>>;
auto getPredName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto getInstrNameOrValue(const llvm::Value *Val) -> std::string;

#endif // REVE_H
