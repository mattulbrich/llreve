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
auto toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB)
    -> std::tuple<std::string, SMTRef>;
auto getPredName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto getInstrNameOrValue(const llvm::Value *Val) -> SMTRef;
auto invariant(int BlockIndex, std::set<std::string> Args) -> SMTRef;
auto getOpName(const llvm::BinaryOperator &Op) -> std::string;
auto swapIndex(int i) -> int;
auto nestLets(SMTRef Clause, std::vector<std::tuple<std::string, SMTRef>> Defs)
    -> SMTRef;
auto instrToDefs(const llvm::BasicBlock *BB, const llvm::BasicBlock *PrevBB,
                 bool IgnorePhis, int Program)
    -> std::vector<std::tuple<std::string, SMTRef>>;
auto pathToSMT(Path Path, SMTRef EndClause, int Program) -> SMTRef;
auto invName(int Index) -> std::string;
auto wrapForall(SMTRef Clause, int BlockIndex, std::set<std::string> FreeVars)
    -> SMTRef;
auto invariantDef(int BlockIndex, std::set<std::string> FreeVars) -> SMTRef;
auto freeVars(std::map<int, Paths> Paths) -> std::set<std::string>;
auto freeVarsMap(PathMap Map_1, PathMap Map_2) -> std::map<int, std::set<std::string>>;
#endif // REVE_H
