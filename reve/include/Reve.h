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
auto walkCFG(const llvm::BasicBlock *CurrentBB, const llvm::BasicBlock *OtherBB,
             llvm::LoopInfo *LoopInfo_1, llvm::LoopInfo *LoopInfo_2,
             const llvm::BasicBlock *PrevCurrentBB,
             const llvm::BasicBlock *PrevOtherBB, int Program,
             std::vector<size_t> &Funs, std::vector<std::string> CurrentFunArgs,
             std::vector<std::string> OtherFunArgs) -> SMTRef;
auto stepCFG(const llvm::BasicBlock *CurrentBB, const llvm::BasicBlock *OtherBB,
             llvm::LoopInfo *LoopInfo_1, llvm::LoopInfo *LoopInfo_2,
             const llvm::BasicBlock *PrevCurrentBB,
             const llvm::BasicBlock *PrevOtherBB, int Program,
             std::vector<size_t> &Funs, std::vector<std::string> CurrentFunArgs,
             std::vector<std::string> OtherFunArgs) -> SMTRef;
auto calcInvArgs(std::vector<const llvm::PHINode *> PhiNodes,
                 std::vector<std::string> &PreCondArgs,
                 std::vector<std::string> &InitialArgs,
                 std::vector<std::string> &PostCondArgs, const llvm::Loop *Loop)
    -> void;
auto stepLoopBlock(
    const llvm::BasicBlock *CurrentBB, llvm::LoopInfo *LoopInfo,
    const llvm::BasicBlock *PrevCurrentBB,
    std::vector<std::string> CurrentFunArgs,
    std::function<SMTRef()> InvariantCont,
    std::function<SMTRef(const llvm::BasicBlock *BB, llvm::LoopInfo *LoopInfo,
                         const llvm::BasicBlock *PrevBB)> ExitCont) -> SMTRef;
auto toDef(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB)
    -> std::tuple<std::string, SMTRef>;
auto getPredName(const llvm::CmpInst::Predicate Pred) -> std::string;
auto getInstrNameOrValue(const llvm::Value *Val) -> std::string;
auto extractPhiNodes(const llvm::Loop &Loop)
    -> std::vector<const llvm::PHINode *>;
auto getOpName(const llvm::BinaryOperator &Op) -> std::string;
auto swapIndex(int i) -> int;
auto nestLets(SMTRef Clause, std::vector<std::tuple<std::string, SMTRef>> Defs)
    -> SMTRef;
auto instrToDefs(const llvm::BasicBlock *BB, const llvm::BasicBlock *PrevBB, bool Loop)
    -> std::vector<std::tuple<std::string, SMTRef>>;

#endif // REVE_H
