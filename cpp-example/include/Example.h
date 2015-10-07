#ifndef EXAMPLE_H
#define EXAMPLE_H

auto main(int Argc, const char **Argv) -> int;
auto getFunction(llvm::Module &Mod) -> llvm::ErrorOr<llvm::Function &>;
template <int N>
auto initializeArgs(const char *ExeName, std::string Input)
    -> llvm::SmallVector<const char *, N>;
auto initializeDiagnostics(void) -> std::unique_ptr<clang::DiagnosticsEngine>;
auto initializeDriver(clang::DiagnosticsEngine &Diags)
    -> std::unique_ptr<clang::driver::Driver>;
auto doAnalysis(llvm::Function &Fun) -> void;
auto getCmd(clang::driver::Compilation &Comp, clang::DiagnosticsEngine &Diags)
    -> llvm::ErrorOr<const clang::driver::Command &>;
template <typename T> auto makeErrorOr(T Arg) -> llvm::ErrorOr<T>;
auto getModule(const char *ExeName, std::string Input)
    -> std::unique_ptr<clang::CodeGenAction>;

#endif // EXAMPLE_H
