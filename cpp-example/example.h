auto main(int argc, const char **argv9) -> int;
auto getFunction(llvm::Module &mod) -> llvm::ErrorOr<llvm::Function &>;
template <int N>
auto initializeArgs(const char **argv, int argc)
    -> llvm::SmallVector<const char *, N>;
auto initializeDiagnostics(void) -> std::unique_ptr<clang::DiagnosticsEngine>;
auto initializeDriver(clang::DiagnosticsEngine &Diags)
    -> std::unique_ptr<clang::driver::Driver>;
auto doAnalysis(llvm::Function &Fun) -> void;
auto getCmd(clang::driver::Compilation &Comp, clang::DiagnosticsEngine &Diags)
    -> llvm::ErrorOr<const clang::driver::Command &>;
