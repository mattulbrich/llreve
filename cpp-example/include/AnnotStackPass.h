#ifndef ANNOT_STACK_PASS_H
#define ANNOT_STACK_PASS_H

class AnnotStackPass {
  public:
    auto run(llvm::Function &F, llvm::FunctionAnalysisManager *AM)
        -> llvm::PreservedAnalyses;
    static auto name() -> llvm::StringRef { return "AnnotStackPass"; }
};

auto markStackInstruction(llvm::Instruction &Inst, std::string MetadataName)
    -> void;

#endif // ANNOT_STACK_PASS_H
