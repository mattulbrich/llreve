#include "PathAnalysis.h"

char PathAnalysis::PassID;

bool PathAnalysis::run(llvm::Function &F, llvm::FunctionAnalysisManager *AM) {
    return true;
}
