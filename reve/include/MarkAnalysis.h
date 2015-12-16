#ifndef MARKANALYSIS_H
#define MARKANALYSIS_H

#include "Mem2Reg.h"

#include <set>

const int UNREACHABLE_MARK = -3;
const int EXIT_MARK = -2;
const int ENTRY_MARK = -1;

struct BidirBlockMarkMap {
    std::map<llvm::BasicBlock *, std::set<int>> BlockToMarksMap;
    std::map<int, std::set<llvm::BasicBlock *>> MarkToBlocksMap;
    BidirBlockMarkMap(
        std::map<llvm::BasicBlock *, std::set<int>> BlockToMarksMap,
        std::map<int, std::set<llvm::BasicBlock *>> MarkToBlocksMap)
        : BlockToMarksMap(BlockToMarksMap), MarkToBlocksMap(MarkToBlocksMap) {}
};
class MarkAnalysis {
  public:
    using Result = BidirBlockMarkMap;
    static llvm::StringRef name() { return "MarkAnalysis"; }
    static void *ID() { return static_cast<void *>(&PassID); }
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);

  private:
    static char PassID;
};

#endif // MARKANALYSIS_H
