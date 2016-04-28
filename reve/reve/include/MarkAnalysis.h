#pragma once

#include <map>
#include <set>

#include "llvm/IR/LegacyPassManager.h"

const int UNREACHABLE_MARK = -3;
const int EXIT_MARK = -2;
const int ENTRY_MARK = -1;

struct BidirBlockMarkMap {
    std::map<llvm::BasicBlock *, std::set<int>> BlockToMarksMap;
    std::map<int, std::set<llvm::BasicBlock *>> MarkToBlocksMap;
    BidirBlockMarkMap() : BlockToMarksMap({}), MarkToBlocksMap({}) {}
    BidirBlockMarkMap(
        std::map<llvm::BasicBlock *, std::set<int>> BlockToMarksMap,
        std::map<int, std::set<llvm::BasicBlock *>> MarkToBlocksMap)
        : BlockToMarksMap(BlockToMarksMap), MarkToBlocksMap(MarkToBlocksMap) {}
};
class MarkAnalysis : public llvm::FunctionPass {
  public:
    using Result = BidirBlockMarkMap;
    static llvm::StringRef name() { return "MarkAnalysis"; }
    bool runOnFunction(llvm::Function &Fun) override;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    BidirBlockMarkMap getBlockMarkMap() const;
    MarkAnalysis() : llvm::FunctionPass(ID) {}
    static char ID;
    // it’s not possible to have non default constructors with the legacy
    // passmanager so we can’t just pass a pointer there to escape this
    BidirBlockMarkMap BlockMarkMap;
};
