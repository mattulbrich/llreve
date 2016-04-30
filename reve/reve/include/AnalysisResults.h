#pragma once

#include "MarkAnalysis.h"
#include "PathAnalysis.h"

#include "llvm/Analysis/LoopInfo.h"

struct AnalysisResults {
    BidirBlockMarkMap blockMarkMap;
    PathMap paths;
    // Loop info is not clonable so we have to keep the pass around to make sure
    // the reference doesn’t die
    llvm::LoopInfoWrapperPass *loopInfo;
    AnalysisResults(BidirBlockMarkMap marks, PathMap pm,
                    llvm::LoopInfoWrapperPass *loopInfo)
        : blockMarkMap(marks), paths(pm), loopInfo(loopInfo) {}
};
