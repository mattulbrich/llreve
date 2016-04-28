#pragma once

#include "MarkAnalysis.h"
#include "PathAnalysis.h"

struct AnalysisResults {
    BidirBlockMarkMap blockMarkMap;
    PathMap paths;
    AnalysisResults(BidirBlockMarkMap marks, PathMap pm)
        : blockMarkMap(marks), paths(pm) {}
};
