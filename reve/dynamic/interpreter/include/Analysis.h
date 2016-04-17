#pragma once

#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "Preprocess.h"
#include "These.h"
#include "Pattern.h"

#include "llvm/IR/Module.h"

using BlockNameMap = std::map<std::string, int>;

void analyse(MonoPair<std::shared_ptr<llvm::Module>> modules,
             std::string outputDirectory,
             std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
             std::string mainFunctionName);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;

std::map<int, std::set<Equality>>
findEqualities(MonoPair<Call<std::string>> calls,
               MonoPair<PreprocessedFunction> functions);
template <typename T> T identity(T x) { return x; }
BlockNameMap blockNameMap(BidirBlockMarkMap blockMap);
enum class LoopInfo {
    Left,  // The left call is looping alone
    Right, // The right call is looping alone
    None   // perfect synchronization
};

struct MatchInfo {
    MonoPair<BlockStep<std::string>> steps;
    LoopInfo loopInfo;
    int mark;
    MatchInfo(MonoPair<const BlockStep<std::string> &> steps, LoopInfo loopInfo,
              int mark)
        : steps(steps), loopInfo(loopInfo), mark(mark) {}
};

// Walks through the two calls and calls the function for every pair of matching
// marks
void analyzeExecution(MonoPair<Call<std::string>> calls,
                      BidirBlockMarkMap markMap, MonoPair<BlockNameMap> nameMap,
                      std::function<void(MatchInfo)> fun);
bool normalMarkBlock(const BlockNameMap &map, BlockName &blockName);
void debugAnalysis(MatchInfo match);
void removeEqualities(std::map<int, std::set<Equality>> &equalities,
                      MatchInfo match);
