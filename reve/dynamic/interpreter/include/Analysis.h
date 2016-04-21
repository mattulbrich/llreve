#pragma once

#include "FunctionSMTGeneration.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "Pattern.h"
#include "Permutation.h"
#include "Preprocess.h"

#include "llvm/IR/Module.h"

using BlockNameMap = std::map<std::string, int>;
using PatternCandidates =
    std::list<std::vector<std::shared_ptr<pattern::InstantiatedValue>>>;
using PatternCandidatesMap = std::map<int, PatternCandidates>;

void analyse(MonoPair<std::shared_ptr<llvm::Module>> modules,
             std::string outputDirectory,
             std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
             std::string mainFunctionName);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;
using EquationsMap = std::map<int, std::vector<std::vector<mpq_class>>>;

void findEqualities(MonoPair<Call<std::string>> calls,
                    MonoPair<BlockNameMap> nameMap, FreeVarsMap freeVars,
                    PatternCandidatesMap &candidates);
void basicPatternCandidates(MonoPair<Call<std::string>> calls,
                            MonoPair<BlockNameMap> nameMap,
                            FreeVarsMap freeVarsMap,
                            PatternCandidatesMap &candidates);
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
                      MonoPair<BlockNameMap> nameMap,
                      std::function<void(MatchInfo)> fun);
bool normalMarkBlock(const BlockNameMap &map, BlockName &blockName);
void debugAnalysis(MatchInfo match);
void removeEqualities(std::map<int, std::set<Equality>> &equalities,
                      MatchInfo match);

void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat);

FreeVarsMap removeEqualities(FreeVarsMap freeVars,
                             const PatternCandidatesMap &candidates);

void instantiatePattern(PatternCandidatesMap &patternCandidates,
                        const FreeVarsMap &freeVars, const pattern::Expr &pat,
                        MatchInfo match);
void populateEquationsMap(EquationsMap &equationsMap, FreeVarsMap freeVarsMap,
                          MatchInfo match);
void dumpEquationsMap(const EquationsMap &equationsMap,
                      const FreeVarsMap &freeVarsmap);
