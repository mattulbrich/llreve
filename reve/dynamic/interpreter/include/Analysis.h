#pragma once

#include "FunctionSMTGeneration.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "Pattern.h"
#include "Preprocess.h"
#include "Permutation.h"

#include "llvm/IR/Module.h"

using BlockNameMap = std::map<std::string, int>;
using PatternCandidates = std::list<std::vector<std::string>>;
using PatternCandidatesMap = std::map<int, PatternCandidates>;

void analyse(MonoPair<std::shared_ptr<llvm::Module>> modules,
             std::string outputDirectory,
             std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
             std::string mainFunctionName);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;

PatternCandidatesMap findEqualities(MonoPair<Call<std::string>> calls,
                                    MonoPair<BlockNameMap> nameMap,
                                    FreeVarsMap freeVars);
void basicPatternCandidates(MonoPair<Call<std::string>> calls,
                            MonoPair<BlockNameMap> nameMap,
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
void removeNonMatchingPatterns(PatternCandidatesMap &patternCandidates,
                               const pattern::Expr &pat,
                               MatchInfo match);

template <typename N, typename V>
PatternCandidatesMap instantiatePattern(std::map<int, std::vector<N>> variables,
                                        const pattern::Expr &pat) {
    std::map<int, std::list<std::vector<N>>> output;
    for (auto mapIt : variables) {
        if (pat.arguments() <= mapIt.second.size()) {
            output.insert(std::make_pair(
                mapIt.first,
                kPermutations(mapIt.second, pat.arguments())));
        } else {
            std::list<std::vector<N>> l;
            output.insert(std::make_pair(mapIt.first, l));
        }
    }
    return output;
}

void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat);

FreeVarsMap removeEqualities(FreeVarsMap freeVars,
                             const PatternCandidatesMap &candidates);
