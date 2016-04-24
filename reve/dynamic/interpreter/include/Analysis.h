#pragma once

#include "FunctionSMTGeneration.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "Pattern.h"
#include "Permutation.h"
#include "Preprocess.h"

#include "llvm/IR/Module.h"

enum class LoopInfo {
    Left,  // The left call is looping alone
    Right, // The right call is looping alone
    None   // perfect synchronization
};

template <typename T> struct LoopInfoData {
    T left;
    T right;
    T none;
    LoopInfoData(T left, T right, T none)
        : left(left), right(right), none(none) {}
};

using BlockNameMap = std::map<std::string, std::set<int>>;
using PatternCandidates =
    std::list<std::vector<std::shared_ptr<pattern::InstantiatedValue>>>;
using PatternCandidatesMap =
    std::map<int, LoopInfoData<llvm::Optional<PatternCandidates>>>;

std::map<int, smt::SharedSMTRef>
analyse(std::string outputDirectory,
        std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
        std::string mainFunctionName);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;
using EquationsMap =
    std::map<int, LoopInfoData<std::vector<std::vector<mpq_class>>>>;
using EquationsSolutionsMap =
    std::map<int, LoopInfoData<std::vector<std::vector<mpz_class>>>>;

void findEqualities(MonoPair<Call<std::string>> calls,
                    MonoPair<BlockNameMap> nameMap, FreeVarsMap freeVars,
                    PatternCandidatesMap &candidates);
void basicPatternCandidates(MonoPair<Call<std::string>> calls,
                            MonoPair<BlockNameMap> nameMap,
                            FreeVarsMap freeVarsMap,
                            PatternCandidatesMap &candidates);
template <typename T> T identity(T x) { return x; }
BlockNameMap blockNameMap(BidirBlockMarkMap blockMap);

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
void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat);
void instantiatePattern(PatternCandidatesMap &patternCandidates,
                        const FreeVarsMap &freeVars, const pattern::Expr &pat,
                        MatchInfo match);
void populateEquationsMap(EquationsMap &equationsMap, FreeVarsMap freeVarsMap,
                          MatchInfo match);
void dumpEquationsMap(const EquationsMap &equationsMap,
                      const FreeVarsMap &freeVarsmap);
std::map<int, smt::SharedSMTRef>
makeInvariantDefinitions(const EquationsSolutionsMap &solutions,
                         const FreeVarsMap &freeVarsMap);
smt::SharedSMTRef
makeInvariantDefinition(const std::vector<std::vector<mpz_class>> &solution,
                        const std::vector<std::string> &freeVars);
smt::SharedSMTRef makeEquation(const std::vector<mpz_class> &eq,
                               const std::vector<std::string> &freeVars);
EquationsSolutionsMap findSolutions(const EquationsMap &equationsMap);
