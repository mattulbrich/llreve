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

template <typename T> struct Bound {
    T lower;
    T upper;
    Bound(T lower, T upper) : lower(lower), upper(upper) {}
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
using BoundsMap =
    std::map<int, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::map<int, smt::SharedSMTRef>
analyse(std::string outputDirectory,
        std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
        std::string mainFunctionName);
std::vector<smt::SharedSMTRef>
driver(MonoPair<std::shared_ptr<llvm::Module>> modules,
       std::string outputDirectory,
       std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
       std::string mainFunctionName);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;
using ExitIndex = mpz_class;
using PolynomialEquations =
    std::map<int, std::map<ExitIndex,
                           LoopInfoData<std::vector<std::vector<mpq_class>>>>>;
using PolynomialSolutions =
    std::map<int, std::map<ExitIndex,
                           LoopInfoData<std::vector<std::vector<mpz_class>>>>>;

using LoopCountMap = std::map<int, std::vector<MonoPair<int>>>;

void findEqualities(MonoPair<Call<std::string>> calls,
                    MonoPair<BlockNameMap> nameMap, FreeVarsMap freeVars,
                    PatternCandidatesMap &candidates);
void basicPatternCandidates(MonoPair<Call<std::string>> calls,
                            MonoPair<BlockNameMap> nameMap,
                            FreeVarsMap freeVarsMap,
                            PatternCandidatesMap &candidates);
template <typename T> T identity(T x) { return x; }
BlockNameMap blockNameMap(BidirBlockMarkMap blockMap);

enum class LoopTransformType { Unroll, Peel };
enum class LoopTransformSide { Left, Right };

struct LoopTransformation {
    LoopTransformType type;
    LoopTransformSide side;
    size_t count;
    LoopTransformation(LoopTransformType type, LoopTransformSide side,
                       size_t count)
        : type(type), side(side), count(count) {}
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
void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat);
void dumpLoopCounts(const LoopCountMap &loopCounts);
std::map<int, LoopTransformation> findLoopTransformations(LoopCountMap &map);
void instantiatePattern(PatternCandidatesMap &patternCandidates,
                        const FreeVarsMap &freeVars, const pattern::Expr &pat,
                        MatchInfo match);
void findLoopCounts(int &lastMark, LoopCountMap &map, MatchInfo match);
void instantiateBounds(
    std::map<int, std::map<std::string, Bound<VarIntVal>>> &boundsMap,
    const FreeVarsMap &freeVars, MatchInfo match);
BoundsMap updateBounds(
    BoundsMap accumulator,
    const std::map<int, std::map<std::string, Bound<VarIntVal>>> &update);
void populateEquationsMap(PolynomialEquations &equationsMap,
                          FreeVarsMap freeVarsMap, MatchInfo match);
void dumpPolynomials(const PolynomialEquations &equationsMap,
                      const FreeVarsMap &freeVarsmap);
std::map<int, smt::SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const BoundsMap &bounds,
                         const FreeVarsMap &freeVarsMap);
smt::SharedSMTRef
makeInvariantDefinition(const std::vector<std::vector<mpz_class>> &solution,
                        const std::vector<std::string> &freeVars);
smt::SharedSMTRef makeEquation(const std::vector<mpz_class> &eq,
                               const std::vector<std::string> &freeVars);
smt::SharedSMTRef makeBoundsDefinitions(
    const std::map<std::string, Bound<llvm::Optional<VarIntVal>>> &bounds);
PolynomialSolutions findSolutions(const PolynomialEquations &equationsMap);
void dumpBounds(const BoundsMap &bounds);

std::map<int,
         std::map<ExitIndex, LoopInfoData<std::set<MonoPair<std::string>>>>>
extractEqualities(const PolynomialEquations &equations,
                  const std::vector<std::string> &freeVars);
void iterateDeserialized(
    std::string directory,
    std::function<void(MonoPair<Call<std::string>> &)> callback);
void dumpLoopTransformations(
    std::map<int, LoopTransformation> loopTransformations);
void applyLoopTransformation(
    MonoPair<PreprocessedFunction> &functions,
    const std::map<int, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &mark);
