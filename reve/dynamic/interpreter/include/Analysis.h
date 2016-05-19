#pragma once

#include "Compat.h"
#include "FunctionSMTGeneration.h"
#include "HeapPattern.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
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

using ExitIndex = mpz_class;

using BlockNameMap = std::map<std::string, std::set<int>>;
using HeapPatternCandidates =
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>;
using HeapPatternCandidatesMap = std::map<
    int,
    std::map<ExitIndex, LoopInfoData<llvm::Optional<HeapPatternCandidates>>>>;
using BoundsMap =
    std::map<int, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::vector<smt::SharedSMTRef>
driver(MonoPair<std::shared_ptr<llvm::Module>> modules,
       std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
       std::string mainFunctionName,
       std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns);
llvm::Optional<MonoPair<PreprocessedFunction>>
findFunction(const std::vector<MonoPair<PreprocessedFunction>> functions,
             std::string functionName);

using Equality = MonoPair<std::string>;
using PolynomialEquations =
    std::map<int, std::map<ExitIndex,
                           LoopInfoData<std::vector<std::vector<mpq_class>>>>>;
using PolynomialSolutions =
    std::map<int, std::map<ExitIndex,
                           LoopInfoData<std::vector<std::vector<mpz_class>>>>>;

using LoopCountMap = std::map<int, std::vector<MonoPair<int>>>;

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

template <typename T> struct MatchInfo {
    MonoPair<const BlockStep<T> *> steps;
    LoopInfo loopInfo;
    int mark;
    MatchInfo(MonoPair<const BlockStep<T> *> steps, LoopInfo loopInfo, int mark)
        : steps(steps), loopInfo(loopInfo), mark(mark) {}
};

// Walks through the two calls and calls the function for every pair of matching
// marks
bool normalMarkBlock(const BlockNameMap &map, BlockName &blockName);
void debugAnalysis(MatchInfo<std::string> match);
void dumpLoopCounts(const LoopCountMap &loopCounts);
std::map<int, LoopTransformation> findLoopTransformations(LoopCountMap &map);
template <typename T>
void findLoopCounts(int &lastMark, LoopCountMap &map, MatchInfo<T> match) {
    if (lastMark == match.mark) {
        switch (match.loopInfo) {
        case LoopInfo::Left:
            map[match.mark].back().first++;
            break;
        case LoopInfo::Right:
            map[match.mark].back().second++;
            break;
        case LoopInfo::None:
            map[match.mark].back().first++;
            map[match.mark].back().second++;
            break;
        }
    } else {
        switch (match.loopInfo) {
        case LoopInfo::None:
            map[match.mark].push_back(makeMonoPair(0, 0));
            break;
        default:
            assert(false);
            break;
        }
        lastMark = match.mark;
    }
}
void instantiateBounds(
    std::map<int, std::map<std::string, Bound<VarIntVal>>> &boundsMap,
    const FreeVarsMap &freeVars, MatchInfo<std::string> match);
BoundsMap updateBounds(
    BoundsMap accumulator,
    const std::map<int, std::map<std::string, Bound<VarIntVal>>> &update);
void populateEquationsMap(PolynomialEquations &equationsMap,
                          FreeVarsMap freeVarsMap,
                          MatchInfo<const llvm::Value *> match, size_t degree);
void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match);
void dumpPolynomials(const PolynomialEquations &equationsMap,
                     const FreeVarsMap &freeVarsmap);
void dumpHeapPatterns(const HeapPatternCandidatesMap &heapPatternsMap);
std::map<int, smt::SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const FreeVarsMap &freeVarsMap, size_t degree);
smt::SharedSMTRef
makeInvariantDefinition(const std::vector<std::vector<mpz_class>> &solution,
                        const std::vector<std::string> &freeVars,
                        size_t degree);
smt::SharedSMTRef makeEquation(const std::vector<mpz_class> &eq,
                               const std::vector<std::string> &freeVars,
                               size_t degree);
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
void iterateTracesInRange(
    MonoPair<llvm::Function *> funs, VarIntVal lowerBound, VarIntVal upperBound,
    std::function<void(MonoPair<Call<const llvm::Value *>>)> callback);
void dumpLoopTransformations(
    std::map<int, LoopTransformation> loopTransformations);
void applyLoopTransformation(
    MonoPair<PreprocessedFunction> &functions,
    const std::map<int, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &mark);
std::vector<std::vector<std::string>>
polynomialTermsOfDegree(std::vector<std::string> variables, size_t degree);

template <typename T>
void analyzeExecution(const MonoPair<Call<T>> &calls,
                      MonoPair<BlockNameMap> nameMaps,
                      std::function<void(MatchInfo<T>)> fun) {
    const std::vector<std::shared_ptr<BlockStep<T>>> &steps1 =
        calls.first.steps;
    const std::vector<std::shared_ptr<BlockStep<T>>> &steps2 =
        calls.second.steps;
    auto stepsIt1 = steps1.begin();
    auto stepsIt2 = steps2.begin();
    auto prevStepIt1 = *stepsIt1;
    auto prevStepIt2 = *stepsIt2;
    while (stepsIt1 != steps1.end() && stepsIt2 != steps2.end()) {
        // Advance until a mark is reached
        while (stepsIt1 != steps1.end() &&
               !normalMarkBlock(nameMaps.first, (*stepsIt1)->blockName)) {
            stepsIt1++;
        }
        while (stepsIt2 != steps2.end() &&
               !normalMarkBlock(nameMaps.second, (*stepsIt2)->blockName)) {
            stepsIt2++;
        }
        if (stepsIt1 == steps1.end() && stepsIt2 == steps2.end()) {
            break;
        }
        // Check marks
        if (!intersection(nameMaps.first.at((*stepsIt1)->blockName),
                          nameMaps.second.at((*stepsIt2)->blockName))
                 .empty()) {
            assert(intersection(nameMaps.first.at((*stepsIt1)->blockName),
                                nameMaps.second.at((*stepsIt2)->blockName))
                       .size() == 1);
            // We resolve the ambiguity in the marks by hoping that for one
            // program there is only one choice
            int mark = *intersection(nameMaps.first.at((*stepsIt1)->blockName),
                                     nameMaps.second.at((*stepsIt2)->blockName))
                            .begin();
            // Perfect synchronization
            fun(MatchInfo<T>(makeMonoPair(&**stepsIt1, &**stepsIt2),
                             LoopInfo::None, mark));
            prevStepIt1 = *stepsIt1;
            prevStepIt2 = *stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In the first round this is not true, but we should never fall in
            // this case in the first round
            assert(prevStepIt1 != *stepsIt1);
            assert(prevStepIt2 != *stepsIt2);

            // One side has to wait for the other to finish its loop
            LoopInfo loop = LoopInfo::Left;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepIt1;
            auto prevStepItOther = prevStepIt2;
            auto end = steps1.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if ((*stepsIt2)->blockName == prevStepIt2->blockName) {
                loop = LoopInfo::Right;
                stepsIt = stepsIt2;
                prevStepIt = prevStepIt2;
                prevStepItOther = prevStepIt1;
                end = steps2.end();
                nameMap = nameMaps.second;
                otherNameMap = nameMaps.first;
            }
            // Keep looping one program until it moves on
            do {
                assert(intersection(nameMap.at(prevStepIt->blockName),
                                    otherNameMap.at(prevStepItOther->blockName))
                           .size() == 1);
                int mark =
                    *intersection(nameMap.at(prevStepIt->blockName),
                                  otherNameMap.at(prevStepItOther->blockName))
                         .begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    const BlockStep<T> *firstStep = &**stepsIt;
                    const BlockStep<T> *secondStep = &*prevStepItOther;
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                } else {
                    const BlockStep<T> *secondStep = &**stepsIt;
                    const BlockStep<T> *firstStep = &*prevStepItOther;
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                }
                // Go to the next mark
                do {
                    stepsIt++;
                } while (stepsIt != end &&
                         !normalMarkBlock(nameMap, (*stepsIt)->blockName));
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     (*stepsIt)->blockName == prevStepIt->blockName);
            // Getting a reference to the iterator and modifying that doesn't
            // seem to work so we copy it and set it again
            if (loop == LoopInfo::Left) {
                stepsIt1 = stepsIt;
            } else {
                stepsIt2 = stepsIt;
            }
        }
    }
}

void workerThread(
    ThreadSafeQueue<WorkItem> &q, std::vector<std::string> &varNamesFirst,
    std::vector<std::string> &varNamesSecond,
    std::function<void(MonoPair<Call<const llvm::Value *>>)> callback,
    Heap heap, MonoPair<const llvm::Function *> funs);
