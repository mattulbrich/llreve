/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "Compat.h"
#include "FunctionSMTGeneration.h"
#include "HeapPattern.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "Model.h"
#include "MonoPair.h"
#include "Opts.h"
#include "ParseInput.h"
#include "Permutation.h"
#include "Preprocess.h"

#include "llreve/dynamic/Invariant.h"

#include "llvm/IR/Module.h"

#include <thread>

namespace llreve {
namespace dynamic {

extern std::string InputFileFlag;

enum class LoopInfo {
    Left,  // The left call is looping alone
    Right, // The right call is looping alone
    None   // perfect synchronization
};

enum class LlreveResult { Equivalent, NotEquivalent };

template <typename T1, typename T2>
void zipWith(LoopInfoData<T1> &loop1, LoopInfoData<T2> &loop2,
             std::function<void(T1 &, T2 &)> f) {
    f(loop1.left, loop2.left);
    f(loop1.right, loop2.right);
    f(loop1.none, loop2.none);
}

using BlockNameMap = std::map<std::string, std::set<Mark>>;

std::vector<smt::SharedSMTRef> cegarDriver(
    MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    llreve::opts::FileOptions fileopts);
llvm::Optional<MonoPair<llvm::Function *>>
findFunction(std::vector<MonoPair<llvm::Function *>> functions,
             std::string functionName);
Heap randomHeap(const llvm::Function &fun, const FastVarMap &variableValues,
                int lengthBound, int valLowerBound, int valUpperBound,
                unsigned int *seedp);

using Equality = MonoPair<std::string>;

using LoopCountMap = std::map<Mark, std::vector<MonoPair<int>>>;

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
    Mark mark;
    MatchInfo(MonoPair<const BlockStep<T> *> steps, LoopInfo loopInfo,
              Mark mark)
        : steps(steps), loopInfo(loopInfo), mark(mark) {}
};

bool normalMarkBlock(const BlockNameMap &map, const BlockName &blockName);
void debugAnalysis(MatchInfo<const llvm::Value *> match);
void dumpLoopCounts(const LoopCountMap &loopCounts);
std::map<Mark, LoopTransformation> findLoopTransformations(LoopCountMap &map);
struct LoopCountsAndMark {
    Mark mark;
    LoopCountMap loopCounts;
    // -5 is never used as a mark so its a good default
    LoopCountsAndMark() : mark(-5) {}
};

template <typename T>
void findLoopCounts(LoopCountsAndMark &loopCountsAndMark, MatchInfo<T> match) {
    if (loopCountsAndMark.mark == match.mark) {
        switch (match.loopInfo) {
        case LoopInfo::Left:
            loopCountsAndMark.loopCounts[match.mark].back().first++;
            break;
        case LoopInfo::Right:
            loopCountsAndMark.loopCounts[match.mark].back().second++;
            break;
        case LoopInfo::None:
            loopCountsAndMark.loopCounts[match.mark].back().first++;
            loopCountsAndMark.loopCounts[match.mark].back().second++;
            break;
        }
    } else {
        switch (match.loopInfo) {
        case LoopInfo::None:
            loopCountsAndMark.loopCounts[match.mark].push_back(
                makeMonoPair(0, 0));
            break;
        default:
            assert(false);
            break;
        }
        loopCountsAndMark.mark = match.mark;
    }
}
void instantiateBounds(
    std::map<Mark, std::map<std::string, Bound<VarIntVal>>> &boundsMap,
    const FreeVarsMap &freeVars, MatchInfo<std::string> match);
BoundsMap updateBounds(
    BoundsMap accumulator,
    const std::map<Mark, std::map<std::string, Bound<VarIntVal>>> &update);
void populateEquationsMap(
    IterativeInvariantMap<PolynomialEquations> &equationsMap,
    FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match,
    ExitIndex exitIndex, size_t degree);
void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match,
    ExitIndex exitIndex);
void dumpPolynomials(
    const IterativeInvariantMap<PolynomialEquations> &equationsMap,
    const FreeVarsMap &freeVarsmap);
void dumpHeapPatterns(const HeapPatternCandidatesMap &heapPatternsMap);
void dumpBounds(const BoundsMap &bounds);

FastVarMap getVarMap(const llvm::Function *fun, std::vector<mpz_class> vals);

std::map<std::string, const llvm::Value *>
instructionNameMap(const llvm::Function *fun);
std::map<std::string, const llvm::Value *>
instructionNameMap(MonoPair<const llvm::Function *> funs);

MonoPair<FastVarMap> getVarMapFromModel(
    std::map<std::string, const llvm::Value *> instructionNameMap,
    std::vector<smt::SortedVar> freeVars,
    std::map<std::string, mpz_class> vals);
Heap getHeapFromModel(const ArrayVal &ar);
MonoPair<Heap> getHeapsFromModel(std::map<std::string, ArrayVal> arrays);
MonoPair<Integer> getHeapBackgrounds(std::map<std::string, ArrayVal> arrays);

template <typename T>
void workerThread(
    ThreadSafeQueue<WorkItem> &q, T &state,
    std::function<void(MonoPair<Call<const llvm::Value *>>, T &)> callback,
    MonoPair<const llvm::Function *> funs) {
    // std::cerr << "State adddress: " << &state << "\n";
    // Each thread has it’s own seed
    unsigned int seedp = static_cast<unsigned int>(time(NULL));
    for (WorkItem item = q.pop(); item.counter >= 0; item = q.pop()) {
        MonoPair<FastVarMap> variableValues = makeMonoPair<FastVarMap>({}, {});
        variableValues.first = getVarMap(funs.first, item.vals.first);
        variableValues.second = getVarMap(funs.second, item.vals.second);
        if (!item.heapSet) {
            Heap heap = randomHeap(*funs.first, variableValues.first, 5, -20,
                                   20, &seedp);
            item.heaps.first = heap;
            item.heaps.second = heap;
        }
        MonoPair<Integer> heapBackgrounds = item.heapBackgrounds.map<Integer>(
            [](auto b) { return Integer(b); });
        MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
            funs, std::move(variableValues), item.heaps, heapBackgrounds, 1000);
        callback(std::move(calls), state);
    }
}

// Each thread operates on it’s own copy of the inital value of state, when
// finished the threads are merged using the supplied merge function which has
// to be associative and the resulting state is written back to the state ref
template <typename T>
void iterateTracesInRange(
    MonoPair<llvm::Function *> funs, mpz_class lowerBound, mpz_class upperBound,
    unsigned threadsNum, T &state, std::function<T(const T &, const T &)> merge,
    std::function<void(MonoPair<Call<const llvm::Value *>>, T &)> callback) {
    assert(!(funs.first->isVarArg() || funs.second->isVarArg()));
    std::vector<VarIntVal> argValues;
    T initialState = state;
    ThreadSafeQueue<WorkItem> q;
    std::vector<std::thread> threads(threadsNum);
    std::vector<T> threadStates(threadsNum, initialState);
    for (size_t i = 0; i < threadsNum; ++i) {
        threads[i] = std::thread([&q, &callback, &funs, &threadStates, i]() {
            workerThread(q, threadStates[i], callback, funs);
        });
    }

    int counter = 0;
    assert(funs.first->getArgumentList().size() ==
           funs.second->getArgumentList().size());
    if (!InputFileFlag.empty()) {
        std::vector<WorkItem> items = parseInput(InputFileFlag);
        for (const auto &item : items) {
            q.push(item);
        }
    } else {
        for (const auto &vals : Range(lowerBound, upperBound,
                                      funs.first->getArgumentList().size())) {
            q.push({{vals, vals}, {0, 0}, {{}, {}}, false, counter});
            ++counter;
        }
    }
    for (size_t i = 0; i < threads.size(); ++i) {
        // Each of these items will terminate exactly one thread
        q.push({{{}, {}}, {0, 0}, {{}, {}}, false, -1});
    }
    for (auto &t : threads) {
        t.join();
    }
    for (auto threadState : threadStates) {
        state = merge(state, threadState);
    }
}
void dumpLoopTransformations(
    std::map<Mark, LoopTransformation> loopTransformations);
bool applyLoopTransformation(
    MonoPair<llvm::Function *> &functions, AnalysisResultsMap &analysisResults,
    const std::map<Mark, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &mark);

// This represents the states along the way from one mark to the next
template <typename T> struct PathStep { std::vector<BlockStep<T>> steps; };

template <typename T> struct SplitCall {
    std::string functionName;
    State<T> entryState;
    State<T> returnState;
    std::vector<PathStep<T>> steps;
};

template <typename T>
auto splitCallAtMarks(const Call<T> &call, BlockNameMap nameMap)
    -> SplitCall<T> {
    std::vector<PathStep<T>> pathSteps;
    std::vector<BlockStep<T>> blockSteps;
    for (const auto &step : call.steps) {
        if (normalMarkBlock(nameMap, step.blockName)) {
            pathSteps.push_back({blockSteps});
            blockSteps.clear();
        }
        blockSteps.push_back(step);
    }
    assert(blockSteps.size() == 1);
    pathSteps.push_back({blockSteps});
    // We should have at least one entry and one exit node
    assert(pathSteps.size() >= 2);
    return {call.functionName, call.entryState, call.returnState, pathSteps};
}

template <typename T>
void analyzeExecution(const MonoPair<Call<T>> &calls,
                      MonoPair<BlockNameMap> nameMaps,
                      std::function<void(MatchInfo<T>)> fun) {
    const auto call1 = splitCallAtMarks(calls.first, nameMaps.first);
    const auto call2 = splitCallAtMarks(calls.second, nameMaps.second);
    auto stepsIt1 = call1.steps.begin();
    auto stepsIt2 = call2.steps.begin();
    auto prevStepsIt1 = *stepsIt1;
    auto prevStepsIt2 = *stepsIt2;
    // The first pathstep is at an entry node and is thus not interesting to
    // us so we can start by moving to the next pathstep
    ++stepsIt1;
    ++stepsIt2;
    while (stepsIt1 != call1.steps.end() && stepsIt2 != call2.steps.end()) {
        // There are two cases to consider, either both programs are at the same
        // mark or they are at different marks. The latter case can occur when
        // one program is waiting for the other to finish its loops
        auto blockNameIntersection =
            intersection(nameMaps.first.at(stepsIt1->steps.front().blockName),
                         nameMaps.second.at(stepsIt2->steps.front().blockName));
        if (!blockNameIntersection.empty()) {
            // The flexible coupling is not yet supported so we should the
            // intersection should contain exactly one block
            assert(blockNameIntersection.size() == 1);
            Mark mark = *blockNameIntersection.begin();
            fun(MatchInfo<T>(makeMonoPair(&stepsIt1->steps.front(),
                                          &stepsIt2->steps.front()),
                             LoopInfo::None, mark));
            prevStepsIt1 = *stepsIt1;
            prevStepsIt2 = *stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In this case one program should have stayed at the same mark
            LoopInfo loop = LoopInfo::Left;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepsIt1;
            auto prevStepItOther = prevStepsIt2;
            auto end = call1.steps.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if (stepsIt2->steps.front().blockName ==
                prevStepsIt2.steps.front().blockName) {
                loop = LoopInfo::Right;
                stepsIt = stepsIt2;
                prevStepIt = prevStepsIt2;
                prevStepItOther = prevStepsIt1;
                end = call2.steps.end();
                nameMap = nameMaps.second;
                otherNameMap = nameMaps.first;
            }
            // Keep looping one program until it moves on
            do {
                const auto blockNameIntersection = intersection(
                    nameMap.at(prevStepIt.steps.front().blockName),
                    otherNameMap.at(prevStepItOther.steps.front().blockName));
                assert(blockNameIntersection.size() == 1);
                Mark mark = *blockNameIntersection.begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    const BlockStep<T> *firstStep = &stepsIt->steps.front();
                    const BlockStep<T> *secondStep =
                        &prevStepItOther.steps.front();
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                } else {
                    const BlockStep<T> *secondStep = &stepsIt->steps.front();
                    const BlockStep<T> *firstStep =
                        &prevStepItOther.steps.front();
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                }
                // Go to the next mark
                ++stepsIt;
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     stepsIt->steps.front().blockName ==
                         prevStepIt.steps.front().blockName);
            // Copy the iterator values back to the corresponding terator
            if (loop == LoopInfo::Left) {
                stepsIt1 = stepsIt;
            } else {
                stepsIt2 = stepsIt;
            }
        }
    }
}

LoopCountsAndMark mergeLoopCounts(LoopCountsAndMark counts1,
                                  LoopCountsAndMark counts2);
IterativeInvariantMap<PolynomialEquations>
mergePolynomialEquations(IterativeInvariantMap<PolynomialEquations> eq1,
                         IterativeInvariantMap<PolynomialEquations> eq2);
struct MergedAnalysisResults {
    LoopCountsAndMark loopCounts;
    IterativeInvariantMap<PolynomialEquations> polynomialEquations;
    RelationalFunctionInvariantMap<PolynomialEquations>
        relationalFunctionPolynomialEquations;
    FunctionInvariantMap<PolynomialEquations> functionPolynomialEquations;
    HeapPatternCandidatesMap heapPatternCandidates;
};

MergedAnalysisResults mergeAnalysisResults(MergedAnalysisResults res1,
                                           MergedAnalysisResults res2);

HeapPatternCandidatesMap mergeHeapPatternMaps(HeapPatternCandidatesMap cand1,
                                              HeapPatternCandidatesMap cand2);
HeapPatternCandidates
mergeHeapPatternCandidates(HeapPatternCandidates candidates1,
                           HeapPatternCandidates candidates2);

ModelValues initialModelValues(MonoPair<const llvm::Function *> funs);

ExitIndex getExitIndex(const MatchInfo<const llvm::Value *> match);

ModelValues parseZ3Model(const z3::context &z3Cxt, const z3::model &model,
                         const std::map<std::string, z3::expr> &nameMap,
                         const FreeVarsMap &freeVarsMap);

ArrayVal getArrayVal(const z3::context &z3Cxt, z3::expr arrayExpr);

void dumpCounterExample(Mark cexStart, Mark cexEndMark,
                        MonoPair<FastVarMap> &variableValues,
                        std::map<std::string, ArrayVal> &arrays);
}
}
