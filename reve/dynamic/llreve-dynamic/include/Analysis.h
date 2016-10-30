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

template <typename T> struct Bound {
    T lower;
    T upper;
    Bound(T lower, T upper) : lower(lower), upper(upper) {}
};

template <typename T> struct LoopInfoData {
    T left;
    T right;
    T none;
    LoopInfoData() = default;
    LoopInfoData(T left, T right, T none)
        : left(left), right(right), none(none) {}
};

template <typename T1, typename T2>
void zipWith(LoopInfoData<T1> &loop1, LoopInfoData<T2> &loop2,
             std::function<void(T1 &, T2 &)> f) {
    f(loop1.left, loop2.left);
    f(loop1.right, loop2.right);
    f(loop1.none, loop2.none);
}

using ExitIndex = mpz_class;

using BlockNameMap = std::map<std::string, std::set<Mark>>;
using HeapPatternCandidates =
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>;
using HeapPatternCandidatesMap = std::map<
    Mark,
    std::map<ExitIndex, LoopInfoData<llvm::Optional<HeapPatternCandidates>>>>;
using BoundsMap =
    std::map<Mark, std::map<std::string, Bound<llvm::Optional<VarIntVal>>>>;

std::vector<smt::SharedSMTRef>
driver(MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
       std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
       llreve::opts::FileOptions fileopts);
std::vector<smt::SharedSMTRef> cegarDriver(
    MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    llreve::opts::FileOptions fileopts);
llvm::Optional<MonoPair<llvm::Function *>>
findFunction(std::vector<MonoPair<llvm::Function *>> functions,
             std::string functionName);
Heap randomHeap(const llvm::Function &fun,
                const std::map<const llvm::Value *, VarVal> &variableValues,
                int lengthBound, int valLowerBound, int valUpperBound,
                unsigned int *seedp);

using Equality = MonoPair<std::string>;
using PolynomialEquations =
    std::map<Mark, std::map<ExitIndex,
                            LoopInfoData<std::vector<std::vector<mpq_class>>>>>;
using PolynomialSolutions =
    std::map<Mark, std::map<ExitIndex,
                            LoopInfoData<std::vector<std::vector<mpz_class>>>>>;

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

// Walks through the two calls and calls the function for every pair of matching
// marks
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
void populateEquationsMap(PolynomialEquations &equationsMap,
                          FreeVarsMap freeVarsMap,
                          MatchInfo<const llvm::Value *> match,
                          ExitIndex exitIndex, size_t degree);
void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match,
    ExitIndex exitIndex);
void dumpPolynomials(const PolynomialEquations &equationsMap,
                     const FreeVarsMap &freeVarsmap);
void dumpHeapPatterns(const HeapPatternCandidatesMap &heapPatternsMap);
std::map<Mark, smt::SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const HeapPatternCandidatesMap &patterns,
                         const FreeVarsMap &freeVarsMap, size_t degree);
smt::SharedSMTRef
makeInvariantDefinition(const std::vector<std::vector<mpz_class>> &solution,
                        const HeapPatternCandidates &candidates,
                        const std::vector<smt::SortedVar> &freeVars,
                        size_t degree);
smt::SharedSMTRef makeEquation(const std::vector<mpz_class> &eq,
                               const std::vector<smt::SortedVar> &freeVars,
                               size_t degree);
smt::SharedSMTRef makeBoundsDefinitions(
    const std::map<std::string, Bound<llvm::Optional<VarIntVal>>> &bounds);
PolynomialSolutions findSolutions(const PolynomialEquations &equationsMap);
void dumpBounds(const BoundsMap &bounds);

std::map<const llvm::Value *, VarVal> getVarMap(const llvm::Function *fun,
                                                std::vector<mpz_class> vals);

std::map<std::string, const llvm::Value *>
instructionNameMap(const llvm::Function *fun);
std::map<std::string, const llvm::Value *>
instructionNameMap(MonoPair<const llvm::Function *> funs);

MonoPair<std::map<const llvm::Value *, VarVal>> getVarMapFromModel(
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
        MonoPair<std::map<const llvm::Value *, VarVal>> variableValues =
            makeMonoPair<std::map<const llvm::Value *, VarVal>>({}, {});
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
std::vector<std::vector<std::string>>
polynomialTermsOfDegree(std::vector<smt::SortedVar> variables, size_t degree);

template <typename T>
void analyzeExecution(const MonoPair<Call<T>> &calls,
                      MonoPair<BlockNameMap> nameMaps,
                      std::function<void(MatchInfo<T>)> fun) {
    const std::vector<BlockStep<T>> &steps1 = calls.first.steps;
    const std::vector<BlockStep<T>> &steps2 = calls.second.steps;
    auto stepsIt1 = steps1.begin();
    auto stepsIt2 = steps2.begin();
    auto prevStepIt1 = *stepsIt1;
    auto prevStepIt2 = *stepsIt2;
    while (stepsIt1 != steps1.end() && stepsIt2 != steps2.end()) {
        // Advance until a mark is reached
        while (stepsIt1 != steps1.end() &&
               !normalMarkBlock(nameMaps.first, stepsIt1->blockName)) {
            stepsIt1++;
        }
        while (stepsIt2 != steps2.end() &&
               !normalMarkBlock(nameMaps.second, stepsIt2->blockName)) {
            stepsIt2++;
        }
        if (stepsIt1 == steps1.end() && stepsIt2 == steps2.end()) {
            break;
        }
        // Check marks
        if (!intersection(nameMaps.first.at(stepsIt1->blockName),
                          nameMaps.second.at(stepsIt2->blockName))
                 .empty()) {
            assert(intersection(nameMaps.first.at(stepsIt1->blockName),
                                nameMaps.second.at(stepsIt2->blockName))
                       .size() == 1);
            // We resolve the ambiguity in the marks by hoping that for one
            // program there is only one choice
            Mark mark = *intersection(nameMaps.first.at(stepsIt1->blockName),
                                      nameMaps.second.at(stepsIt2->blockName))
                             .begin();
            // Perfect synchronization
            fun(MatchInfo<T>(makeMonoPair(&*stepsIt1, &*stepsIt2),
                             LoopInfo::None, mark));
            prevStepIt1 = *stepsIt1;
            prevStepIt2 = *stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In the first round this is not true, but we should never fall in
            // this case in the first round
            assert(&prevStepIt1 != &*stepsIt1);
            assert(&prevStepIt2 != &*stepsIt2);

            // One side has to wait for the other to finish its loop
            LoopInfo loop = LoopInfo::Left;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepIt1;
            auto prevStepItOther = prevStepIt2;
            auto end = steps1.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if (stepsIt2->blockName == prevStepIt2.blockName) {
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
                assert(intersection(nameMap.at(prevStepIt.blockName),
                                    otherNameMap.at(prevStepItOther.blockName))
                           .size() == 1);
                Mark mark =
                    *intersection(nameMap.at(prevStepIt.blockName),
                                  otherNameMap.at(prevStepItOther.blockName))
                         .begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    const BlockStep<T> *firstStep = &*stepsIt;
                    const BlockStep<T> *secondStep = &prevStepItOther;
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                } else {
                    const BlockStep<T> *secondStep = &*stepsIt;
                    const BlockStep<T> *firstStep = &prevStepItOther;
                    fun(MatchInfo<T>(makeMonoPair(firstStep, secondStep), loop,
                                     mark));
                }
                // Go to the next mark
                do {
                    stepsIt++;
                } while (stepsIt != end &&
                         !normalMarkBlock(nameMap, stepsIt->blockName));
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     stepsIt->blockName == prevStepIt.blockName);
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

LoopCountsAndMark mergeLoopCounts(LoopCountsAndMark counts1,
                                  LoopCountsAndMark counts2);
PolynomialEquations mergePolynomialEquations(PolynomialEquations eq1,
                                             PolynomialEquations eq2);
struct MergedAnalysisResults {
    LoopCountsAndMark loopCounts;
    PolynomialEquations polynomialEquations;
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
}
}
