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
#include "llreve/dynamic/Match.h"

#include "llvm/IR/Module.h"

#include <thread>

namespace llreve {
namespace dynamic {

extern std::string InputFileFlag;

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
void insertInblockNameMap(BlockNameMap &nameMap,
                          const BidirBlockMarkMap &blockMap);
MonoPair<BlockNameMap>
getBlockNameMaps(const AnalysisResultsMap &analysisResults);

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

template <typename T> VarIntVal getReturnValue(const Call<T> &call) {
    // Non int return values should not exist so this is safe
    return unsafeIntVal(call.returnState.variables.at(ReturnName));
}
template <typename T>
MonoPair<VarIntVal> getReturnValues(const Call<T> &call1,
                                    const Call<T> &call2) {
    return {getReturnValue(call1), getReturnValue(call2)};
}

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

struct MergedAnalysisResults;
enum class Transformed { Yes, No };

// This function has way too many arguments
Transformed analyzeMainCounterExample(
    Mark cexStartMark, Mark cexEndMark, ModelValues &vals,
    MonoPair<llvm::Function *> functions,
    MergedAnalysisResults &dynamicAnalysisResults,
    AnalysisResultsMap &analysisResults,
    std::map<std::string, const llvm::Value *> &instrNameMap,
    const MonoPair<BlockNameMap> &nameMap,
    const std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
        &patterns,
    unsigned degree);
void analyzeRelationalCounterExample();
void analyzeFunctionalCounterExample();

void instantiateBounds(
    std::map<Mark, std::map<std::string, Bound<VarIntVal>>> &boundsMap,
    const FreeVarsMap &freeVars, MatchInfo<std::string> match);
BoundsMap updateBounds(
    BoundsMap accumulator,
    const std::map<Mark, std::map<std::string, Bound<VarIntVal>>> &update);
void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    const std::vector<smt::SortedVar> &primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex);
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
        MonoPair<Call<const llvm::Value *>> calls =
            interpretFunctionPair(funs, std::move(variableValues), item.heaps,
                                  heapBackgrounds, 10000);
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
template <typename T> struct PathStep {
    std::vector<BlockStep<T>> stepsOnPath;
};

template <typename T> struct SplitCall {
    const llvm::Function *function;
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
    return {call.function, call.entryState, call.returnState, pathSteps};
}

template <typename T>
auto extractCalls(const PathStep<T> &path) -> std::vector<Call<T>> {
    std::vector<Call<T>> calls;
    for (const auto &step : path.stepsOnPath) {
        calls.insert(calls.end(), step.calls.begin(), step.calls.end());
    }
    return calls;
}

template <typename T>
bool coupledCalls(const Call<T> &call1, const Call<T> &call2) {
    // TODO maybe don’t use names here but whatever
    return call1.function->getName() == call2.function->getName();
};

template <typename T>
void analyzeCallsOnPaths(
    const PathStep<T> &path1, const PathStep<T> &path2,
    const MonoPair<BlockNameMap> &nameMaps,
    std::function<void(CoupledCallInfo<T>)> relationalCallMatch,
    std::function<void(UncoupledCallInfo<T>)> functionalCallMatch) {
    auto calls1 = extractCalls(path1);
    auto calls2 = extractCalls(path2);
    auto coupleSteps = matchFunCalls(calls1, calls2, coupledCalls<T>);
    auto callIt1 = calls1.begin();
    auto callIt2 = calls2.begin();
    for (const auto step : coupleSteps) {
        switch (step) {
        case InterleaveStep::StepBoth:
            analyzeCoupledCalls(*callIt1, *callIt2, nameMaps,
                                relationalCallMatch, functionalCallMatch);
            ++callIt1;
            ++callIt2;
            break;
        case InterleaveStep::StepFirst:
            analyzeUncoupledCall(*callIt1, nameMaps.first, Program::First,
                                 functionalCallMatch);
            ++callIt1;
            break;
        case InterleaveStep::StepSecond:
            analyzeUncoupledCall(*callIt2, nameMaps.second, Program::Second,
                                 functionalCallMatch);
            ++callIt2;
            break;
        }
    }
    assert(callIt1 == calls1.end());
    assert(callIt2 == calls2.end());
}

// TODO this is only a slight variation of analyzeExecution, it might make sense
// to unify those two
template <typename T>
void analyzeCoupledCalls(
    const Call<T> &call1_, const Call<T> &call2_,
    const MonoPair<BlockNameMap> &nameMaps,
    std::function<void(CoupledCallInfo<T>)> relationalCallMatch,
    std::function<void(UncoupledCallInfo<T>)> functionalCallMatch) {
    MonoPair<const llvm::Function *> functions = {call1_.function,
                                                  call2_.function};
    const auto returnValues = getReturnValues(call1_, call2_);
    const auto call1 = splitCallAtMarks(call1_, nameMaps.first);
    const auto call2 = splitCallAtMarks(call2_, nameMaps.second);
    auto stepsIt1 = call1.steps.begin();
    auto stepsIt2 = call2.steps.begin();
    auto prevStepsIt1 = stepsIt1;
    auto prevStepsIt2 = stepsIt2;
    while (stepsIt1 != call1.steps.end() && stepsIt2 != call2.steps.end()) {
        // There are two cases to consider, either both programs are at the same
        // mark or they are at different marks. The latter case can occur when
        // one program is waiting for the other to finish its loops
        auto blockNameIntersection = intersection(
            nameMaps.first.at(stepsIt1->stepsOnPath.front().blockName),
            nameMaps.second.at(stepsIt2->stepsOnPath.front().blockName));
        if (!blockNameIntersection.empty()) {
            if (stepsIt1 != prevStepsIt1 && stepsIt2 != prevStepsIt2) {
                // We can only start analyzing calls if we already moved away
                // from the start
                analyzeCallsOnPaths(*prevStepsIt1, *prevStepsIt2, nameMaps,
                                    relationalCallMatch, functionalCallMatch);
            }
            // The flexible coupling is not yet supported so we should the
            // intersection should contain exactly one block
            assert(blockNameIntersection.size() == 1);
            Mark mark = *blockNameIntersection.begin();
            relationalCallMatch(
                CoupledCallInfo<T>(functions, {&stepsIt1->stepsOnPath.front(),
                                               &stepsIt2->stepsOnPath.front()},
                                   returnValues, LoopInfo::None, mark));
            prevStepsIt1 = stepsIt1;
            prevStepsIt2 = stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In this case one program should have stayed at the same mark
            LoopInfo loop = LoopInfo::Left;
            Program prog = Program::First;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepsIt1;
            auto prevStepItOther = prevStepsIt2;
            auto end = call1.steps.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if (stepsIt2->stepsOnPath.front().blockName ==
                prevStepsIt2->stepsOnPath.front().blockName) {
                loop = LoopInfo::Right;
                prog = Program::Second;
                stepsIt = stepsIt2;
                prevStepIt = prevStepsIt2;
                prevStepItOther = prevStepsIt1;
                end = call2.steps.end();
                nameMap = nameMaps.second;
                otherNameMap = nameMaps.first;
            }
            // Keep looping one program until it moves on
            do {
                analyzeUncoupledPath(*prevStepIt, nameMap, prog,
                                     functionalCallMatch);
                const auto blockNameIntersection = intersection(
                    nameMap.at(prevStepIt->stepsOnPath.front().blockName),
                    otherNameMap.at(
                        prevStepItOther->stepsOnPath.front().blockName));
                assert(blockNameIntersection.size() == 1);
                Mark mark = *blockNameIntersection.begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    const BlockStep<T> *firstStep =
                        &stepsIt->stepsOnPath.front();
                    const BlockStep<T> *secondStep =
                        &prevStepItOther->stepsOnPath.front();
                    relationalCallMatch(
                        CoupledCallInfo<T>(functions, {firstStep, secondStep},
                                           returnValues, loop, mark));
                } else {
                    const BlockStep<T> *secondStep =
                        &stepsIt->stepsOnPath.front();
                    const BlockStep<T> *firstStep =
                        &prevStepItOther->stepsOnPath.front();
                    relationalCallMatch(
                        CoupledCallInfo<T>(functions, {firstStep, secondStep},
                                           returnValues, loop, mark));
                }
                // Go to the next mark
                ++stepsIt;
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     stepsIt->stepsOnPath.front().blockName ==
                         prevStepIt->stepsOnPath.front().blockName);
            // Copy the iterator values back to the corresponding terator
            if (loop == LoopInfo::Left) {
                stepsIt1 = stepsIt;
            } else {
                stepsIt2 = stepsIt;
            }
        }
    }
}

template <typename T>
void analyzeUncoupledPath(
    const PathStep<T> &path, const BlockNameMap &nameMap, Program prog,
    std::function<void(UncoupledCallInfo<T>)> functionCallMatch) {}

template <typename T>
void analyzeUncoupledCall(
    const Call<T> &call_, const BlockNameMap &nameMap, Program prog,
    std::function<void(UncoupledCallInfo<T>)> functionCallMatch) {
    const auto returnValue = getReturnValue(call_);
    auto call = splitCallAtMarks(call_, nameMap);
    for (const auto &step : call.steps) {
        auto markSet = nameMap.at(step.stepsOnPath.front().blockName);
        assert(markSet.size() == 1);
        auto mark = *markSet.begin();
        functionCallMatch(UncoupledCallInfo<T>(call_.function,
                                               &step.stepsOnPath.front(),
                                               returnValue, mark, prog));
        analyzeUncoupledPath(step, nameMap, prog, functionCallMatch);
    }
}

template <typename T>
void analyzeExecution(
    const MonoPair<Call<T>> &calls, MonoPair<BlockNameMap> nameMaps,
    std::function<void(MatchInfo<T>)> iterativeMatch,
    std::function<void(CoupledCallInfo<T>)> relationalCallMatch,
    std::function<void(UncoupledCallInfo<T>)> functionalCallMatch) {
    const auto call1 = splitCallAtMarks(calls.first, nameMaps.first);
    const auto call2 = splitCallAtMarks(calls.second, nameMaps.second);
    auto stepsIt1 = call1.steps.begin();
    auto stepsIt2 = call2.steps.begin();
    auto prevStepsIt1 = *stepsIt1;
    auto prevStepsIt2 = *stepsIt2;
    // The first pathstep is at an entry node and is thus not interesting to
    // us so we can start by moving to the next pathstep.
    ++stepsIt1;
    ++stepsIt2;
    while (stepsIt1 != call1.steps.end() && stepsIt2 != call2.steps.end()) {
        // There are two cases to consider, either both programs are at the same
        // mark or they are at different marks. The latter case can occur when
        // one program is waiting for the other to finish its loops
        auto blockNameIntersection = intersection(
            nameMaps.first.at(stepsIt1->stepsOnPath.front().blockName),
            nameMaps.second.at(stepsIt2->stepsOnPath.front().blockName));
        if (!blockNameIntersection.empty()) {
            // We want to match calls on the paths that led us here
            analyzeCallsOnPaths(prevStepsIt1, prevStepsIt2, nameMaps,
                                relationalCallMatch, functionalCallMatch);
            // The flexible coupling is not yet supported so we should the
            // intersection should contain exactly one block
            assert(blockNameIntersection.size() == 1);
            Mark mark = *blockNameIntersection.begin();
            iterativeMatch(
                MatchInfo<T>(makeMonoPair(&stepsIt1->stepsOnPath.front(),
                                          &stepsIt2->stepsOnPath.front()),
                             LoopInfo::None, mark));
            prevStepsIt1 = *stepsIt1;
            prevStepsIt2 = *stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In this case one program should have stayed at the same mark
            LoopInfo loop = LoopInfo::Left;
            Program prog = Program::First;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepsIt1;
            auto prevStepItOther = prevStepsIt2;
            auto end = call1.steps.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if (stepsIt2->stepsOnPath.front().blockName ==
                prevStepsIt2.stepsOnPath.front().blockName) {
                loop = LoopInfo::Right;
                prog = Program::Second;
                stepsIt = stepsIt2;
                prevStepIt = prevStepsIt2;
                prevStepItOther = prevStepsIt1;
                end = call2.steps.end();
                nameMap = nameMaps.second;
                otherNameMap = nameMaps.first;
            }
            // Keep looping one program until it moves on
            do {
                analyzeUncoupledPath(prevStepIt, nameMap, prog,
                                     functionalCallMatch);
                const auto blockNameIntersection = intersection(
                    nameMap.at(prevStepIt.stepsOnPath.front().blockName),
                    otherNameMap.at(
                        prevStepItOther.stepsOnPath.front().blockName));
                assert(blockNameIntersection.size() == 1);
                Mark mark = *blockNameIntersection.begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    const BlockStep<T> *firstStep =
                        &stepsIt->stepsOnPath.front();
                    const BlockStep<T> *secondStep =
                        &prevStepItOther.stepsOnPath.front();
                    iterativeMatch(MatchInfo<T>(
                        makeMonoPair(firstStep, secondStep), loop, mark));
                } else {
                    const BlockStep<T> *secondStep =
                        &stepsIt->stepsOnPath.front();
                    const BlockStep<T> *firstStep =
                        &prevStepItOther.stepsOnPath.front();
                    iterativeMatch(MatchInfo<T>(
                        makeMonoPair(firstStep, secondStep), loop, mark));
                }
                // Go to the next mark
                ++stepsIt;
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     stepsIt->stepsOnPath.front().blockName ==
                         prevStepIt.stepsOnPath.front().blockName);
            // Copy the iterator values back to the corresponding terator
            if (loop == LoopInfo::Left) {
                stepsIt1 = stepsIt;
            } else {
                stepsIt2 = stepsIt;
            }
        }
    }
    // There can be calls on the way to the return block which we need to take a
    // look at here
    analyzeCallsOnPaths(prevStepsIt1, prevStepsIt2, nameMaps,
                        relationalCallMatch, functionalCallMatch);
    assert(stepsIt1 == call1.steps.end());
    assert(stepsIt2 == call2.steps.end());
}

LoopCountsAndMark mergeLoopCounts(LoopCountsAndMark counts1,
                                  LoopCountsAndMark counts2);
IterativeInvariantMap<PolynomialEquations>
mergePolynomialEquations(IterativeInvariantMap<PolynomialEquations> eq1,
                         IterativeInvariantMap<PolynomialEquations> eq2);
struct MergedAnalysisResults {
    LoopCountsAndMark loopCounts;
    IterativeInvariantMap<PolynomialEquations> polynomialEquations;
    RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>>
        relationalFunctionPolynomialEquations;
    FunctionInvariantMap<Matrix<mpq_class>> functionPolynomialEquations;
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
                         MonoPair<const llvm::Function *> functions,
                         const AnalysisResultsMap &analysisResults);

ArrayVal getArrayVal(const z3::context &z3Cxt, z3::expr arrayExpr);

void dumpCounterExample(Mark cexStart, Mark cexEndMark,
                        const MonoPair<FastVarMap> &variableValues,
                        const std::map<std::string, ArrayVal> &arrays);
}
}
