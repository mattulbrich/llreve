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
#include "Permutation.h"
#include "Preprocess.h"

#include "llreve/dynamic/Invariant.h"
#include "llreve/dynamic/Match.h"

#include "llvm/IR/Module.h"

#include <thread>

namespace llreve {
namespace dynamic {

template <typename V, unsigned N>
llvm::SmallVector<V, N> intersection(llvm::SmallVector<V, N> a,
                                     llvm::SmallVector<V, N> b) {
    llvm::SmallVector<V, N> c;
    set_intersection(a.begin(), a.end(), b.begin(), b.end(),
                     std::back_inserter(c));
    return c;
}
enum class LlreveResult { Equivalent, NotEquivalent };

template <typename T1, typename T2>
void zipWith(LoopInfoData<T1> &loop1, LoopInfoData<T2> &loop2,
             std::function<void(T1 &, T2 &)> f) {
    f(loop1.left, loop2.left);
    f(loop1.right, loop2.right);
    f(loop1.none, loop2.none);
}

using BlockNameMap = llvm::StringMap<llvm::SmallVector<Mark, 2>>;

std::vector<smt::SharedSMTRef> cegarDriver(
    MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
    std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    llreve::opts::FileOptions fileopts);

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

template <typename T>
Integer getReturnValue(const Call<T> &call,
                       const AnalysisResultsMap &analysisResults) {
    // Non int return values should not exist so this is safe
    return call.returnState.variables
        .find(analysisResults.at(call.function).returnInstruction)
        ->second;
}
template <typename T>
MonoPair<Integer> getReturnValues(const Call<T> &call1, const Call<T> &call2,
                                  const AnalysisResultsMap &analysisResults) {
    return {getReturnValue(call1, analysisResults),
            getReturnValue(call2, analysisResults)};
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
        // We want to count iterations rather than times we arrive at the loop
        // header so the first time is not counted.
        loopCountsAndMark.loopCounts[match.mark].push_back(makeMonoPair(0, 0));
        loopCountsAndMark.mark = match.mark;
    }
}

struct DynamicAnalysisResults;
enum class Transformed { Yes, No };

// This function has way too many arguments
Transformed analyzeMainCounterExample(
    MarkPair pathMarks, ModelValues &vals, MonoPair<llvm::Function *> functions,
    DynamicAnalysisResults &dynamicAnalysisResults,
    AnalysisResultsMap &analysisResults,
    llvm::StringMap<const llvm::Value *> &instrNameMap,
    const MonoPair<BlockNameMap> &nameMap,
    const std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
        &patterns,
    unsigned degree);
void analyzeRelationalCounterExample(
    MarkPair pathMarks, const ModelValues &vals,
    MonoPair<const llvm::Function *> functions,
    DynamicAnalysisResults &dynamicAnalysisResults,
    const MonoPair<BlockNameMap> &nameMap,
    const AnalysisResultsMap &analysisResults, unsigned maxDegree);
void analyzeFunctionalCounterExample(
    MarkPair pathMarks, const ModelValues &vals, const llvm::Function *function,
    Program program, DynamicAnalysisResults &dynamicAnalysisResults,
    const BlockNameMap &blockNameMap, const AnalysisResultsMap &analysisResults,
    unsigned maxDegree);

void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    const std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
        &patterns,
    const std::vector<smt::SortedVar> &primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex);
void populateHeapPatterns(
    RelationalFunctionInvariantMap<
        LoopInfoData<llvm::Optional<FunctionInvariant<HeapPatternCandidates>>>>
        &heapPatternCandidates,
    const std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
        &patterns,
    const std::vector<smt::SortedVar> &primitiveVariables,
    CoupledCallInfo<const llvm::Value *> match,
    MonoPair<llvm::Value *> returnValues);
void populateHeapPatterns(
    FunctionInvariantMap<HeapPatternCandidates> &heapPatternCandidates,
    const std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
        &patterns,
    const std::vector<smt::SortedVar> &primitiveVariables,
    UncoupledCallInfo<const llvm::Value *> match, llvm::Value *returnValue);
void dumpPolynomials(
    const IterativeInvariantMap<PolynomialEquations> &equationsMap,
    const FreeVarsMap &freeVarsmap);
void dumpHeapPatterns(const HeapPatternCandidatesMap &heapPatternsMap);

FastVarMap getVarMap(const llvm::Function *fun, std::vector<mpz_class> vals);

llvm::StringMap<const llvm::Value *>
instructionNameMap(const llvm::Function *fun);
llvm::StringMap<const llvm::Value *>
instructionNameMap(MonoPair<const llvm::Function *> funs);

MonoPair<FastVarMap> getVarMapFromModel(
    const llvm::StringMap<const llvm::Value *> &instructionNameMap,
    MonoPair<std::vector<smt::SortedVar>> freeVars,
    std::map<std::string, mpz_class> vals);
FastVarMap getVarMapFromModel(
    const llvm::StringMap<const llvm::Value *> &instructionNameMap,
    std::vector<smt::SortedVar> freeVars,
    std::map<std::string, mpz_class> vals);
llvm::SmallDenseMap<HeapAddress, Integer> getHeapFromModel(const ArrayVal &ar);
Heap getHeapFromModel(const std::map<std::string, ArrayVal> &arrays,
                      Program prog);
MonoPair<Heap> getHeapsFromModel(std::map<std::string, ArrayVal> arrays);
void dumpLoopTransformations(
    std::map<Mark, LoopTransformation> loopTransformations);
bool applyLoopTransformation(
    MonoPair<llvm::Function *> &functions, AnalysisResultsMap &analysisResults,
    const std::map<Mark, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &mark);

// This represents the states along the way from one mark to the next
template <typename T> struct PathStep {
    std::vector<BlockStep<T>> stepsOnPath;
    PathStep(std::vector<BlockStep<T>> stepsOnPath)
        : stepsOnPath(std::move(stepsOnPath)) {}
};

template <typename T> struct SplitCall {
    const llvm::Function *function;
    State<T> entryState;
    State<T> returnState;
    std::vector<PathStep<T>> steps;
    SplitCall(const llvm::Function *function, State<T> entryState,
              State<T> returnState, std::vector<PathStep<T>> steps)
        : function(std::move(function)), entryState(std::move(entryState)),
          returnState(std::move(returnState)), steps(std::move(steps)) {}
};

template <typename T>
auto splitCallAtMarks(Call<T> call, const BlockNameMap &nameMap)
    -> SplitCall<T> {
    std::vector<PathStep<T>> pathSteps;
    std::vector<BlockStep<T>> blockSteps;
    for (auto &step : call.steps) {
        if (normalMarkBlock(nameMap, step.blockName)) {
            pathSteps.emplace_back(std::move(blockSteps));
            blockSteps.clear();
        }
        blockSteps.emplace_back(std::move(step));
    }
    pathSteps.emplace_back(std::move(blockSteps));
    // We should have at least one entry and one exit node
    assert(pathSteps.size() >= 2);
    return {std::move(call.function), std::move(call.entryState),
            std::move(call.returnState), std::move(pathSteps)};
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
    const AnalysisResultsMap &analysisResults,
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
            analyzeCoupledCalls(*callIt1, *callIt2, nameMaps, analysisResults,
                                relationalCallMatch, functionalCallMatch);
            ++callIt1;
            ++callIt2;
            break;
        case InterleaveStep::StepFirst:
            analyzeUncoupledCall(*callIt1, nameMaps.first, Program::First,
                                 analysisResults, functionalCallMatch);
            ++callIt1;
            break;
        case InterleaveStep::StepSecond:
            analyzeUncoupledCall(*callIt2, nameMaps.second, Program::Second,
                                 analysisResults, functionalCallMatch);
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
    const AnalysisResultsMap &analysisResults,
    std::function<void(CoupledCallInfo<T>)> relationalCallMatch,
    std::function<void(UncoupledCallInfo<T>)> functionalCallMatch) {
    MonoPair<const llvm::Function *> functions = {call1_.function,
                                                  call2_.function};
    const auto returnValues = getReturnValues(call1_, call2_, analysisResults);
    const auto call1 = splitCallAtMarks(std::move(call1_), nameMaps.first);
    const auto call2 = splitCallAtMarks(std::move(call2_), nameMaps.second);
    auto stepsIt1 = call1.steps.begin();
    auto stepsIt2 = call2.steps.begin();
    auto prevStepsIt1 = stepsIt1;
    auto prevStepsIt2 = stepsIt2;
    while (stepsIt1 != call1.steps.end() && stepsIt2 != call2.steps.end()) {
        // There are two cases to consider, either both programs are at the same
        // mark or they are at different marks. The latter case can occur when
        // one program is waiting for the other to finish its loops
        auto blockNameIntersection = intersection(
            nameMaps.first.find(stepsIt1->stepsOnPath.front().blockName)
                ->second,
            nameMaps.second.find(stepsIt2->stepsOnPath.front().blockName)
                ->second);
        if (!blockNameIntersection.empty()) {
            if (stepsIt1 != prevStepsIt1 && stepsIt2 != prevStepsIt2) {
                // We can only start analyzing calls if we already moved away
                // from the start
                analyzeCallsOnPaths(*prevStepsIt1, *prevStepsIt2, nameMaps,
                                    analysisResults, relationalCallMatch,
                                    functionalCallMatch);
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
                                     analysisResults, functionalCallMatch);
                const auto blockNameIntersection = intersection(
                    nameMap[prevStepIt->stepsOnPath.front().blockName],
                    otherNameMap[prevStepItOther->stepsOnPath.front()
                                     .blockName]);
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
    analyzeCallsOnPaths(*prevStepsIt1, *prevStepsIt2, nameMaps, analysisResults,
                        relationalCallMatch, functionalCallMatch);
    assert(stepsIt1 == call1.steps.end());
    assert(stepsIt2 == call2.steps.end());
}

template <typename T>
void analyzeUncoupledPath(
    const PathStep<T> &path, const BlockNameMap &nameMap, Program prog,
    const AnalysisResultsMap &analysisResults,
    std::function<void(UncoupledCallInfo<T>)> functionCallMatch) {
    auto calls = extractCalls(path);
    for (const auto &call : calls) {
        analyzeUncoupledCall(call, nameMap, prog, analysisResults,
                             functionCallMatch);
    }
}

template <typename T>
void analyzeUncoupledCall(
    const Call<T> &call_, const BlockNameMap &nameMap, Program prog,
    const AnalysisResultsMap &analysisResults,
    std::function<void(UncoupledCallInfo<T>)> functionCallMatch) {
    const llvm::Function *function = call_.function;
    const auto returnValue = getReturnValue(call_, analysisResults);
    auto call = splitCallAtMarks(std::move(call_), nameMap);
    for (const auto &step : call.steps) {
        auto markSet = nameMap.find(step.stepsOnPath.front().blockName)->second;
        assert(markSet.size() == 1);
        auto mark = *markSet.begin();
        functionCallMatch(UncoupledCallInfo<T>(
            function, &step.stepsOnPath.front(), returnValue, mark, prog));
        analyzeUncoupledPath(step, nameMap, prog, analysisResults,
                             functionCallMatch);
    }
}

template <typename T>
void analyzeExecution(
    MonoPair<Call<T>> calls, const MonoPair<BlockNameMap> &nameMaps,
    const AnalysisResultsMap &analysisResults,
    std::function<void(MatchInfo<T>)> iterativeMatch,
    std::function<void(CoupledCallInfo<T>)> relationalCallMatch,
    std::function<void(UncoupledCallInfo<T>)> functionalCallMatch) {
    const auto call1 = splitCallAtMarks(std::move(calls.first), nameMaps.first);
    const auto call2 =
        splitCallAtMarks(std::move(calls.second), nameMaps.second);
    auto stepsIt1 = call1.steps.begin();
    auto stepsIt2 = call2.steps.begin();
    auto prevStepsIt1 = *stepsIt1;
    auto prevStepsIt2 = *stepsIt2;
    // The first pathstep is at an entry node and is thus not interesting to
    // us so we can start by moving to the next pathstep.
    ++stepsIt1;
    ++stepsIt2;
    while (stepsIt1 != call1.steps.end() && stepsIt2 != call2.steps.end()) {
        // There are two cases to consider, either both programs are at the
        // same
        // mark or they are at different marks. The latter case can occur
        // when
        // one program is waiting for the other to finish its loops
        auto blockNameIntersection = intersection(
            nameMaps.first.find(stepsIt1->stepsOnPath.front().blockName)
                ->second,
            nameMaps.second.find(stepsIt2->stepsOnPath.front().blockName)
                ->second);
        if (!blockNameIntersection.empty()) {
            // We want to match calls on the paths that led us here
            analyzeCallsOnPaths(prevStepsIt1, prevStepsIt2, nameMaps,
                                analysisResults, relationalCallMatch,
                                functionalCallMatch);
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
                analyzeUncoupledPath(prevStepIt, nameMap, prog, analysisResults,
                                     functionalCallMatch);
                const auto blockNameIntersection = intersection(
                    nameMap.find(prevStepIt.stepsOnPath.front().blockName)
                        ->second,
                    otherNameMap
                        .find(prevStepItOther.stepsOnPath.front().blockName)
                        ->second);
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
    // There can be calls on the way to the return block which we need to
    // take a
    // look at here
    analyzeCallsOnPaths(prevStepsIt1, prevStepsIt2, nameMaps, analysisResults,
                        relationalCallMatch, functionalCallMatch);
    // This assertion is only correct if the interpreter didn’t stop because it
    // ran out of steps
    // assert(stepsIt1 == call1.steps.end());
    // assert(stepsIt2 == call2.steps.end());
}

struct DynamicAnalysisResults {
    LoopCountsAndMark loopCounts;
    IterativeInvariantMap<PolynomialEquations> polynomialEquations;
    RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>>
        relationalFunctionPolynomialEquations;
    FunctionInvariantMap<Matrix<mpq_class>> functionPolynomialEquations;
    HeapPatternCandidatesMap heapPatternCandidates;
    RelationalFunctionInvariantMap<
        LoopInfoData<llvm::Optional<FunctionInvariant<HeapPatternCandidates>>>>
        relationalFunctionHeapPatterns;
    FunctionInvariantMap<HeapPatternCandidates> functionHeapPatterns;
};
ModelValues initialModelValues(MonoPair<const llvm::Function *> funs);

ExitIndex getExitIndex(const MatchInfo<const llvm::Value *> match);

ModelValues parseZ3Model(const z3::context &z3Cxt, const z3::model &model,
                         const std::map<std::string, z3::expr> &nameMap,
                         const AnalysisResultsMap &analysisResults);

ArrayVal getArrayVal(const z3::context &z3Cxt, z3::expr arrayExpr);

void dumpCounterExample(Mark cexStart, Mark cexEndMark,
                        const FastVarMap &variableValues,
                        const std::map<std::string, ArrayVal> &arrays);
void dumpCounterExample(Mark cexStart, Mark cexEndMark,
                        const MonoPair<FastVarMap> &variableValues,
                        const std::map<std::string, ArrayVal> &arrays);
}
}
