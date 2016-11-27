/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "FunctionSMTGeneration.h"

#include "Compat.h"
#include "Declaration.h"
#include "FreeVariables.h"
#include "Invariant.h"
#include "ModuleSMTGeneration.h"
#include "Opts.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"

#include <iostream>

using llvm::CmpInst;

using std::function;
using std::make_pair;
using std::make_shared;
using std::make_unique;
using std::map;
using std::set;
using std::string;
using std::string;
using std::unique_ptr;
using std::vector;

using namespace smt;
using namespace llreve::opts;

vector<SharedSMTRef>
relationalFunctionAssertions(MonoPair<const llvm::Function *> functions,
                             const AnalysisResultsMap &analysisResults) {
    const auto pathMaps = getPathMaps(functions, analysisResults);
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = getBlockMarkMaps(functions, analysisResults);
    const string funName = getFunctionName(functions);
    const auto funArgsPair = getFunctionArguments(functions, analysisResults);
    const auto freeVarsMap = getFreeVarsMap(functions, analysisResults);
    const auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap,
        [&freeVarsMap, funName](Mark startIndex, Mark endIndex) {
            return invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                             freeVarsMap.at(endIndex), ProgramSelection::Both,
                             funName, freeVarsMap);
        });

    map<MarkPair, vector<SharedSMTRef>> smtExprs;
    for (const auto &it : synchronizedPaths) {
        const SharedSMTRef endInvariant =
            invariant(it.first.startMark, it.first.endMark,
                      freeVarsMap.at(it.first.startMark),
                      freeVarsMap.at(it.first.endMark), ProgramSelection::Both,
                      funName, freeVarsMap);
        for (const auto &path : it.second) {
            auto clause = forallStartingAt(
                path, freeVarsMap.at(it.first.startMark), it.first.startMark,
                ProgramSelection::Both, funName, false, freeVarsMap);
            smtExprs[it.first].push_back(clause);
        }
    }

    const auto forbiddenPaths =
        getForbiddenPaths(pathMaps, marked, freeVarsMap, funName, false);
    for (const auto &it : forbiddenPaths) {
        for (const auto &path : it.second) {
            auto clause = forallStartingAt(path, freeVarsMap.at(it.first),
                                           it.first, ProgramSelection::Both,
                                           funName, false, freeVarsMap);
            smtExprs[{it.first, FORBIDDEN_MARK}].push_back(clause);
        }
    }

    if (SMTGenerationOpts::getInstance().PerfectSync ==
        PerfectSynchronization::Disabled) {
        const auto offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                                freeVarsMap, funName, false);
        for (const auto &it : offByNPaths) {
            for (const auto &path : it.second) {
                auto clause =
                    forallStartingAt(path, freeVarsMap.at(it.first.startMark),
                                     it.first.startMark, ProgramSelection::Both,
                                     funName, false, freeVarsMap);
                smtExprs[{it.first.startMark, it.first.startMark}].push_back(
                    clause);
            }
        }
    }

    return clauseMapToClauseVector(smtExprs, false, ProgramSelection::Both,
                                   getFunctionNumeralConstraints(functions));
}

// the main function that we want to check doesn’t need the output
// parameters in
// the assertions since it is never called
vector<SharedSMTRef>
relationalIterativeAssertions(MonoPair<const llvm::Function *> functions,
                              const AnalysisResultsMap &analysisResults) {
    const auto pathMaps = getPathMaps(functions, analysisResults);
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = getBlockMarkMaps(functions, analysisResults);
    const string funName = getFunctionName(functions);
    const auto funArgsPair = getFunctionArguments(functions, analysisResults);
    const auto freeVarsMap = getFreeVarsMap(functions, analysisResults);
    vector<SharedSMTRef> smtExprs;

    const llvm::Type *returnType = functions.first->getReturnType();
    if (SMTGenerationOpts::getInstance().OnlyRecursive ==
        FunctionEncoding::OnlyRecursive) {
        smtExprs.push_back(
            equalInputsEqualOutputs(freeVarsMap.at(ENTRY_MARK),
                                    filterVars(1, freeVarsMap.at(ENTRY_MARK)),
                                    filterVars(2, freeVarsMap.at(ENTRY_MARK)),
                                    funName, freeVarsMap, returnType));
        return smtExprs;
    }

    auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap,
        [&freeVarsMap, funName](Mark startIndex, Mark endIndex) {
            SMTRef endInvariant =
                mainInvariant(endIndex, freeVarsMap.at(endIndex), funName);
            if (SMTGenerationOpts::getInstance().OutputFormat ==
                    SMTFormat::Z3 &&
                endIndex == EXIT_MARK) {
                endInvariant =
                    makeOp("=>", makeOp("not", std::move(endInvariant)),
                           make_unique<TypedVariable>("END_QUERY", boolType()));
            }
            return endInvariant;
        });

    const auto forbiddenPaths =
        getForbiddenPaths(pathMaps, marked, freeVarsMap, funName, true);
    if (SMTGenerationOpts::getInstance().PerfectSync ==
        PerfectSynchronization::Disabled) {
        const auto offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                                freeVarsMap, funName, true);
        synchronizedPaths = mergeVectorMaps(synchronizedPaths, offByNPaths);
    }

    map<MarkPair, vector<SharedSMTRef>> clauses;
    for (const auto &it : synchronizedPaths) {
        for (auto &path : it.second) {
            auto clause = forallStartingAt(
                path, freeVarsMap.at(it.first.startMark), it.first.startMark,
                ProgramSelection::Both, funName, true, freeVarsMap);
            clauses[it.first].push_back(clause);
        }
    }
    for (const auto &it : forbiddenPaths) {
        for (auto &path : it.second) {
            auto clause = forallStartingAt(path, freeVarsMap.at(it.first),
                                           it.first, ProgramSelection::Both,
                                           funName, true, freeVarsMap);
            clauses[{it.first, FORBIDDEN_MARK}].push_back(clause);
        }
    }

    return clauseMapToClauseVector(clauses, true, ProgramSelection::Both,
                                   getFunctionNumeralConstraints(functions));
}

/* --------------------------------------------------------------------------
 */
// Generate SMT for all paths

map<MarkPair, vector<SharedSMTRef>>
getSynchronizedPaths(const PathMap &pathMap1, const PathMap &pathMap2,
                     const FreeVarsMap &freeVarsMap,
                     ReturnInvariantGenerator generateReturnInvariant) {
    map<MarkPair, vector<SharedSMTRef>> clauses;
    for (const auto &pathMapIt : pathMap1) {
        const Mark startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const Mark endIndex = innerPathMapIt.first;
            if (pathMap2.at(startIndex).find(endIndex) !=
                pathMap2.at(startIndex).end()) {
                const auto paths = pathMap2.at(startIndex).at(endIndex);
                for (const auto &path1 : innerPathMapIt.second) {
                    for (const auto &path2 : paths) {
                        bool returnPath = endIndex == EXIT_MARK;
                        const auto assignments1 = assignmentsOnPath(
                            path1, Program::First, freeVarsMap.at(startIndex),
                            returnPath);
                        const auto assignments2 = assignmentsOnPath(
                            path2, Program::Second, freeVarsMap.at(startIndex),
                            returnPath);
                        clauses[{startIndex, endIndex}].push_back(
                            interleaveAssignments(
                                generateReturnInvariant(startIndex, endIndex),
                                assignments1, assignments2));
                    }
                }
            }
        }
    }

    return clauses;
}

map<Mark, vector<SharedSMTRef>>
getForbiddenPaths(MonoPair<PathMap> pathMaps,
                  MonoPair<BidirBlockMarkMap> marked, FreeVarsMap freeVarsMap,
                  string funName, bool main) {
    map<Mark, vector<SharedSMTRef>> pathExprs;
    for (const auto &pathMapIt : pathMaps.first) {
        const Mark startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt1 : pathMapIt.second) {
            const Mark endIndex1 = innerPathMapIt1.first;
            for (auto &innerPathMapIt2 : pathMaps.second.at(startIndex)) {
                const auto endIndex2 = innerPathMapIt2.first;
                if (endIndex1 != endIndex2) {
                    for (const auto &path1 : innerPathMapIt1.second) {
                        for (const auto &path2 : innerPathMapIt2.second) {
                            const auto endBlocks =
                                makeMonoPair(path1, path2)
                                    .map<llvm::BasicBlock *>(lastBlock);
                            const auto endIndices =
                                zipWith<BidirBlockMarkMap, llvm::BasicBlock *,
                                        set<Mark>>(
                                    marked, endBlocks,
                                    [](BidirBlockMarkMap marks,
                                       llvm::BasicBlock *endBlock)
                                        -> set<Mark> {
                                        return marks.BlockToMarksMap[endBlock];
                                    });
                            if (SMTGenerationOpts::getInstance().PerfectSync ==
                                    PerfectSynchronization::Enabled ||
                                ((startIndex != endIndex1 && // no circles
                                  startIndex != endIndex2) &&
                                 intersection(endIndices.first,
                                              endIndices.second)
                                     .empty())) {
                                const auto smt2 = assignmentsOnPath(
                                    path2, Program::Second,
                                    freeVarsMap.at(startIndex),
                                    endIndex2 == EXIT_MARK);
                                const auto smt1 = assignmentsOnPath(
                                    path1, Program::First,
                                    freeVarsMap.at(startIndex),
                                    endIndex1 == EXIT_MARK);
                                // We need to interleave here, because
                                // otherwise
                                // extern functions are not matched
                                const auto smt = interleaveAssignments(
                                    make_unique<ConstantBool>(false), smt1,
                                    smt2);
                                pathExprs[startIndex].push_back(smt);
                            }
                        }
                    }
                }
            }
        }
    }
    return pathExprs;
}

vector<SharedSMTRef>
functionalFunctionAssertions(const llvm::Function *f,
                             const AnalysisResultsMap &analysisResults,
                             Program prog) {
    const auto pathMap = analysisResults.at(f).paths;
    const auto funName = f->getName();
    const auto returnType = f->getReturnType();
    const auto funArgs = analysisResults.at(f).functionArguments;
    const auto freeVarsMap = analysisResults.at(f).freeVariables;
    return nonmutualPaths(pathMap, freeVarsMap, prog, funName, returnType,
                          getFunctionNumeralConstraints(f, prog));
}
vector<SharedSMTRef>
nonmutualPaths(PathMap pathMap, FreeVarsMap freeVarsMap, Program prog,
               string funName, const llvm::Type *returnType,
               vector<SharedSMTRef> functionNumeralConstraints) {
    map<MarkPair, vector<SharedSMTRef>> smtExprs;
    const int progIndex = programIndex(prog);
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const Mark endIndex = innerPathMapIt.first;
            for (const auto &path : innerPathMapIt.second) {
                SMTRef endInvariant1 =
                    invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                              freeVarsMap.at(endIndex), asSelection(prog),
                              funName, freeVarsMap);
                const auto defs =
                    assignmentsOnPath(path, prog, freeVarsMap.at(startIndex),
                                      endIndex == EXIT_MARK);
                auto clause = forallStartingAt(
                    nonmutualSMT(std::move(endInvariant1), defs, prog),
                    filterVars(progIndex, freeVarsMap.at(startIndex)),
                    startIndex, asSelection(prog), funName, false, freeVarsMap);
                smtExprs[{startIndex, endIndex}].push_back(clause);
            }
        }
    }

    return clauseMapToClauseVector(smtExprs, false, asSelection(prog),
                                   functionNumeralConstraints);
}

map<MarkPair, vector<SharedSMTRef>> getOffByNPaths(PathMap pathMap1,
                                                   PathMap pathMap2,
                                                   FreeVarsMap freeVarsMap,
                                                   string funName, bool main) {
    vector<SharedSMTRef> paths;
    const auto firstPaths = offByNPathsOneDir(pathMap1, pathMap2, freeVarsMap,
                                              Program::First, funName, main);
    const auto secondPaths = offByNPathsOneDir(pathMap2, pathMap1, freeVarsMap,
                                               Program::Second, funName, main);
    return mergeVectorMaps(firstPaths, secondPaths);
}

map<MarkPair, vector<SharedSMTRef>>
offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                  FreeVarsMap freeVarsMap, Program prog, string funName,
                  bool main) {
    const int progIndex = programIndex(prog);
    map<MarkPair, vector<SharedSMTRef>> clauses;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const Mark endIndex = innerPathMapIt.first;
            if (startIndex == endIndex) {
                // we found a loop
                for (const auto &path : innerPathMapIt.second) {
                    const auto endArgs2 = filterVars(
                        swapIndex(progIndex), freeVarsMap.at(startIndex));
                    const auto endArgs =
                        filterVars(progIndex, freeVarsMap.at(startIndex));
                    vector<SortedVar> args;
                    if (prog == Program::First) {
                        for (auto arg : endArgs) {
                            args.push_back(arg);
                        }
                        for (auto arg : endArgs2) {
                            args.push_back(SortedVar(arg.name + "_old",
                                                     std::move(arg.type)));
                        }

                    } else {
                        for (auto arg : endArgs2) {
                            args.push_back(SortedVar(arg.name + "_old",
                                                     std::move(arg.type)));
                        }
                        for (auto arg : endArgs) {
                            args.push_back(arg);
                        }
                    }
                    SMTRef endInvariant;
                    if (main) {
                        endInvariant = mainInvariant(startIndex, args, funName);
                    } else {
                        endInvariant = invariant(
                            startIndex, startIndex, freeVarsMap.at(startIndex),
                            args, ProgramSelection::Both, funName, freeVarsMap);
                    }
                    SharedSMTRef dontLoopInvariant = getDontLoopInvariant(
                        std::move(endInvariant), startIndex, otherPathMap,
                        freeVarsMap, swapProgram(prog));
                    const auto defs =
                        assignmentsOnPath(path, prog, freeVarsMap.at(endIndex),
                                          endIndex == EXIT_MARK);
                    clauses[{startIndex, startIndex}].push_back(
                        nonmutualSMT(dontLoopInvariant, defs, prog));
                }
            }
        }
    }
    return clauses;
}

/* --------------------------------------------------------------------------
 */
// Functions for generating SMT for a single/mutual path

vector<AssignmentCallBlock> assignmentsOnPath(const Path &path, Program prog,
                                              const vector<SortedVar> &freeVars,
                                              bool toEnd) {
    const int progIndex = programIndex(prog);
    const auto filteredFreeVars = filterVars(progIndex, freeVars);

    vector<AssignmentCallBlock> allDefs;
    set<string> constructed;
    vector<CallInfo> callInfos;

    // Set the new values to the initial values
    vector<DefOrCallInfo> oldDefs;
    for (const auto &var : filteredFreeVars) {
        oldDefs.push_back(DefOrCallInfo(make_unique<Assignment>(
            var.name,
            make_unique<TypedVariable>(var.name + "_old", var.type->copy()))));
    }
    allDefs.push_back(AssignmentCallBlock(std::move(oldDefs), nullptr));

    // First block of path, this is special, because we don’t have a
    // previous
    // block so we can’t resolve phi nodes
    allDefs.push_back(AssignmentCallBlock(
        blockAssignments(*path.Start, nullptr, false, prog), nullptr));

    auto prev = path.Start;

    // Rest of the path
    unsigned int i = 0;
    for (const auto &edge : path.Edges) {
        i++;
        const bool last = i == path.Edges.size();
        allDefs.push_back(AssignmentCallBlock(
            blockAssignments(*edge.Block, prev, last && !toEnd, prog),
            edge.Cond == nullptr ? nullptr : edge.Cond->toSmt()));
        prev = edge.Block;
    }
    return allDefs;
}

SharedSMTRef addAssignments(const SharedSMTRef end,
                            llvm::ArrayRef<AssignmentBlock> assignments) {
    SharedSMTRef clause = end;
    for (auto assgnIt = assignments.rbegin(); assgnIt != assignments.rend();
         ++assgnIt) {
        clause = fastNestLets(std::move(clause), assgnIt->definitions);
        if (assgnIt->condition) {
            clause = makeOp("=>", assgnIt->condition, std::move(clause));
        }
    }
    return clause;
}

SharedSMTRef interleaveAssignments(
    SharedSMTRef endClause,
    llvm::ArrayRef<AssignmentCallBlock> assignmentCallBlocks1,
    llvm::ArrayRef<AssignmentCallBlock> assignmentCallBlocks2) {
    SharedSMTRef clause = endClause;
    const auto splitAssignments1 =
        splitAssignmentsFromCalls(assignmentCallBlocks1);
    const auto splitAssignments2 =
        splitAssignmentsFromCalls(assignmentCallBlocks2);
    const auto &assignmentBlocks1 = splitAssignments1.assignments;
    const auto &assignmentBlocks2 = splitAssignments2.assignments;
    const auto &callInfo1 = splitAssignments1.callInfos;
    const auto &callInfo2 = splitAssignments2.callInfos;

    const auto interleaveSteps =
        matchFunCalls(callInfo1, callInfo2, coupledCalls);

    assert(assignmentBlocks1.size() == callInfo1.size() + 1);
    assert(assignmentBlocks2.size() == callInfo2.size() + 1);
    assert(assignmentCallBlocks1.size() >= 1);
    assert(assignmentCallBlocks2.size() >= 1);

    auto callIt1 = callInfo1.rbegin();
    auto callIt2 = callInfo2.rbegin();
    auto assignmentIt1 = assignmentBlocks1.rbegin();
    auto assignmentIt2 = assignmentBlocks2.rbegin();

    // We step through the matched calls in reverse to build up the smt from
    // the
    // bottom up
    for (InterleaveStep step : makeReverse(interleaveSteps)) {
        switch (step) {
        case InterleaveStep::StepFirst:
            clause = addAssignments(clause, *assignmentIt1);
            clause = nonMutualFunctionCall(clause, *callIt1, Program::First);
            ++callIt1;
            ++assignmentIt1;
            break;
        case InterleaveStep::StepSecond:
            clause = addAssignments(clause, *assignmentIt2);
            clause = nonMutualFunctionCall(clause, *callIt2, Program::Second);
            ++callIt2;
            ++assignmentIt2;
            break;
        case InterleaveStep::StepBoth:
            assert(coupledCalls(*callIt1, *callIt2));
            clause = addAssignments(clause, *assignmentIt2);
            clause = addAssignments(clause, *assignmentIt1);
            clause =
                mutualFunctionCall(clause, makeMonoPair(*callIt1, *callIt2));
            ++callIt1;
            ++callIt2;
            ++assignmentIt1;
            ++assignmentIt2;
            break;
        }
    }
    // There is always one more block than there are calls, so we have to
    // add it
    // separately at the end
    clause = addAssignments(clause, *assignmentIt2);
    clause = addAssignments(clause, *assignmentIt1);
    ++assignmentIt1;
    ++assignmentIt2;

    assert(callIt1 == callInfo1.rend());
    assert(callIt2 == callInfo2.rend());
    assert(assignmentIt1 == assignmentBlocks1.rend());
    assert(assignmentIt2 == assignmentBlocks2.rend());

    return clause;
}

SharedSMTRef
nonmutualSMT(SharedSMTRef endClause,
             llvm::ArrayRef<AssignmentCallBlock> assignmentCallBlocks,
             Program prog) {
    SharedSMTRef clause = endClause;
    const auto splitAssignments =
        splitAssignmentsFromCalls(assignmentCallBlocks);
    const auto assignmentBlocks = splitAssignments.assignments;
    const auto callInfos = splitAssignments.callInfos;
    assert(assignmentBlocks.size() == callInfos.size() + 1);
    bool first = true;
    auto callIt = callInfos.rbegin();
    for (auto assgnsVec : makeReverse(assignmentBlocks)) {
        if (first) {
            first = false;
        } else {
            clause = nonMutualFunctionCall(clause, *callIt, prog);
            ++callIt;
        }
        clause = addAssignments(clause, assgnsVec);
    }
    return clause;
}

SMTRef mutualFunctionCall(SharedSMTRef clause, MonoPair<CallInfo> callPair) {
    const uint32_t varArgs = callPair.first.varArgs;
    vector<SortedVar> args;
    args.push_back(SortedVar(callPair.first.assignedTo,
                             llvmType(callPair.first.fun.getReturnType())));
    args.push_back(SortedVar(callPair.second.assignedTo,
                             llvmType(callPair.second.fun.getReturnType())));
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        args.push_back(SortedVar("HEAP$1_res", memoryType()));
        args.push_back(SortedVar("HEAP$2_res", memoryType()));
    }
    vector<SharedSMTRef> implArgs;

    callPair.indexedForEach(addMemory(implArgs));
    vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(callPair.first.assignedTo));
    implArgs.push_back(stringExpr(callPair.second.assignedTo));
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        implArgs.push_back(memoryVariable("HEAP$1_res"));
        implArgs.push_back(memoryVariable("HEAP$2_res"));
    }
    SMTRef postInvariant = std::make_unique<Op>(
        invariantName(ENTRY_MARK, ProgramSelection::Both,
                      callPair.first.callName + "^" + callPair.second.callName,
                      InvariantAttr::NONE, varArgs),
        implArgs, !hasFixedAbstraction(callPair.first.fun));
    SMTRef result = makeOp("=>", std::move(postInvariant), clause);
    result = std::make_unique<Forall>(args, std::move(result));
    if (hasMutualFixedAbstraction(
            {&callPair.first.fun, &callPair.second.fun})) {
        return result;
    }
    SMTRef preInv = std::make_unique<Op>(
        invariantName(ENTRY_MARK, ProgramSelection::Both,
                      callPair.first.callName + "^" + callPair.second.callName,
                      InvariantAttr::PRE),
        preArgs);
    return makeOp("and", std::move(preInv), std::move(result));
}

SMTRef nonMutualFunctionCall(SharedSMTRef clause, CallInfo call, Program prog) {
    vector<SortedVar> forallArgs;
    vector<SharedSMTRef> implArgs;

    const int progIndex = programIndex(prog);
    const string programS = std::to_string(progIndex);

    const uint32_t varArgs = call.varArgs;
    // TODO figure out proper return type
    forallArgs.push_back(SortedVar(call.assignedTo, int64Type()));
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        forallArgs.push_back(
            SortedVar("HEAP$" + programS + "_res", memoryType()));
    }
    addMemory(implArgs)(call, progIndex);
    const vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(call.assignedTo));
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        implArgs.push_back(memoryVariable("HEAP$" + programS + "_res"));
    }

    const SharedSMTRef endInvariant = make_shared<Op>(
        invariantName(ENTRY_MARK, asSelection(prog), call.callName,
                      InvariantAttr::NONE, varArgs),
        implArgs, !hasFixedAbstraction(call.fun));
    SMTRef result = makeOp("=>", endInvariant, clause);
    result = std::make_unique<Forall>(forallArgs, std::move(result));
    if (hasFixedAbstraction(call.fun)) {
        return result;
    }
    const auto preInv =
        make_shared<Op>(invariantName(ENTRY_MARK, asSelection(prog),
                                      call.callName, InvariantAttr::PRE),
                        preArgs);
    return makeOp("and", preInv, std::move(result));
}

/// Wrap the clause in a forall
SharedSMTRef forallStartingAt(SharedSMTRef clause, vector<SortedVar> freeVars,
                              Mark blockIndex, ProgramSelection prog,
                              string funName, bool main,
                              FreeVarsMap freeVarsMap) {
    vector<SortedVar> vars;
    vector<SharedSMTRef> preVars;
    for (const auto &arg : freeVars) {
        std::smatch matchResult;
        vars.push_back(SortedVar(arg.name + "_old", arg.type->copy()));
        preVars.push_back(
            make_unique<TypedVariable>(arg.name + "_old", arg.type->copy()));
    }

    if (vars.empty()) {
        return clause;
    }

    if (main && blockIndex == ENTRY_MARK) {
        string opname =
            SMTGenerationOpts::getInstance().InitPredicate ? "INIT" : "IN_INV";

        vector<SharedSMTRef> args;
        for (const auto &arg : freeVars) {
            args.push_back(make_unique<TypedVariable>(arg.name + "_old",
                                                      arg.type->copy()));
        }

        clause = makeOp("=>", make_unique<Op>(opname, std::move(args)), clause);

    } else {
        InvariantAttr attr = main ? InvariantAttr::MAIN : InvariantAttr::PRE;
        SMTRef preInv = make_unique<Op>(
            invariantName(blockIndex, prog, funName, attr), preVars);
        clause = makeOp("=>", std::move(preInv), clause);
    }

    return std::make_unique<Forall>(vars, clause);
}

/* --------------------------------------------------------------------------
 */
// Functions forcing arguments to be equal

SharedSMTRef makeFunArgsEqual(SharedSMTRef clause, SharedSMTRef preClause,
                              vector<SortedVar> Args1,
                              vector<SortedVar> Args2) {
    assert(Args1.size() == Args2.size());

    vector<SharedSMTRef> args;
    for (const auto &arg : Args1) {
        args.push_back(typedVariableFromSortedVar(arg));
    }
    for (const auto &arg : Args2) {
        args.push_back(typedVariableFromSortedVar(arg));
    }

    auto inInv = make_unique<Op>("IN_INV", std::move(args));

    return makeOp("=>", std::move(inInv), makeOp("and", clause, preClause));
}

/// Create an assertion to require that if the recursive invariant holds and
/// the
/// arguments are equal the outputs are equal
SharedSMTRef equalInputsEqualOutputs(vector<SortedVar> funArgs,
                                     vector<SortedVar> funArgs1,
                                     vector<SortedVar> funArgs2, string funName,
                                     FreeVarsMap freeVarsMap,
                                     const llvm::Type *returnType) {
    vector<SortedVar> forallArgs;
    vector<SharedSMTRef> args;
    vector<SharedSMTRef> preInvArgs;
    for (const auto &arg : funArgs) {
        args.push_back(typedVariableFromSortedVar(arg));
    }
    preInvArgs = args;

    forallArgs.insert(forallArgs.end(), funArgs.begin(), funArgs.end());

    args.push_back(stringExpr("result$1"));
    args.push_back(stringExpr("result$2"));
    forallArgs.push_back(SortedVar("result$1", llvmType(returnType)));
    forallArgs.push_back(SortedVar("result$2", llvmType(returnType)));
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        forallArgs.push_back(SortedVar("HEAP$1_res", memoryType()));
        forallArgs.push_back(SortedVar("HEAP$2_res", memoryType()));
        args.push_back(memoryVariable("HEAP$1_res"));
        args.push_back(memoryVariable("HEAP$2_res"));
    }
    vector<SharedSMTRef> outArgs = {stringExpr("result$1"),
                                    stringExpr("result$2")};
    vector<string> sortedFunArgs1;
    vector<string> sortedFunArgs2;
    for (const auto &arg : funArgs1) {
        sortedFunArgs1.push_back(arg.name);
    }
    for (const auto &arg : funArgs2) {
        sortedFunArgs2.push_back(arg.name);
    }
    std::sort(sortedFunArgs1.begin(), sortedFunArgs1.end());
    std::sort(sortedFunArgs2.begin(), sortedFunArgs2.end());
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : funArgs1) {
            if (!isArray(*arg.type)) {
                outArgs.push_back(typedVariableFromSortedVar(arg));
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        outArgs.push_back(memoryVariable("HEAP$1_res"));
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : funArgs2) {
            if (!isArray(*arg.type)) {
                outArgs.push_back(typedVariableFromSortedVar(arg));
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        outArgs.push_back(memoryVariable("HEAP$2_res"));
    }
    const SharedSMTRef equalResults = makeOp(
        "=>",
        make_unique<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both, funName), args),
        make_unique<Op>("OUT_INV", outArgs));
    SMTRef preInv =
        make_unique<Op>(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                      funName, InvariantAttr::PRE),
                        preInvArgs);

    const auto equalArgs =
        makeFunArgsEqual(equalResults, std::move(preInv), funArgs1, funArgs2);
    const auto forallInputs = make_shared<Forall>(forallArgs, equalArgs);
    return make_shared<Assert>(forallInputs);
}

/// Swap the program index
int swapIndex(int I) {
    assert(I == 1 || I == 2);
    return I == 1 ? 2 : 1;
}

/// Split the assignment blocks on each call
SplitAssignments splitAssignmentsFromCalls(
    llvm::ArrayRef<AssignmentCallBlock> assignmentCallBlocks) {
    vector<vector<AssignmentBlock>> assignmentBlocks;
    vector<CallInfo> callInfos;
    vector<struct AssignmentBlock> currentAssignmentsList;
    for (auto &assignments : assignmentCallBlocks) {
        SharedSMTRef condition = assignments.condition;
        vector<Assignment> currentDefinitions;
        for (auto &defOrCall : assignments.definitions) {
            if (defOrCall.tag == DefOrCallInfoTag::Def) {
                currentDefinitions.emplace_back(
                    std::move(*defOrCall.definition));
            } else {
                currentAssignmentsList.emplace_back(
                    std::move(currentDefinitions), std::move(condition));
                currentDefinitions.clear();
                assignmentBlocks.emplace_back(
                    std::move(currentAssignmentsList));
                currentAssignmentsList.clear();
                condition = nullptr;
                callInfos.emplace_back(std::move(*defOrCall.callInfo));
            }
        }
        currentAssignmentsList.emplace_back(std::move(currentDefinitions),
                                            std::move(condition));
    }
    assignmentBlocks.emplace_back(std::move(currentAssignmentsList));
    return {std::move(assignmentBlocks), std::move(callInfos)};
}

/// Check if the marks match
void checkPathMaps(PathMap map1, PathMap map2) {
    if (!mapSubset(map1, map2) || !mapSubset(map2, map1)) {
        exit(1);
    }
}

bool mapSubset(PathMap map1, PathMap map2) {
    for (auto Pair : map1) {
        if (map2.find(Pair.first) == map2.end()) {
            logError("Mark '" + Pair.first.toString() +
                     "' doesn’t exist in both files\n");
            return false;
        }
    }
    return true;
}

SMTRef getDontLoopInvariant(SMTRef endClause, Mark startIndex, PathMap pathMap,
                            FreeVarsMap freeVars, Program prog) {
    SMTRef clause = std::move(endClause);
    vector<Path> dontLoopPaths;
    for (auto pathMapIt : pathMap.at(startIndex)) {
        if (pathMapIt.first == startIndex) {
            for (auto path : pathMapIt.second) {
                dontLoopPaths.push_back(path);
            }
        }
    }
    vector<SharedSMTRef> dontLoopExprs;
    for (auto path : dontLoopPaths) {
        auto defs =
            assignmentsOnPath(path, prog, freeVars.at(startIndex), false);
        auto smt = nonmutualSMT(make_unique<ConstantBool>(false), defs, prog);
        dontLoopExprs.push_back(smt);
    }
    if (!dontLoopExprs.empty()) {
        auto andExpr = make_shared<Op>("and", dontLoopExprs);
        clause = makeOp("=>", andExpr, std::move(clause));
    }
    return clause;
}

auto addMemory(vector<SharedSMTRef> &implArgs)
    -> function<void(CallInfo call, int index)> {
    return [&implArgs](CallInfo call, int index) {
        for (auto arg : call.args) {
            implArgs.push_back(arg);
        }
        if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
            implArgs.push_back(memoryVariable(heapName(index)));
        }
        if (SMTGenerationOpts::getInstance().Stack == StackOpt::Enabled) {
            implArgs.push_back(memoryVariable(stackPointerName(index)));
            implArgs.push_back(memoryVariable(stackName(index)));
        }
    };
}

void generateRelationalFunctionSMT(
    MonoPair<const llvm::Function *> preprocessedFunction,
    const AnalysisResultsMap &analysisResults, vector<SharedSMTRef> &assertions,
    vector<SharedSMTRef> &declarations) {
    auto newAssertions =
        relationalFunctionAssertions(preprocessedFunction, analysisResults);
    auto newDeclarations =
        relationalFunctionDeclarations(preprocessedFunction, analysisResults);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}
void generateFunctionalFunctionSMT(const llvm::Function *preprocessedFunction,
                                   const AnalysisResultsMap &analysisResults,
                                   Program prog,
                                   vector<SharedSMTRef> &assertions,
                                   vector<SharedSMTRef> &declarations) {
    auto newAssertions = functionalFunctionAssertions(preprocessedFunction,
                                                      analysisResults, prog);
    auto newDeclarations = functionalFunctionDeclarations(
        preprocessedFunction, analysisResults, prog);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}

void generateRelationalIterativeSMT(
    MonoPair<const llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults, vector<SharedSMTRef> &assertions,
    vector<SharedSMTRef> &declarations) {
    auto newAssertions =
        relationalIterativeAssertions(preprocessedFunctions, analysisResults);
    auto newDeclarations =
        relationalIterativeDeclarations(preprocessedFunctions, analysisResults);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}

vector<SharedSMTRef>
clauseMapToClauseVector(const map<MarkPair, vector<SharedSMTRef>> &clauseMap,
                        bool main, ProgramSelection programSelection,
                        vector<SharedSMTRef> functionNumeralConstraints) {
    if (SMTGenerationOpts::getInstance().Invert) {
        bool program1 = oneOf(programSelection, ProgramSelection::First,
                              ProgramSelection::Both);
        bool program2 = oneOf(programSelection, ProgramSelection::Second,
                              ProgramSelection::Both);
        vector<SharedSMTRef> clauses;
        for (const auto it : clauseMap) {
            vector<SharedSMTRef> clausesForMark;
            for (const auto &path : it.second) {
                clausesForMark.push_back(makeOp("not", path));
            }
            vector<SharedSMTRef> conjuncts = functionNumeralConstraints;
            conjuncts.push_back(
                makeOp("=", "INV_INDEX_START",
                       std::make_unique<ConstantInt>(llvm::APInt(
                           64, it.first.startMark.toString(), 10))));
            conjuncts.push_back(
                makeOp("=", "INV_INDEX_END",
                       std::make_unique<ConstantInt>(
                           llvm::APInt(64, it.first.endMark.toString(), 10))));
            conjuncts.push_back(
                makeOp("=", "MAIN", std::make_unique<ConstantBool>(main)));
            conjuncts.push_back(makeOp(
                "=", "PROGRAM_1", std::make_unique<ConstantBool>(program1)));
            conjuncts.push_back(makeOp(
                "=", "PROGRAM_2", std::make_unique<ConstantBool>(program2)));
            conjuncts.push_back(make_unique<Op>("or", clausesForMark));
            clauses.push_back(make_unique<Op>("and", conjuncts));
        }
        return clauses;
    } else {
        vector<SharedSMTRef> clauses;
        for (const auto it : clauseMap) {
            for (const auto &clause : it.second) {
                clauses.push_back(clause);
            }
        }
        return clauses;
    }
}

vector<SharedSMTRef> getFunctionNumeralConstraints(const llvm::Function *f,
                                                   Program prog) {
    string name = prog == Program::First ? "FUNCTION_1" : "FUNCTION_2";
    return {makeOp(
        "=", name,
        std::make_unique<ConstantInt>(llvm::APInt(
            64, SMTGenerationOpts::getInstance().FunctionNumerals.at(f))))};
}

vector<SharedSMTRef>
getFunctionNumeralConstraints(MonoPair<const llvm::Function *> functions) {
    return {makeOp("=", "FUNCTION_1",
                   std::make_unique<ConstantInt>(llvm::APInt(
                       64, SMTGenerationOpts::getInstance().FunctionNumerals.at(
                               functions.first)))),
            makeOp("=", "FUNCTION_2",
                   std::make_unique<ConstantInt>(llvm::APInt(
                       64, SMTGenerationOpts::getInstance().FunctionNumerals.at(
                               functions.second))))};
}
