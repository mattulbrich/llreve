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
using smt::Assert;
using smt::Assignment;
using smt::Comment;
using smt::Forall;
using smt::FunDef;
using smt::Op;
using smt::SMTExpr;
using smt::SMTRef;
using smt::SharedSMTRef;
using smt::SortedVar;
using smt::VarDecl;
using smt::makeOp;
using smt::stringExpr;
using std::function;
using std::make_pair;
using std::make_shared;
using std::map;
using std::set;
using std::string;
using std::string;
using std::unique_ptr;
using std::vector;

vector<SharedSMTRef>
relationalFunctionAssertions(MonoPair<PreprocessedFunction> preprocessedFuns) {
    const auto pathMaps = preprocessedFuns.map<PathMap>(
        [](PreprocessedFunction fun) { return fun.results.paths; });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = preprocessedFuns.map<BidirBlockMarkMap>(
        [](PreprocessedFunction fun) { return fun.results.blockMarkMap; });
    const string funName = preprocessedFuns.first.fun->getName().str() + "^" +
                           preprocessedFuns.second.fun->getName().str();
    const auto funArgsPair =
        functionArgs(*preprocessedFuns.first.fun, *preprocessedFuns.second.fun);
    const auto freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgsPair);
    vector<SharedSMTRef> smtExprs;
    vector<SharedSMTRef> pathExprs;

    const auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap,
        [&freeVarsMap, funName](int startIndex, int endIndex) {
            return invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                             freeVarsMap.at(endIndex), ProgramSelection::Both,
                             funName, freeVarsMap);
        });
    for (const auto &it : synchronizedPaths) {
        const SharedSMTRef endInvariant =
            invariant(it.first.startMark, it.first.endMark,
                      freeVarsMap.at(it.first.startMark),
                      freeVarsMap.at(it.first.endMark), ProgramSelection::Both,
                      funName, freeVarsMap);
        for (const auto &clause : it.second) {
            pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                clause, freeVarsMap.at(it.first.startMark), it.first.startMark,
                ProgramSelection::Both, funName, false, freeVarsMap)));
        }
    }

    const auto forbiddenPaths =
        getForbiddenPaths(pathMaps, marked, freeVarsMap, funName, false);
    pathExprs.insert(pathExprs.end(), forbiddenPaths.begin(),
                     forbiddenPaths.end());

    if (!SMTGenerationOpts::getInstance().PerfectSync) {
        const auto offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                                freeVarsMap, funName, false);
        for (const auto &it : offByNPaths) {
            for (const auto &clause : it.second) {
                pathExprs.push_back(make_shared<Assert>(
                    forallStartingAt(clause, freeVarsMap.at(it.first.startMark),
                                     it.first.startMark, ProgramSelection::Both,
                                     funName, false, freeVarsMap)));
            }
        }
    }

    smtExprs.insert(smtExprs.end(), pathExprs.begin(), pathExprs.end());

    return smtExprs;
}

// the main function that we want to check doesn’t need the output parameters in
// the assertions since it is never called
vector<SharedSMTRef>
relationalIterativeAssertions(MonoPair<PreprocessedFunction> preprocessedFuns) {
    const auto pathMaps = preprocessedFuns.map<PathMap>(
        [](PreprocessedFunction fun) { return fun.results.paths; });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = preprocessedFuns.map<BidirBlockMarkMap>(
        [](PreprocessedFunction fun) { return fun.results.blockMarkMap; });
    const string funName = preprocessedFuns.first.fun->getName().str() + "^" +
                           preprocessedFuns.second.fun->getName().str();
    const auto funArgsPair =
        functionArgs(*preprocessedFuns.first.fun, *preprocessedFuns.second.fun);
    const auto freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgsPair);
    vector<SharedSMTRef> smtExprs;

    const llvm::Type *returnType = preprocessedFuns.first.fun->getReturnType();
    if (SMTGenerationOpts::getInstance().OnlyRecursive) {
        smtExprs.push_back(
            equalInputsEqualOutputs(freeVarsMap.at(ENTRY_MARK),
                                    filterVars(1, freeVarsMap.at(ENTRY_MARK)),
                                    filterVars(2, freeVarsMap.at(ENTRY_MARK)),
                                    funName, freeVarsMap, returnType));
        return smtExprs;
    }

    auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap,
        [&freeVarsMap, funName](int startIndex, int endIndex) {
            SMTRef endInvariant =
                mainInvariant(endIndex, freeVarsMap.at(endIndex), funName);
            if (SMTGenerationOpts::getInstance().MuZ && endIndex == EXIT_MARK) {
                endInvariant =
                    makeOp("=>", makeOp("not", std::move(endInvariant)),
                           stringExpr("END_QUERY"));
            }
            return endInvariant;
        });

    const auto forbiddenPaths =
        getForbiddenPaths(pathMaps, marked, freeVarsMap, funName, true);
    if (!SMTGenerationOpts::getInstance().PerfectSync) {
        const auto offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                                freeVarsMap, funName, true);
        synchronizedPaths = mergeVectorMaps(synchronizedPaths, offByNPaths);
    }

    vector<SharedSMTRef> negations;
    for (const auto &it : synchronizedPaths) {
        for (auto &path : it.second) {
            auto clause = forallStartingAt(
                path, freeVarsMap.at(it.first.startMark), it.first.startMark,
                ProgramSelection::Both, funName, true, freeVarsMap);
            if (SMTGenerationOpts::getInstance().Invert) {
                negations.push_back(
                    makeOp("and", makeOp("=", "INV_INDEX",
                                         std::to_string(it.first.startMark)),
                           makeOp("not", clause)));
            } else {
                smtExprs.push_back(make_shared<Assert>(clause));
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Invert) {
        smtExprs.push_back(
            make_shared<Assert>(make_shared<Op>("or", negations)));
    }
    smtExprs.insert(smtExprs.end(), forbiddenPaths.begin(),
                    forbiddenPaths.end());
    return smtExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

map<MarkPair, vector<SharedSMTRef>>
getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                     smt::FreeVarsMap freeVarsMap,
                     ReturnInvariantGenerator generateReturnInvariant) {
    map<MarkPair, vector<SharedSMTRef>> clauses;
    for (const auto &pathMapIt : pathMap1) {
        const int startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            if (pathMap2.at(startIndex).find(endIndex) !=
                pathMap2.at(startIndex).end()) {
                const auto paths = pathMap2.at(startIndex).at(endIndex);
                for (const auto &path1 : innerPathMapIt.second) {
                    for (const auto &path2 : paths) {
                        auto defs =
                            makeMonoPair(make_pair(path1, Program::First),
                                         make_pair(path2, Program::Second))
                                .map<vector<AssignmentCallBlock>>(
                                    [=](std::pair<Path, Program> pair) {
                                        return assignmentsOnPath(
                                            pair.first, pair.second,
                                            freeVarsMap.at(startIndex),
                                            endIndex == EXIT_MARK);
                                    });
                        clauses[{startIndex, endIndex}].push_back(
                            interleaveAssignments(
                                generateReturnInvariant(startIndex, endIndex),
                                defs));
                    }
                }
            }
        }
    }

    return clauses;
}

vector<SharedSMTRef> getForbiddenPaths(MonoPair<PathMap> pathMaps,
                                       MonoPair<BidirBlockMarkMap> marked,
                                       smt::FreeVarsMap freeVarsMap,
                                       string funName, bool main) {
    vector<SharedSMTRef> pathExprs;
    for (const auto &pathMapIt : pathMaps.first) {
        const int startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt1 : pathMapIt.second) {
            const int endIndex1 = innerPathMapIt1.first;
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
                                        set<int>>(
                                    marked, endBlocks,
                                    [](BidirBlockMarkMap marks,
                                       llvm::BasicBlock *endBlock) -> set<int> {
                                        return marks.BlockToMarksMap[endBlock];
                                    });
                            if (SMTGenerationOpts::getInstance().PerfectSync ||
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
                                // We need to interleave here, because otherwise
                                // extern functions are not matched
                                const auto smt = interleaveAssignments(
                                    stringExpr("false"),
                                    makeMonoPair(smt1, smt2));
                                pathExprs.push_back(
                                    make_shared<Assert>(forallStartingAt(
                                        smt, freeVarsMap.at(startIndex),
                                        startIndex, ProgramSelection::Both,
                                        funName, main, freeVarsMap)));
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
functionalFunctionAssertions(PreprocessedFunction preprocessedFun,
                             Program prog) {
    const auto pathMap = preprocessedFun.results.paths;
    const auto funName = preprocessedFun.fun->getName();
    const auto returnType = preprocessedFun.fun->getReturnType();
    const auto funArgs = functionArgs(*preprocessedFun.fun);
    const auto freeVarsMap = freeVars(pathMap, funArgs, prog);
    return nonmutualPaths(pathMap, freeVarsMap, prog, funName, returnType);
}
vector<SharedSMTRef> nonmutualPaths(PathMap pathMap,
                                    smt::FreeVarsMap freeVarsMap, Program prog,
                                    string funName,
                                    const llvm::Type *returnType) {
    vector<SharedSMTRef> smtExprs;
    const int progIndex = programIndex(prog);
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            for (const auto &path : innerPathMapIt.second) {
                SMTRef endInvariant1 =
                    invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                              freeVarsMap.at(endIndex), asSelection(prog),
                              funName, freeVarsMap);
                const auto defs =
                    assignmentsOnPath(path, prog, freeVarsMap.at(startIndex),
                                      endIndex == EXIT_MARK);
                smtExprs.push_back(make_shared<Assert>(forallStartingAt(
                    nonmutualSMT(std::move(endInvariant1), defs, prog),
                    filterVars(progIndex, freeVarsMap.at(startIndex)),
                    startIndex, asSelection(prog), funName, false,
                    freeVarsMap)));
            }
        }
    }
    return smtExprs;
}

map<MarkPair, vector<SharedSMTRef>> getOffByNPaths(PathMap pathMap1,
                                                   PathMap pathMap2,
                                                   smt::FreeVarsMap freeVarsMap,
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
                  smt::FreeVarsMap freeVarsMap, Program prog, string funName,
                  bool main) {
    const int progIndex = programIndex(prog);
    map<MarkPair, vector<SharedSMTRef>> clauses;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            if (startIndex == endIndex) {
                // we found a loop
                for (const auto &path : innerPathMapIt.second) {
                    const auto endArgs2 = filterVars(
                        swapIndex(progIndex), freeVarsMap.at(startIndex));
                    const auto endArgs =
                        filterVars(progIndex, freeVarsMap.at(startIndex));
                    vector<smt::SortedVar> args;
                    if (prog == Program::First) {
                        for (auto arg : endArgs) {
                            args.push_back(arg);
                        }
                        for (auto arg : endArgs2) {
                            args.push_back(
                                SortedVar(arg.name + "_old", arg.type));
                        }

                    } else {
                        for (auto arg : endArgs2) {
                            args.push_back(
                                SortedVar(arg.name + "_old", arg.type));
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

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

vector<AssignmentCallBlock> assignmentsOnPath(Path path, Program prog,
                                              vector<smt::SortedVar> freeVars,
                                              bool toEnd) {
    const int progIndex = programIndex(prog);
    const auto filteredFreeVars = filterVars(progIndex, freeVars);

    vector<AssignmentCallBlock> allDefs;
    set<string> constructed;
    vector<CallInfo> callInfos;

    // Set the new values to the initial values
    vector<DefOrCallInfo> oldDefs;
    for (auto var : filteredFreeVars) {
        oldDefs.push_back(DefOrCallInfo(
            make_shared<Assignment>(var.name, stringExpr(var.name + "_old"))));
    }
    allDefs.push_back(AssignmentCallBlock(oldDefs, nullptr));

    // First block of path, this is special, because we don’t have a
    // previous
    // block so we can’t resolve phi nodes
    const auto startDefs = blockAssignments(*path.Start, nullptr, false, prog);
    allDefs.push_back(AssignmentCallBlock(startDefs, nullptr));

    auto prev = path.Start;

    // Rest of the path
    unsigned int i = 0;
    for (auto edge : path.Edges) {
        i++;
        const bool last = i == path.Edges.size();
        const auto defs =
            blockAssignments(*edge.Block, prev, last && !toEnd, prog);
        allDefs.push_back(AssignmentCallBlock(
            defs, edge.Cond == nullptr ? nullptr : edge.Cond->toSmt()));
        prev = edge.Block;
    }
    return allDefs;
}

SharedSMTRef addAssignments(const SharedSMTRef end,
                            vector<AssignmentBlock> assignments) {
    SharedSMTRef clause = end;
    for (auto assgns : makeReverse(assignments)) {
        clause = nestLets(clause, assgns.definitions);
        if (assgns.condition) {
            clause = makeOp("=>", assgns.condition, clause);
        }
    }
    return clause;
}

SharedSMTRef interleaveAssignments(
    SharedSMTRef endClause,
    MonoPair<vector<AssignmentCallBlock>> AssignmentCallBlocks) {
    SharedSMTRef clause = endClause;
    const auto splitAssignments =
        AssignmentCallBlocks.map<SplitAssignments>(splitAssignmentsFromCalls);
    const auto assignmentBlocks1 = splitAssignments.first.assignments;
    const auto assignmentBlocks2 = splitAssignments.second.assignments;
    const auto callInfo1 = splitAssignments.first.callInfos;
    const auto callInfo2 = splitAssignments.second.callInfos;

    const auto interleaveSteps = matchFunCalls(callInfo1, callInfo2);

    assert(assignmentBlocks1.size() == callInfo1.size() + 1);
    assert(assignmentBlocks2.size() == callInfo2.size() + 1);
    assert(AssignmentCallBlocks.first.size() >= 1);
    assert(AssignmentCallBlocks.second.size() >= 1);

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

SharedSMTRef nonmutualSMT(SharedSMTRef endClause,
                          vector<AssignmentCallBlock> assignmentCallBlocks,
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
    args.push_back(
        SortedVar(callPair.first.assignedTo,
                  llvmTypeToSMTSort(callPair.first.fun.getReturnType())));
    args.push_back(
        SortedVar(callPair.second.assignedTo,
                  llvmTypeToSMTSort(callPair.second.fun.getReturnType())));
    if (SMTGenerationOpts::getInstance().Heap) {
        args.push_back(SortedVar("HEAP$1_res", arrayType()));
        args.push_back(SortedVar("HEAP$2_res", arrayType()));
    }
    vector<SharedSMTRef> implArgs;

    callPair.indexedForEach(addMemory(implArgs));
    vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(callPair.first.assignedTo));
    implArgs.push_back(stringExpr(callPair.second.assignedTo));
    if (SMTGenerationOpts::getInstance().Heap) {
        implArgs.push_back(stringExpr("HEAP$1_res"));
        implArgs.push_back(stringExpr("HEAP$2_res"));
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
    forallArgs.push_back(SortedVar(call.assignedTo, "Int"));
    if (SMTGenerationOpts::getInstance().Heap) {
        forallArgs.push_back(
            SortedVar("HEAP$" + programS + "_res", arrayType()));
    }
    addMemory(implArgs)(call, progIndex);
    const vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(call.assignedTo));
    if (SMTGenerationOpts::getInstance().Heap) {
        implArgs.push_back(stringExpr("HEAP$" + programS + "_res"));
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
                              int blockIndex, ProgramSelection prog,
                              string funName, bool main,
                              smt::FreeVarsMap freeVarsMap) {
    vector<SortedVar> vars;
    vector<string> preVars;
    for (const auto &arg : freeVars) {
        std::smatch matchResult;
        vars.push_back(toSMTSortedVar(SortedVar(arg.name + "_old", arg.type)));
        preVars.push_back(arg.name + "_old");
    }

    if (vars.empty()) {
        return clause;
    }

    if (main && blockIndex == ENTRY_MARK) {
        string opname =
            SMTGenerationOpts::getInstance().InitPredicate ? "INIT" : "IN_INV";

        vector<string> args;
        for (const auto &arg : freeVars) {
            args.push_back(arg.name + "_old");
        }

        clause = makeOp("=>", makeOp(opname, args), clause);

    } else {
        InvariantAttr attr = main ? InvariantAttr::MAIN : InvariantAttr::PRE;
        SMTRef preInv =
            makeOp(invariantName(blockIndex, prog, funName, attr), preVars);
        clause = makeOp("=>", std::move(preInv), clause);
    }

    return std::make_unique<Forall>(vars, clause);
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SharedSMTRef makeFunArgsEqual(SharedSMTRef clause, SharedSMTRef preClause,
                              vector<smt::SortedVar> Args1,
                              vector<smt::SortedVar> Args2) {
    assert(Args1.size() == Args2.size());

    vector<string> args;
    for (const auto &arg : Args1) {
        args.push_back(arg.name);
    }
    for (const auto &arg : Args2) {
        args.push_back(arg.name);
    }

    auto inInv = makeOp("IN_INV", args);

    return makeOp("=>", std::move(inInv), makeOp("and", clause, preClause));
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SharedSMTRef equalInputsEqualOutputs(vector<smt::SortedVar> funArgs,
                                     vector<smt::SortedVar> funArgs1,
                                     vector<smt::SortedVar> funArgs2,
                                     string funName,
                                     smt::FreeVarsMap freeVarsMap,
                                     const llvm::Type *returnType) {
    vector<SortedVar> forallArgs;
    vector<string> args;
    vector<string> preInvArgs;
    for (const auto &arg : funArgs) {
        args.push_back(arg.name);
    }
    preInvArgs = args;

    forallArgs.insert(forallArgs.end(), funArgs.begin(), funArgs.end());

    args.push_back("result$1");
    args.push_back("result$2");
    forallArgs.push_back(SortedVar("result$1", llvmTypeToSMTSort(returnType)));
    forallArgs.push_back(SortedVar("result$2", llvmTypeToSMTSort(returnType)));
    if (SMTGenerationOpts::getInstance().Heap) {
        forallArgs.push_back(SortedVar("HEAP$1_res", arrayType()));
        forallArgs.push_back(SortedVar("HEAP$2_res", arrayType()));
        args.push_back("HEAP$1_res");
        args.push_back("HEAP$2_res");
    }
    vector<string> outArgs = {"result$1", "result$2"};
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
            if (!std::regex_match(arg.name, HEAP_REGEX)) {
                outArgs.push_back(arg.name);
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        outArgs.push_back("HEAP$1_res");
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : funArgs2) {
            if (!std::regex_match(arg.name, HEAP_REGEX)) {
                outArgs.push_back(arg.name);
            }
        }
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        outArgs.push_back("HEAP$2_res");
    }
    const SharedSMTRef equalResults = makeOp(
        "=>", makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both, funName),
                     args),
        makeOp("OUT_INV", outArgs));
    SMTRef preInv = makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both,
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
SplitAssignments
splitAssignmentsFromCalls(vector<AssignmentCallBlock> assignmentCallBlocks) {
    vector<vector<AssignmentBlock>> assignmentBlocks;
    vector<CallInfo> callInfos;
    vector<struct AssignmentBlock> currentAssignmentsList;
    for (auto assignments : assignmentCallBlocks) {
        SharedSMTRef condition = assignments.condition;
        vector<Assignment> currentDefinitions;
        for (auto defOrCall : assignments.definitions) {
            if (defOrCall.tag == DefOrCallInfoTag::Def) {
                currentDefinitions.push_back(*defOrCall.definition);
            } else {
                currentAssignmentsList.push_back(
                    AssignmentBlock(currentDefinitions, condition));
                currentDefinitions.clear();
                assignmentBlocks.push_back(currentAssignmentsList);
                currentAssignmentsList.clear();
                condition = nullptr;
                callInfos.push_back(*defOrCall.callInfo);
            }
        }
        currentAssignmentsList.push_back(
            AssignmentBlock(currentDefinitions, condition));
    }
    assignmentBlocks.push_back(currentAssignmentsList);
    return {assignmentBlocks, callInfos};
}

vector<InterleaveStep> matchFunCalls(vector<CallInfo> callInfos1,
                                     vector<CallInfo> callInfos2) {
    // This is just a basic edit distance algorithm
    vector<vector<size_t>> table(callInfos1.size() + 1,
                                 vector<size_t>(callInfos2.size() + 1, 0));
    for (uint32_t i = 0; i <= callInfos1.size(); ++i) {
        table[i][0] = i;
    }
    for (uint32_t j = 0; j <= callInfos2.size(); ++j) {
        table[0][j] = j;
    }
    for (uint32_t i = 1; i <= callInfos1.size(); ++i) {
        for (uint32_t j = 1; j <= callInfos2.size(); ++j) {
            if (coupledCalls(callInfos1[i - 1], callInfos2[j - 1])) {
                table[i][j] = table[i - 1][j - 1];
            } else {
                table[i][j] =
                    std::min(table[i - 1][j] + 1, table[i][j - 1] + 1);
            }
        }
    }
    vector<InterleaveStep> interleaveSteps;
    uint64_t i = callInfos1.size(), j = callInfos2.size();
    while (i > 0 && j > 0) {
        if (coupledCalls(callInfos1[i - 1], callInfos2[j - 1])) {
            interleaveSteps.push_back(InterleaveStep::StepBoth);
            --i;
            --j;
        } else {
            if (table[i - 1][j] <= table[i][j - 1]) {
                interleaveSteps.push_back(InterleaveStep::StepFirst);
                --i;
            } else {
                interleaveSteps.push_back(InterleaveStep::StepSecond);
                --j;
            }
        }
    }
    while (i > 0) {
        interleaveSteps.push_back(InterleaveStep::StepFirst);
        --i;
    }
    while (j > 0) {
        interleaveSteps.push_back(InterleaveStep::StepSecond);
        --j;
    }
    std::reverse(interleaveSteps.begin(), interleaveSteps.end());
    return interleaveSteps;
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
            logError("Mark '" + std::to_string(Pair.first) +
                     "' doesn’t exist in both files\n");
            return false;
        }
    }
    return true;
}

SMTRef getDontLoopInvariant(SMTRef endClause, int startIndex, PathMap pathMap,
                            smt::FreeVarsMap freeVars, Program prog) {
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
        auto smt = nonmutualSMT(stringExpr("false"), defs, prog);
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
        if (SMTGenerationOpts::getInstance().Heap) {
            implArgs.push_back(stringExpr(heapName(index)));
        }
        if (SMTGenerationOpts::getInstance().Stack) {
            implArgs.push_back(stringExpr(stackPointerName(index)));
            implArgs.push_back(stringExpr(stackName(index)));
        }
    };
}

void generateRelationalFunctionSMT(
    MonoPair<PreprocessedFunction> preprocessedFunction,
    vector<SharedSMTRef> &assertions, vector<SharedSMTRef> &declarations) {
    auto newAssertions = relationalFunctionAssertions(preprocessedFunction);
    auto newDeclarations = relationalFunctionDeclarations(preprocessedFunction);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}
void generateFunctionalFunctionSMT(PreprocessedFunction preprocessedFunction,
                                   Program prog,
                                   vector<SharedSMTRef> &assertions,
                                   vector<SharedSMTRef> &declarations) {
    auto newAssertions =
        functionalFunctionAssertions(preprocessedFunction, prog);
    auto newDeclarations =
        functionalFunctionDeclarations(preprocessedFunction, prog);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}

void generateRelationalIterativeSMT(
    MonoPair<PreprocessedFunction> preprocessedFunctions,
    vector<SharedSMTRef> &assertions, vector<SharedSMTRef> &declarations) {
    auto newAssertions = relationalIterativeAssertions(preprocessedFunctions);
    auto newDeclarations =
        relationalIterativeDeclarations(preprocessedFunctions);
    assertions.insert(assertions.end(), newAssertions.begin(),
                      newAssertions.end());
    declarations.insert(declarations.end(), newDeclarations.begin(),
                        newDeclarations.end());
}
