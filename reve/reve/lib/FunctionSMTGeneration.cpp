#include "FunctionSMTGeneration.h"

#include "Compat.h"
#include "Invariant.h"
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
using smt::makeBinOp;
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
functionAssertion(MonoPair<PreprocessedFunction> preprocessedFuns,
                  vector<SharedSMTRef> &declarations, Memory memory) {
    const MonoPair<PathMap> pathMaps =
        preprocessedFuns.map<PathMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<PathAnalysis>(*pair.fun);
        });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const MonoPair<BidirBlockMarkMap> marked =
        preprocessedFuns.map<BidirBlockMarkMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<MarkAnalysis>(*pair.fun);
        });
    const string funName = preprocessedFuns.first.fun->getName();
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*preprocessedFuns.first.fun, *preprocessedFuns.second.fun);
    // TODO this should use concat
    const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) -> vector<string> {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });
    const FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, memory);
    vector<SharedSMTRef> smtExprs;
    vector<SharedSMTRef> pathExprs;

    const auto addInvariant = [&](SMTRef invariant) {
        declarations.push_back(std::move(invariant));

    };
    if (!SMTGenerationOpts::getInstance().SingleInvariant) {
        MonoPair<SMTRef> invariants =
            invariantDeclaration(ENTRY_MARK, freeVarsMap.at(ENTRY_MARK),
                                 ProgramSelection::Both, funName, memory);
        MonoPair<SMTRef> invariants1 = invariantDeclaration(
            ENTRY_MARK, filterVars(1, freeVarsMap.at(ENTRY_MARK)),
            ProgramSelection::First, funName, memory);
        MonoPair<SMTRef> invariants2 = invariantDeclaration(
            ENTRY_MARK, filterVars(2, freeVarsMap.at(ENTRY_MARK)),
            ProgramSelection::Second, funName, memory);
        std::move(invariants).forEach(addInvariant);
        std::move(invariants1).forEach(addInvariant);
        std::move(invariants2).forEach(addInvariant);
    } else {
        MonoPair<SMTRef> invariants = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::Both, funName);
        MonoPair<SMTRef> invariants1 = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::First, funName);
        MonoPair<SMTRef> invariants2 = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::Second, funName);
        std::move(invariants).forEach(addInvariant);
        std::move(invariants1).forEach(addInvariant);
        std::move(invariants2).forEach(addInvariant);
    }

    const map<int, map<int, vector<std::function<SharedSMTRef(SharedSMTRef)>>>>
        synchronizedPaths = getSynchronizedPaths(
            pathMaps.first, pathMaps.second, freeVarsMap, memory);
    const vector<SharedSMTRef> recDecls =
        recDeclarations(pathMaps.first, funName, freeVarsMap, memory);
    declarations.insert(declarations.end(), recDecls.begin(), recDecls.end());
    for (const auto &it : synchronizedPaths) {
        const int startIndex = it.first;
        for (const auto &it2 : it.second) {
            const int endIndex = it2.first;
            const SharedSMTRef endInvariant =
                invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                          freeVarsMap.at(endIndex), ProgramSelection::Both,
                          funName, memory, freeVarsMap);
            for (const auto &pathFun : it2.second) {
                pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                    pathFun(endInvariant), freeVarsMap.at(startIndex),
                    startIndex, ProgramSelection::Both, funName, false,
                    freeVarsMap, memory)));
            }
        }
    }
    // these are needed for calls that can’t be matched with the same call in
    // the other program
    nonmutualPaths(pathMaps.first, pathExprs, freeVarsMap, Program::First,
                   funName, declarations, memory);
    nonmutualPaths(pathMaps.second, pathExprs, freeVarsMap, Program::Second,
                   funName, declarations, memory);

    const vector<SharedSMTRef> forbiddenPaths = getForbiddenPaths(
        pathMaps, marked, freeVarsMap, funName, false, memory);
    pathExprs.insert(pathExprs.end(), forbiddenPaths.begin(),
                     forbiddenPaths.end());

    if (!SMTGenerationOpts::getInstance().PerfectSync) {
        const map<int,
                  map<int, vector<std::function<SharedSMTRef(SharedSMTRef)>>>>
            offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                         freeVarsMap, funName, false, memory);
        for (const auto &it : offByNPaths) {
            const int startIndex = it.first;
            for (const auto &it2 : it.second) {
                for (const auto &pathFun : it2.second) {
                    pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                        pathFun(nullptr), freeVarsMap.at(startIndex),
                        startIndex, ProgramSelection::Both, funName, false,
                        freeVarsMap, memory)));
                }
            }
        }
    }

    smtExprs.insert(smtExprs.end(), pathExprs.begin(), pathExprs.end());

    return smtExprs;
}

// the main function that we want to check doesn’t need the output parameters in
// the assertions since it is never called
vector<SharedSMTRef>
mainAssertion(MonoPair<PreprocessedFunction> preprocessedFuns,
              vector<SharedSMTRef> &declarations, bool onlyRec, Memory memory) {
    const MonoPair<PathMap> pathMaps =
        preprocessedFuns.map<PathMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<PathAnalysis>(*pair.fun);
        });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const MonoPair<BidirBlockMarkMap> marked =
        preprocessedFuns.map<BidirBlockMarkMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<MarkAnalysis>(*pair.fun);
        });
    const string funName = preprocessedFuns.first.fun->getName();
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*preprocessedFuns.first.fun, *preprocessedFuns.second.fun);
    // TODO this should use concat
    const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });

    const FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, memory);
    if (SMTGenerationOpts::getInstance().MuZ) {
        const vector<SharedSMTRef> variables = declareVariables(freeVarsMap);
        declarations.insert(declarations.end(), variables.begin(),
                            variables.end());
    }
    vector<SharedSMTRef> smtExprs;

    if (onlyRec) {
        smtExprs.push_back(
            equalInputsEqualOutputs(freeVarsMap.at(ENTRY_MARK),
                                    filterVars(1, freeVarsMap.at(ENTRY_MARK)),
                                    filterVars(2, freeVarsMap.at(ENTRY_MARK)),
                                    funName, freeVarsMap, memory));
        return smtExprs;
    }

    if (SMTGenerationOpts::getInstance().SingleInvariant) {
        declarations.push_back(
            singleMainInvariant(freeVarsMap, memory, ProgramSelection::Both));
    }

    map<int, map<int, vector<std::function<SharedSMTRef(SharedSMTRef)>>>>
        synchronizedPaths = getSynchronizedPaths(
            pathMaps.first, pathMaps.second, freeVarsMap, memory);
    const vector<SharedSMTRef> mainDecls =
        mainDeclarations(pathMaps.first, funName, freeVarsMap);
    declarations.insert(declarations.end(), mainDecls.begin(), mainDecls.end());
    const vector<SharedSMTRef> forbiddenPaths =
        getForbiddenPaths(pathMaps, marked, freeVarsMap, funName, true, memory);
    if (!SMTGenerationOpts::getInstance().PerfectSync) {
        const map<int,
                  map<int, vector<std::function<SharedSMTRef(SharedSMTRef)>>>>
            offByNPaths = getOffByNPaths(pathMaps.first, pathMaps.second,
                                         freeVarsMap, funName, true, memory);
        synchronizedPaths = mergePathFuns(synchronizedPaths, offByNPaths);
    }
    auto transposedPaths = transpose(synchronizedPaths);
    // remove cycles
    for (auto &it : transposedPaths) {
        it.second.erase(it.first);
    }
    for (const auto &it : synchronizedPaths) {
        const int startIndex = it.first;
        vector<SharedSMTRef> pathsStartingHere;
        for (auto it2 : it.second) {
            const int endIndex = it2.first;
            SharedSMTRef endInvariant =
                mainInvariant(endIndex, freeVarsMap.at(endIndex), funName);
            if (SMTGenerationOpts::getInstance().MuZ && endIndex == EXIT_MARK) {
                endInvariant =
                    makeBinOp("=>", makeUnaryOp("not", std::move(endInvariant)),
                              stringExpr("END_QUERY"));
            }
            for (auto pathFun : it2.second) {
                pathsStartingHere.push_back(pathFun(endInvariant));
            }
        }
        if (!SMTGenerationOpts::getInstance().Nest) {
            for (auto path : pathsStartingHere) {
                auto clause = forallStartingAt(
                    path, freeVarsMap.at(startIndex), startIndex,
                    ProgramSelection::Both, funName, true, freeVarsMap, memory);
                smtExprs.push_back(make_shared<Assert>(clause));
            }
        } else {
            auto clause = forallStartingAt(
                make_shared<Op>("and", pathsStartingHere),
                freeVarsMap.at(startIndex), startIndex, ProgramSelection::Both,
                funName, true, freeVarsMap, memory);
            if ((transposedPaths.find(startIndex) != transposedPaths.end())) {
                if (transposedPaths.at(startIndex).size() == 1) {
                    auto it = transposedPaths.at(startIndex).begin();
                    const int comingFrom = it->first;
                    if (it->second.size() == 1) {
                        const auto nestFun = it->second.at(0);
                        clause = forallStartingAt(
                            nestFun(clause), freeVarsMap.at(comingFrom),
                            comingFrom, ProgramSelection::Both, funName, true,
                            freeVarsMap, memory);
                    }
                }
            }
            smtExprs.push_back(make_shared<Assert>(clause));
        }
    }
    smtExprs.insert(smtExprs.end(), forbiddenPaths.begin(),
                    forbiddenPaths.end());
    return smtExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>>
getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                     FreeVarsMap freeVarsMap, Memory memory) {
    map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>> pathFuns;
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
                                            endIndex == EXIT_MARK, memory);
                                    });
                        pathFuns[startIndex][endIndex].push_back(
                            [=](SharedSMTRef end) {
                                return interleaveAssignments(end, defs, memory);
                            });
                    }
                }
            }
        }
    }

    return pathFuns;
}

vector<SharedSMTRef> mainDeclarations(PathMap pathMap, string funName,
                                      FreeVarsMap freeVarsMap) {
    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK &&
            !SMTGenerationOpts::getInstance().SingleInvariant) {
            // ignore entry node
            const auto invariant =
                mainInvariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                         ProgramSelection::Both, funName);
            declarations.push_back(invariant);
        }
    }
    return declarations;
}

vector<SharedSMTRef> recDeclarations(PathMap pathMap, string funName,
                                     FreeVarsMap freeVarsMap, Memory memory) {
    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK &&
            !SMTGenerationOpts::getInstance().SingleInvariant) {
            // ignore entry node
            MonoPair<SharedSMTRef> invariants =
                invariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                     ProgramSelection::Both, funName, memory);
            declarations.push_back(invariants.first);
            declarations.push_back(invariants.second);
        }
    }
    return declarations;
}

vector<SharedSMTRef> getForbiddenPaths(MonoPair<PathMap> pathMaps,
                                       MonoPair<BidirBlockMarkMap> marked,
                                       FreeVarsMap freeVarsMap, string funName,
                                       bool main, Memory memory) {
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
                                    endIndex2 == EXIT_MARK, memory);
                                const auto smt1 = assignmentsOnPath(
                                    path1, Program::First,
                                    freeVarsMap.at(startIndex),
                                    endIndex1 == EXIT_MARK, memory);
                                // We need to interleave here, because otherwise
                                // extern functions are not matched
                                const auto smt = interleaveAssignments(
                                    stringExpr("false"),
                                    makeMonoPair(smt1, smt2), memory);
                                pathExprs.push_back(
                                    make_shared<Assert>(forallStartingAt(
                                        smt, freeVarsMap.at(startIndex),
                                        startIndex, ProgramSelection::Both,
                                        funName, main, freeVarsMap, memory)));
                            }
                        }
                    }
                }
            }
        }
    }
    return pathExprs;
}

void nonmutualPaths(PathMap pathMap, vector<SharedSMTRef> &pathExprs,
                    FreeVarsMap freeVarsMap, Program prog, string funName,
                    vector<SharedSMTRef> &declarations, Memory memory) {
    const int progIndex = programIndex(prog);
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK &&
            !SMTGenerationOpts::getInstance().SingleInvariant) {
            MonoPair<SMTRef> invariants = invariantDeclaration(
                startIndex, filterVars(progIndex, freeVarsMap.at(startIndex)),
                asSelection(prog), funName, memory);
            std::move(invariants).forEach([&declarations](SMTRef inv) {
                declarations.push_back(std::move(inv));
            });
        }
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            for (const auto &path : innerPathMapIt.second) {
                SMTRef endInvariant1 =
                    invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                              freeVarsMap.at(endIndex), asSelection(prog),
                              funName, memory, freeVarsMap);
                const auto defs =
                    assignmentsOnPath(path, prog, freeVarsMap.at(startIndex),
                                      endIndex == EXIT_MARK, memory);
                pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                    nonmutualSMT(std::move(endInvariant1), defs, prog, memory),
                    filterVars(progIndex, freeVarsMap.at(startIndex)),
                    startIndex, asSelection(prog), funName, false, freeVarsMap,
                    memory)));
            }
        }
    }
}

map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>>
getOffByNPaths(PathMap pathMap1, PathMap pathMap2, FreeVarsMap freeVarsMap,
               string funName, bool main, Memory memory) {
    map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>> pathFuns;
    vector<SharedSMTRef> paths;
    const auto firstPaths = offByNPathsOneDir(
        pathMap1, pathMap2, freeVarsMap, Program::First, funName, main, memory);
    const auto secondPaths =
        offByNPathsOneDir(pathMap2, pathMap1, freeVarsMap, Program::Second,
                          funName, main, memory);
    return mergePathFuns(firstPaths, secondPaths);
}

map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>>
offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                  FreeVarsMap freeVarsMap, Program prog, string funName,
                  bool main, Memory memory) {
    const int progIndex = programIndex(prog);
    map<int, map<int, vector<function<SharedSMTRef(SharedSMTRef)>>>> pathFuns;
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
                    vector<string> args;
                    if (prog == Program::First) {
                        for (auto arg : endArgs) {
                            args.push_back(arg);
                        }
                        for (auto arg : endArgs2) {
                            args.push_back(arg + "_old");
                        }

                    } else {
                        for (auto arg : endArgs2) {
                            args.push_back(arg + "_old");
                        }
                        for (auto arg : endArgs) {
                            args.push_back(arg);
                        }
                    }
                    SMTRef endInvariant;
                    if (main) {
                        endInvariant = mainInvariant(startIndex, args, funName);
                    } else {
                        endInvariant = invariant(startIndex, startIndex,
                                                 freeVarsMap.at(startIndex),
                                                 args, ProgramSelection::Both,
                                                 funName, memory, freeVarsMap);
                    }
                    SharedSMTRef dontLoopInvariant = getDontLoopInvariant(
                        std::move(endInvariant), startIndex, otherPathMap,
                        freeVarsMap, swapProgram(prog), memory);
                    const auto defs =
                        assignmentsOnPath(path, prog, freeVarsMap.at(endIndex),
                                          endIndex == EXIT_MARK, memory);
                    pathFuns[startIndex][startIndex].push_back(
                        [=](SharedSMTRef /*unused*/) {
                            return nonmutualSMT(dontLoopInvariant, defs, prog,
                                                memory);
                        });
                }
            }
        }
    }
    return pathFuns;
}

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

vector<AssignmentCallBlock> assignmentsOnPath(Path path, Program prog,
                                              vector<string> freeVars,
                                              bool toEnd, Memory memory) {
    const int progIndex = programIndex(prog);
    const auto filteredFreeVars = filterVars(progIndex, freeVars);

    vector<AssignmentCallBlock> allDefs;
    set<string> constructed;
    vector<CallInfo> callInfos;

    // Set the new values to the initial values
    vector<DefOrCallInfo> oldDefs;
    for (auto var : filteredFreeVars) {
        oldDefs.push_back(DefOrCallInfo(
            make_shared<Assignment>(var, stringExpr(var + "_old"))));
    }
    allDefs.push_back(AssignmentCallBlock(oldDefs, nullptr));

    // First block of path, this is special, because we don’t have a
    // previous
    // block so we can’t resolve phi nodes
    const auto startDefs =
        blockAssignments(*path.Start, nullptr, false, prog, memory);
    allDefs.push_back(AssignmentCallBlock(startDefs, nullptr));

    auto prev = path.Start;

    // Rest of the path
    unsigned int i = 0;
    for (auto edge : path.Edges) {
        i++;
        const bool last = i == path.Edges.size();
        const auto defs =
            blockAssignments(*edge.Block, prev, last && !toEnd, prog, memory);
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
            clause = makeBinOp("=>", assgns.condition, clause);
        }
    }
    return clause;
}

SharedSMTRef interleaveAssignments(
    SharedSMTRef endClause,
    MonoPair<vector<AssignmentCallBlock>> AssignmentCallBlocks, Memory memory) {
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
            clause = nonmutualRecursiveForall(clause, *callIt1, Program::First,
                                              memory);
            ++callIt1;
            ++assignmentIt1;
            break;
        case InterleaveStep::StepSecond:
            clause = addAssignments(clause, *assignmentIt2);
            clause = nonmutualRecursiveForall(clause, *callIt2, Program::Second,
                                              memory);
            ++callIt2;
            ++assignmentIt2;
            break;
        case InterleaveStep::StepBoth:
            assert(callIt1->callName == callIt2->callName);
            clause = addAssignments(clause, *assignmentIt2);
            clause = addAssignments(clause, *assignmentIt1);
            clause = mutualRecursiveForall(
                clause, makeMonoPair(*callIt1, *callIt2), memory);
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
                          Program prog, Memory memory) {
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
            clause = nonmutualRecursiveForall(clause, *callIt, prog, memory);
            ++callIt;
        }
        clause = addAssignments(clause, assgnsVec);
    }
    return clause;
}

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

SMTRef mutualRecursiveForall(SharedSMTRef clause, MonoPair<CallInfo> callPair,
                             Memory memory) {
    const uint32_t varArgs =
        static_cast<uint32_t>(callPair.first.args.size()) -
        callPair.first.fun.getFunctionType()->getNumParams();
    vector<SortedVar> args;
    args.push_back(SortedVar(callPair.first.assignedTo, "Int"));
    args.push_back(SortedVar(callPair.second.assignedTo, "Int"));
    if (memory & HEAP_MASK) {
        args.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        args.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    vector<SharedSMTRef> implArgs;

    callPair.indexedForEach(addMemory(implArgs, memory));
    vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(callPair.first.assignedTo));
    implArgs.push_back(stringExpr(callPair.second.assignedTo));
    if (memory & HEAP_MASK) {
        implArgs.push_back(stringExpr("HEAP$1_res"));
        implArgs.push_back(stringExpr("HEAP$2_res"));
    }
    SMTRef postInvariant = llvm::make_unique<Op>(
        invariantName(ENTRY_MARK, ProgramSelection::Both,
                      callPair.first.callName, InvariantAttr::NONE, varArgs),
        implArgs, !callPair.first.externFun);
    if (memory & STACK_MASK) {
        // TODO we need to add the stack somewhere here
    }
    SMTRef result = makeBinOp("=>", std::move(postInvariant), clause);
    result = llvm::make_unique<Forall>(args, std::move(result));
    if (callPair.first.externFun) {
        return result;
    }
    SMTRef preInv = llvm::make_unique<Op>(
        invariantName(ENTRY_MARK, ProgramSelection::Both,
                      callPair.first.callName, InvariantAttr::PRE),
        preArgs);
    return makeBinOp("and", std::move(preInv), std::move(result));
}

SMTRef nonmutualRecursiveForall(SharedSMTRef clause, CallInfo call,
                                Program prog, Memory memory) {
    vector<SortedVar> forallArgs;
    vector<SharedSMTRef> implArgs;

    const int progIndex = programIndex(prog);
    const string programS = std::to_string(progIndex);

    const uint32_t varArgs = static_cast<uint32_t>(call.args.size()) -
                             call.fun.getFunctionType()->getNumParams();
    forallArgs.push_back(SortedVar(call.assignedTo, "Int"));
    if (memory & HEAP_MASK) {
        forallArgs.push_back(
            SortedVar("HEAP$" + programS + "_res", "(Array Int Int)"));
    }
    addMemory(implArgs, memory)(call, progIndex);
    const vector<SharedSMTRef> preArgs = implArgs;

    implArgs.push_back(stringExpr(call.assignedTo));
    if (memory & HEAP_MASK) {
        implArgs.push_back(stringExpr("HEAP$" + programS + "_res"));
    }

    const SharedSMTRef endInvariant = make_shared<Op>(
        invariantName(ENTRY_MARK, asSelection(prog), call.callName,
                      InvariantAttr::NONE, varArgs),
        implArgs, !call.externFun);
    if (memory & STACK_MASK) {
        // TODO We need to add the stack somewhere here
    }
    SMTRef result = makeBinOp("=>", endInvariant, clause);
    result = llvm::make_unique<Forall>(forallArgs, std::move(result));
    if (call.externFun) {
        return result;
    }
    const auto preInv =
        make_shared<Op>(invariantName(ENTRY_MARK, asSelection(prog),
                                      call.callName, InvariantAttr::PRE),
                        preArgs);
    if (memory & STACK_MASK) {
        return makeBinOp("and", preInv, std::move(result));
    } else {
        return makeBinOp("and", preInv, std::move(result));
    }
}

/// Wrap the clause in a forall
SharedSMTRef forallStartingAt(SharedSMTRef clause, vector<string> freeVars,
                              int blockIndex, ProgramSelection prog,
                              string funName, bool main,
                              FreeVarsMap freeVarsMap, Memory memory) {
    vector<SortedVar> vars;
    vector<string> preVars;
    for (const auto &arg : freeVars) {
        std::smatch matchResult;
        if (std::regex_match(arg, matchResult, HEAP_REGEX)) {
            vars.push_back(SortedVar(arg + "_old", "(Array Int Int)"));
            preVars.push_back(arg + "_old");
        } else {
            vars.push_back(SortedVar(arg + "_old", "Int"));
            preVars.push_back(arg + "_old");
        }
    }

    if (vars.empty()) {
        return clause;
    }

    if (main && blockIndex == ENTRY_MARK) {
        vector<string> args;
        for (auto arg : freeVars) {
            args.push_back(arg + "_old");
        }
        clause = makeBinOp("=>", makeOp("IN_INV", args), clause);
    } else {
        InvariantAttr attr = main ? InvariantAttr::MAIN : InvariantAttr::PRE;
        preVars = fillUpArgs(preVars, freeVarsMap, memory, prog, attr);
        SMTRef preInv =
            makeOp(invariantName(blockIndex, prog, funName, attr), preVars);
        clause = makeBinOp("=>", std::move(preInv), clause);
    }

    if (SMTGenerationOpts::getInstance().MuZ) {
        // μZ rules are implicitly universally quantified
        return clause;
    }
    return llvm::make_unique<Forall>(vars, clause);
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SharedSMTRef makeFunArgsEqual(SharedSMTRef clause, SharedSMTRef preClause,
                              vector<string> Args1, vector<string> Args2) {
    vector<string> args;
    args.insert(args.end(), Args1.begin(), Args1.end());
    args.insert(args.end(), Args2.begin(), Args2.end());
    assert(Args1.size() == Args2.size());

    auto inInv = makeOp("IN_INV", args);

    return makeBinOp("=>", std::move(inInv),
                     makeBinOp("and", clause, preClause));
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SharedSMTRef equalInputsEqualOutputs(vector<string> funArgs,
                                     vector<string> funArgs1,
                                     vector<string> funArgs2, string funName,
                                     FreeVarsMap freeVarsMap, Memory memory) {
    vector<SortedVar> forallArgs;
    vector<string> args;
    vector<string> preInvArgs;
    args.insert(args.end(), funArgs.begin(), funArgs.end());
    preInvArgs = args;

    for (auto arg : funArgs) {
        forallArgs.push_back(SortedVar(arg, argSort(arg)));
    }
    forallArgs.push_back(SortedVar("result$1", "Int"));
    forallArgs.push_back(SortedVar("result$2", "Int"));
    if (memory & HEAP_MASK) {
        forallArgs.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        forallArgs.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    args.push_back("result$1");
    args.push_back("result$2");
    if (memory & HEAP_MASK) {
        args.push_back("HEAP$1_res");
        args.push_back("HEAP$2_res");
    }
    args = fillUpArgs(args, freeVarsMap, memory, ProgramSelection::Both,
                      InvariantAttr::NONE);
    vector<string> outArgs = {"result$1", "result$2"};
    vector<string> sortedFunArgs1 = funArgs1;
    vector<string> sortedFunArgs2 = funArgs2;
    std::sort(sortedFunArgs1.begin(), sortedFunArgs1.end());
    std::sort(sortedFunArgs2.begin(), sortedFunArgs2.end());
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const string &arg : funArgs1) {
            if (!std::regex_match(arg, HEAP_REGEX)) {
                outArgs.push_back(arg);
            }
        }
    }
    if (memory & HEAP_MASK) {
        outArgs.push_back("HEAP$1_res");
    }
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const string &arg : funArgs2) {
            if (!std::regex_match(arg, HEAP_REGEX)) {
                outArgs.push_back(arg);
            }
        }
    }
    if (memory & HEAP_MASK) {
        outArgs.push_back("HEAP$2_res");
    }
    const SharedSMTRef equalResults = makeBinOp(
        "=>", makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both, funName),
                     args),
        makeOp("OUT_INV", outArgs));
    preInvArgs = fillUpArgs(preInvArgs, freeVarsMap, memory,
                            ProgramSelection::Both, InvariantAttr::PRE);
    SMTRef preInv = makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                         funName, InvariantAttr::PRE),
                           preInvArgs);

    const auto equalArgs =
        makeFunArgsEqual(equalResults, std::move(preInv), funArgs1, funArgs2);
    const auto forallInputs = make_shared<Forall>(forallArgs, equalArgs);
    return make_shared<Assert>(forallInputs);
}

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

/// Collect the free variables for the entry block of the PathMap
/// A variable is free if we use it but didn't create it
std::pair<set<string>, map<int, set<string>>>
freeVarsForBlock(map<int, Paths> pathMap) {
    set<string> freeVars;
    map<int, set<string>> constructedIntersection;
    for (const auto &paths : pathMap) {
        for (const auto &path : paths.second) {
            const llvm::BasicBlock *prev = path.Start;
            set<string> constructed;

            // the first block is special since we can't resolve phi
            // nodes here
            for (auto &instr : *path.Start) {
                constructed.insert(instr.getName());
                if (llvm::isa<llvm::PHINode>(instr)) {
                    freeVars.insert(instr.getName());
                    continue;
                }
                if (const auto callInst =
                        llvm::dyn_cast<llvm::CallInst>(&instr)) {
                    for (unsigned int i = 0; i < callInst->getNumArgOperands();
                         i++) {
                        const auto arg = callInst->getArgOperand(i);
                        if (!arg->getName().empty() &&
                            constructed.find(arg->getName()) ==
                                constructed.end()) {
                            freeVars.insert(arg->getName());
                        }
                    }
                    continue;
                }
                for (const auto op : instr.operand_values()) {
                    if (constructed.find(op->getName()) == constructed.end() &&
                        !op->getName().empty() &&
                        !llvm::isa<llvm::BasicBlock>(op)) {
                        freeVars.insert(op->getName());
                    }
                }
            }

            // now deal with the rest
            for (const auto &edge : path.Edges) {
                for (auto &instr : *edge.Block) {
                    constructed.insert(instr.getName());
                    if (const auto phiInst =
                            llvm::dyn_cast<llvm::PHINode>(&instr)) {
                        const auto incoming =
                            phiInst->getIncomingValueForBlock(prev);
                        if (constructed.find(incoming->getName()) ==
                                constructed.end() &&
                            !incoming->getName().empty() &&
                            !llvm::isa<llvm::BasicBlock>(incoming)) {
                            freeVars.insert(incoming->getName());
                        }
                        continue;
                    }
                    if (const auto callInst =
                            llvm::dyn_cast<llvm::CallInst>(&instr)) {
                        for (unsigned int i = 0;
                             i < callInst->getNumArgOperands(); i++) {
                            const auto arg = callInst->getArgOperand(i);
                            if (!arg->getName().empty() &&
                                constructed.find(arg->getName()) ==
                                    constructed.end()) {
                                freeVars.insert(arg->getName());
                            }
                        }
                        continue;
                    }
                    for (const auto op : instr.operand_values()) {
                        if (constructed.find(op->getName()) ==
                                constructed.end() &&
                            !op->getName().empty() &&
                            !llvm::isa<llvm::BasicBlock>(op)) {
                            freeVars.insert(op->getName());
                        }
                    }
                }
                prev = edge.Block;
            }

            set<string> newConstructedIntersection;
            if (constructedIntersection.find(paths.first) ==
                constructedIntersection.end()) {
                constructedIntersection.insert(
                    make_pair(paths.first, constructed));
                ;
            } else {
                std::set_intersection(
                    constructed.begin(), constructed.end(),
                    constructedIntersection.at(paths.first).begin(),
                    constructedIntersection.at(paths.first).end(),
                    inserter(newConstructedIntersection,
                             newConstructedIntersection.begin()));
                constructedIntersection.insert(
                    make_pair(paths.first, newConstructedIntersection));
            }
        }
    }
    return make_pair(freeVars, constructedIntersection);
}

FreeVarsMap freeVars(PathMap map1, PathMap map2, vector<string> funArgs,
                     Memory memory) {
    map<int, set<string>> freeVarsMap;
    FreeVarsMap freeVarsMapVect;
    map<int, map<int, set<string>>> constructed;
    for (const auto &it : map1) {
        const int index = it.first;
        auto freeVars1 = freeVarsForBlock(map1.at(index));
        const auto freeVars2 = freeVarsForBlock(map2.at(index));
        for (auto var : freeVars2.first) {
            freeVars1.first.insert(var);
        }
        freeVarsMap.insert(make_pair(index, freeVars1.first));

        // constructed variables
        for (auto mapIt : freeVars2.second) {
            for (auto var : mapIt.second) {
                freeVars1.second[mapIt.first].insert(var);
            }
        }

        constructed.insert(make_pair(index, freeVars1.second));
    }

    freeVarsMap[EXIT_MARK] = set<string>();
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const string &arg : funArgs) {
            freeVarsMap[EXIT_MARK].insert(arg);
        }
    }
    freeVarsMap[UNREACHABLE_MARK] = set<string>();

    // search for a least fixpoint
    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto &it : map1) {
            const int startIndex = it.first;
            for (const auto &itInner : it.second) {
                const int endIndex = itInner.first;
                for (auto var : freeVarsMap.at(endIndex)) {
                    if (constructed.at(startIndex).at(endIndex).find(var) ==
                        constructed.at(startIndex).at(endIndex).end()) {
                        const auto inserted =
                            freeVarsMap.at(startIndex).insert(var);
                        changed = changed || inserted.second;
                    }
                }
            }
        }
    }

    const auto addMemoryArrays = [memory](vector<string> vars,
                                          int index) -> vector<string> {
        string stringIndex = std::to_string(index);
        if (memory & HEAP_MASK) {
            vars.push_back("HEAP$" + stringIndex);
        }
        if (memory & STACK_MASK) {
            vars.push_back("STACK$" + stringIndex);
        }
        return vars;
    };

    for (auto it : freeVarsMap) {
        const int index = it.first;
        vector<string> varsVect;
        for (auto var : it.second) {
            varsVect.push_back(var);
        }
        const auto argPair =
            makeMonoPair(filterVars(1, varsVect), filterVars(2, varsVect))
                .indexedMap<vector<string>>(addMemoryArrays);
        freeVarsMapVect[index] = concat(argPair);
    }

    const auto argPair =
        makeMonoPair(filterVars(1, funArgs), filterVars(2, funArgs))
            .indexedMap<vector<string>>(addMemoryArrays);
    // The input arguments should be in the function call order so we can’t add
    // them before
    freeVarsMapVect[ENTRY_MARK] = concat(argPair);

    return freeVarsMapVect;
}

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

MonoPair<vector<string>> functionArgs(const llvm::Function &fun1,
                                      const llvm::Function &fun2) {
    vector<string> args1;
    for (auto &arg : fun1.args()) {
        args1.push_back(arg.getName());
    }
    vector<string> args2;
    for (auto &arg : fun2.args()) {
        args2.push_back(arg.getName());
    }
    return makeMonoPair(args1, args2);
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
            if (callInfos1[i - 1] == callInfos2[j - 1]) {
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
        if (callInfos1[i - 1] == callInfos2[j - 1]) {
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
                            FreeVarsMap freeVars, Program prog, Memory memory) {
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
        auto defs = assignmentsOnPath(path, prog, freeVars.at(startIndex),
                                      false, memory);
        auto smt = nonmutualSMT(stringExpr("false"), defs, prog, memory);
        dontLoopExprs.push_back(smt);
    }
    if (!dontLoopExprs.empty()) {
        auto andExpr = make_shared<Op>("and", dontLoopExprs);
        clause = makeBinOp("=>", andExpr, std::move(clause));
    }
    return clause;
}

auto addMemory(vector<SharedSMTRef> &implArgs, Memory memory)
    -> function<void(CallInfo call, int index)> {
    return [&implArgs, memory](CallInfo call, int index) {
        string indexString = std::to_string(index);
        for (auto arg : call.args) {
            implArgs.push_back(arg);
        }
        if (memory & HEAP_MASK) {
            implArgs.push_back(stringExpr("HEAP$" + indexString));
        }
        if (memory & STACK_MASK) {
            implArgs.push_back(stringExpr("STACK$" + indexString));
        }
    };
}

vector<SharedSMTRef> declareVariables(FreeVarsMap freeVarsMap) {
    set<string> uniqueVars;
    for (auto it : freeVarsMap) {
        for (const string &var : it.second) {
            uniqueVars.insert(var);
        }
    }
    vector<SharedSMTRef> variables;
    for (string var : uniqueVars) {
        string type = "Int";
        if (std::regex_match(var, HEAP_REGEX)) {
            type = "(Array Int Int)";
        }
        variables.push_back(make_shared<VarDecl>(var + "_old", type));
    }
    return variables;
}
