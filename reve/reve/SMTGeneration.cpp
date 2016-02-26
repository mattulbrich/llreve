#include "SMTGeneration.h"

#include "Compat.h"
#include "Invariant.h"
#include "Opts.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"

#include <iostream>

using llvm::CmpInst;
using std::vector;
using std::map;
using std::function;
using std::string;
using smt::SMTRef;
using smt::Assert;
using smt::Op;
using smt::name;
using smt::Assignment;
using smt::SortedVar;
using smt::makeBinOp;
using smt::Forall;
using smt::makeOp;
using smt::FunDef;
using smt::VarDecl;
using smt::Comment;
using std::make_shared;
using std::make_pair;
using std::set;
using std::string;

vector<SMTRef> functionAssertion(MonoPair<llvm::Function *> funs,
                                 MonoPair<FAMRef> fams, bool offByN,
                                 vector<SMTRef> &declarations, Memory memory) {
    const auto pathMaps = zipWith<llvm::Function *, FAMRef, PathMap>(
        funs, fams, [](llvm::Function *fun, FAMRef fam) -> PathMap {
            return fam->getResult<PathAnalysis>(*fun);
        });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = zipWith<llvm::Function *, FAMRef, BidirBlockMarkMap>(
        funs, fams, [](llvm::Function *fun, FAMRef fam) -> BidirBlockMarkMap {
            return fam->getResult<MarkAnalysis>(*fun);
        });
    const string funName = funs.first->getName();
    const auto funArgsPair = functionArgs(*funs.first, *funs.second);
    const auto funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) -> vector<string> {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });
    FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, memory);
    vector<SMTRef> smtExprs;
    vector<SMTRef> pathExprs;

    auto addInvariant = [&](SMTRef invariant) {
        declarations.push_back(invariant);

    };
    if (!SingleInvariantFlag) {
        const auto invariants =
            invariantDeclaration(ENTRY_MARK, freeVarsMap[ENTRY_MARK],
                                 ProgramSelection::Both, funName, memory);
        const auto invariants1 = invariantDeclaration(
            ENTRY_MARK, filterVars(1, freeVarsMap[ENTRY_MARK]),
            ProgramSelection::First, funName, memory);
        const auto invariants2 = invariantDeclaration(
            ENTRY_MARK, filterVars(2, freeVarsMap[ENTRY_MARK]),
            ProgramSelection::Second, funName, memory);
        invariants.forEach(addInvariant);
        invariants1.forEach(addInvariant);
        invariants2.forEach(addInvariant);
    } else {
        const auto invariants = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::Both, funName);
        const auto invariants1 = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::First, funName);
        const auto invariants2 = singleInvariantDeclaration(
            freeVarsMap, memory, ProgramSelection::Second, funName);
        invariants.forEach(addInvariant);
        invariants1.forEach(addInvariant);
        invariants2.forEach(addInvariant);
    }

    const auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap, memory);
    const auto recDecls =
        recDeclarations(pathMaps.first, funName, freeVarsMap, memory);
    declarations.insert(declarations.end(), recDecls.begin(), recDecls.end());
    for (auto it : synchronizedPaths) {
        const int startIndex = it.first;
        for (auto it2 : it.second) {
            const int endIndex = it2.first;
            const auto endInvariant =
                invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                          freeVarsMap.at(endIndex), ProgramSelection::Both,
                          funName, memory, freeVarsMap);
            for (auto pathFun : it2.second) {
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

    // generate forbidden paths
    pathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    const auto forbiddenPaths = getForbiddenPaths(
        pathMaps, marked, freeVarsMap, offByN, funName, false, memory);
    pathExprs.insert(pathExprs.end(), forbiddenPaths.begin(),
                     forbiddenPaths.end());

    if (offByN) {
        // generate off by n paths
        pathExprs.push_back(make_shared<Comment>("OFF BY N"));
        const auto offByNPaths =
            getOffByNPaths(pathMaps.first, pathMaps.second, freeVarsMap,
                           funName, false, memory);
        for (auto it : offByNPaths) {
            int startIndex = it.first;
            for (auto it2 : it.second) {
                for (auto pathFun : it2.second) {
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
vector<SMTRef> mainAssertion(MonoPair<llvm::Function *> funs,
                             MonoPair<FAMRef> fams, bool offByN,
                             vector<SMTRef> &declarations, bool onlyRec,
                             Memory memory, bool dontNest) {
    const auto pathMaps = zipWith<llvm::Function *, FAMRef, PathMap>(
        funs, fams, [](llvm::Function *fun, FAMRef fam) -> PathMap {
            return fam->getResult<PathAnalysis>(*fun);
        });
    checkPathMaps(pathMaps.first, pathMaps.second);
    const auto marked = zipWith<llvm::Function *, FAMRef, BidirBlockMarkMap>(
        funs, fams, [](llvm::Function *fun, FAMRef fam) -> BidirBlockMarkMap {
            return fam->getResult<MarkAnalysis>(*fun);
        });
    const string funName = funs.first->getName();
    const auto funArgsPair = functionArgs(*funs.first, *funs.second);
    const auto funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });

    FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, memory);
    if (MuZFlag) {
        vector<SMTRef> variables = declareVariables(freeVarsMap);
        declarations.insert(declarations.end(), variables.begin(),
                            variables.end());
    }
    vector<SMTRef> smtExprs;

    if (onlyRec) {
        smtExprs.push_back(equalInputsEqualOutputs(
            freeVarsMap[ENTRY_MARK], filterVars(1, freeVarsMap[ENTRY_MARK]),
            filterVars(2, freeVarsMap[ENTRY_MARK]), funName, freeVarsMap,
            memory));
        return smtExprs;
    }

    if (SingleInvariantFlag) {
        declarations.push_back(
            singleMainInvariant(freeVarsMap, memory, ProgramSelection::Both));
    }

    auto synchronizedPaths = getSynchronizedPaths(
        pathMaps.first, pathMaps.second, freeVarsMap, memory);
    const auto mainDecls =
        mainDeclarations(pathMaps.first, funName, freeVarsMap);
    declarations.insert(declarations.end(), mainDecls.begin(), mainDecls.end());
    const auto forbiddenPaths = getForbiddenPaths(
        pathMaps, marked, freeVarsMap, offByN, funName, true, memory);
    if (offByN) {
        const auto offByNPaths =
            getOffByNPaths(pathMaps.first, pathMaps.second, freeVarsMap,
                           funName, true, memory);
        synchronizedPaths = mergePathFuns(synchronizedPaths, offByNPaths);
    }
    auto transposedPaths = transpose(synchronizedPaths);
    // remove cycles
    for (auto &it : transposedPaths) {
        it.second.erase(it.first);
    }
    for (auto it : synchronizedPaths) {
        const int startIndex = it.first;
        vector<SMTRef> pathsStartingHere;
        for (auto it2 : it.second) {
            const int endIndex = it2.first;
            auto endInvariant = mainInvariant(
                endIndex, freeVarsMap.at(endIndex), funName, memory);
            if (MuZFlag && endIndex == EXIT_MARK) {
                endInvariant = makeBinOp("=>", makeUnaryOp("not", endInvariant),
                                         name("END_QUERY"));
            }
            for (auto pathFun : it2.second) {
                pathsStartingHere.push_back(pathFun(endInvariant));
            }
        }
        if (dontNest) {
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
    smtExprs.push_back(make_shared<Comment>("forbidden main"));
    smtExprs.insert(smtExprs.end(), forbiddenPaths.begin(),
                    forbiddenPaths.end());
    return smtExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                     FreeVarsMap freeVarsMap, Memory memory) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> pathFuns;
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
                            [=](SMTRef end) {
                                return interleaveAssignments(end, defs, memory);
                            });
                    }
                }
            }
        }
    }

    return pathFuns;
}

vector<SMTRef> mainDeclarations(PathMap pathMap, string funName,
                                FreeVarsMap freeVarsMap) {
    vector<SMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK && !SingleInvariantFlag) {
            // ignore entry node
            const auto invariant =
                mainInvariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                         ProgramSelection::Both, funName);
            declarations.push_back(invariant);
        }
    }
    return declarations;
}

vector<SMTRef> recDeclarations(PathMap pathMap, string funName,
                               FreeVarsMap freeVarsMap, Memory memory) {
    vector<SMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK && !SingleInvariantFlag) {
            // ignore entry node
            const auto invariants =
                invariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                     ProgramSelection::Both, funName, memory);
            declarations.push_back(invariants.first);
            declarations.push_back(invariants.second);
        }
    }
    return declarations;
}

vector<SMTRef> getForbiddenPaths(MonoPair<PathMap> pathMaps,
                                 MonoPair<BidirBlockMarkMap> marked,
                                 FreeVarsMap freeVarsMap, bool offByN,
                                 string funName, bool main, Memory memory) {
    vector<SMTRef> pathExprs;
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
                            if (!offByN ||
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
                                    name("false"), makeMonoPair(smt1, smt2),
                                    memory);
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

void nonmutualPaths(PathMap pathMap, vector<SMTRef> &pathExprs,
                    FreeVarsMap freeVarsMap, Program prog, string funName,
                    vector<SMTRef> &declarations, Memory memory) {
    const int progIndex = programIndex(prog);
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK && !SingleInvariantFlag) {
            const auto invariants = invariantDeclaration(
                startIndex, filterVars(progIndex, freeVarsMap.at(startIndex)),
                asSelection(prog), funName, memory);
            invariants.forEach(
                [&declarations](SMTRef inv) { declarations.push_back(inv); });
        }
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            for (const auto &path : innerPathMapIt.second) {
                const auto endInvariant1 =
                    invariant(startIndex, endIndex, freeVarsMap.at(startIndex),
                              freeVarsMap.at(endIndex), asSelection(prog),
                              funName, memory, freeVarsMap);
                const auto defs =
                    assignmentsOnPath(path, prog, freeVarsMap.at(startIndex),
                                      endIndex == EXIT_MARK, memory);
                pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                    nonmutualSMT(endInvariant1, defs, prog, memory),
                    filterVars(progIndex, freeVarsMap.at(startIndex)),
                    startIndex, asSelection(prog), funName, false, freeVarsMap,
                    memory)));
            }
        }
    }
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
getOffByNPaths(PathMap pathMap1, PathMap pathMap2, FreeVarsMap freeVarsMap,
               string funName, bool main, Memory memory) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> pathFuns;
    vector<SMTRef> paths;
    const auto firstPaths = offByNPathsOneDir(
        pathMap1, pathMap2, freeVarsMap, Program::First, funName, main, memory);
    const auto secondPaths =
        offByNPathsOneDir(pathMap2, pathMap1, freeVarsMap, Program::Second,
                          funName, main, memory);
    return mergePathFuns(firstPaths, secondPaths);
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                  FreeVarsMap freeVarsMap, Program prog, string funName,
                  bool main, Memory memory) {
    const int progIndex = programIndex(prog);
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> pathFuns;
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
                        endInvariant =
                            mainInvariant(startIndex, args, funName, memory);
                    } else {
                        endInvariant = invariant(startIndex, startIndex,
                                                 freeVarsMap.at(startIndex),
                                                 args, ProgramSelection::Both,
                                                 funName, memory, freeVarsMap);
                    }
                    const auto dontLoopInvariant = getDontLoopInvariant(
                        endInvariant, startIndex, otherPathMap, freeVarsMap,
                        swapProgram(prog), memory);
                    const auto defs =
                        assignmentsOnPath(path, prog, freeVarsMap.at(endIndex),
                                          endIndex == EXIT_MARK, memory);
                    pathFuns[startIndex][startIndex].push_back(
                        [=](SMTRef /*unused*/) {
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
        oldDefs.push_back(
            DefOrCallInfo(make_shared<Assignment>(var, name(var + "_old"))));
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

SMTRef addAssignments(const SMTRef end, vector<AssignmentBlock> assignments) {
    SMTRef clause = end;
    for (auto assgns : makeReverse(assignments)) {
        clause = nestLets(clause, assgns.definitions);
        if (assgns.condition) {
            clause = makeBinOp("=>", assgns.condition, clause);
        }
    }
    return clause;
}

SMTRef interleaveAssignments(
    SMTRef endClause,
    MonoPair<vector<AssignmentCallBlock>> AssignmentCallBlocks, Memory memory) {
    SMTRef clause = endClause;
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

SMTRef nonmutualSMT(SMTRef endClause,
                    vector<AssignmentCallBlock> assignmentCallBlocks,
                    Program prog, Memory memory) {
    SMTRef clause = endClause;
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

SMTRef mutualRecursiveForall(SMTRef clause, MonoPair<CallInfo> callPair,
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
    vector<SMTRef> implArgs;
    vector<SMTRef> preArgs;

    if (callPair.first.externFun) {
        callPair.indexedForEach([&implArgs, memory](CallInfo call, int index) {
            for (auto arg : call.args) {
                implArgs.push_back(arg);
            }
            if (memory & HEAP_MASK) {
                implArgs.push_back(name("HEAP$" + std::to_string(index)));
            }
        });
        implArgs.push_back(name(callPair.first.assignedTo));
        implArgs.push_back(name(callPair.second.assignedTo));
        if (memory & HEAP_MASK) {
            implArgs.push_back(name("HEAP$1_res"));
            implArgs.push_back(name("HEAP$2_res"));
        }
        const auto postInvariant =
            make_shared<Op>(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                          callPair.first.callName,
                                          InvariantAttr::NONE, varArgs),
                            implArgs, false);
        clause = makeBinOp("=>", postInvariant, clause);
        return make_shared<Forall>(args, clause);
    } else {
        callPair.indexedForEach(addMemory(implArgs, memory));
        preArgs.insert(preArgs.end(), implArgs.begin(), implArgs.end());

        implArgs.push_back(name(callPair.first.assignedTo));
        implArgs.push_back(name(callPair.second.assignedTo));
        if (memory & HEAP_MASK) {
            implArgs.push_back(name("HEAP$1_res"));
            implArgs.push_back(name("HEAP$2_res"));
        }
        SMTRef postInvariant =
            make_shared<Op>(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                          callPair.first.callName),
                            implArgs);
        clause = makeBinOp("=>", postInvariant, clause);
        clause = make_shared<Forall>(args, clause);
        const auto preInv = make_shared<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both,
                          callPair.first.callName, InvariantAttr::PRE),
            preArgs);
        return makeBinOp("and", preInv, clause);
    }
}

SMTRef nonmutualRecursiveForall(SMTRef clause, CallInfo call, Program prog,
                                Memory memory) {
    vector<SortedVar> forallArgs;
    vector<SMTRef> implArgs;
    vector<SMTRef> preArgs;

    const int progIndex = programIndex(prog);
    const string programS = std::to_string(progIndex);

    const uint32_t varArgs = static_cast<uint32_t>(call.args.size()) -
                             call.fun.getFunctionType()->getNumParams();
    forallArgs.push_back(SortedVar(call.assignedTo, "Int"));
    if (memory & HEAP_MASK) {
        forallArgs.push_back(
            SortedVar("HEAP$" + programS + "_res", "(Array Int Int)"));
    }
    if (call.externFun) {
        if (memory & HEAP_MASK) {
            call.args.push_back(name("HEAP$" + programS));
        }
        call.args.push_back(name(call.assignedTo));
        if (memory & HEAP_MASK) {
            call.args.push_back(name("HEAP$" + programS + "_res"));
        }
        const SMTRef endInvariant = make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(prog), call.callName,
                          InvariantAttr::NONE, varArgs),
            call.args, false);
        clause = makeBinOp("=>", endInvariant, clause);
        return make_shared<Forall>(forallArgs, clause);
    } else {
        addMemory(implArgs, memory)(call, progIndex);
        preArgs = implArgs;

        implArgs.push_back(name(call.assignedTo));
        if (memory & HEAP_MASK) {
            implArgs.push_back(name("HEAP$" + programS + "_res"));
        }

        SMTRef endInvariant = make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(prog), call.callName),
            implArgs);
        if (memory & STACK_MASK) {
            // TODO We need to add the stack somewhere here
        }
        clause = makeBinOp("=>", endInvariant, clause);
        clause = make_shared<Forall>(forallArgs, clause);
        const auto preInv =
            make_shared<Op>(invariantName(ENTRY_MARK, asSelection(prog),
                                          call.callName, InvariantAttr::PRE),
                            preArgs);
        if (memory & STACK_MASK) {
            return makeBinOp("and", preInv, clause);
        } else {
            return makeBinOp("and", preInv, clause);
        }
    }
}

/// Wrap the clause in a forall
SMTRef forallStartingAt(SMTRef clause, vector<string> freeVars, int blockIndex,
                        ProgramSelection prog, string funName, bool main,
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

    SMTRef preInv;
    if (main && blockIndex == ENTRY_MARK) {
        vector<string> args;
        for (auto arg : freeVars) {
            args.push_back(arg + "_old");
        }
        clause = makeBinOp("=>", makeOp("IN_INV", args), clause);
    } else {
        InvariantAttr attr = main ? InvariantAttr::MAIN : InvariantAttr::PRE;
        preVars = fillUpArgs(preVars, freeVarsMap, memory, prog, attr);
        auto preInv =
            makeOp(invariantName(blockIndex, prog, funName, attr), preVars);
        clause = makeBinOp("=>", preInv, clause);
    }

    if (MuZFlag) {
        // μZ rules are implicitly universally quantified
        return clause;
    }
    return make_shared<Forall>(vars, clause);
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SMTRef makeFunArgsEqual(SMTRef clause, SMTRef preClause, vector<string> Args1,
                        vector<string> Args2) {
    vector<string> args;
    args.insert(args.end(), Args1.begin(), Args1.end());
    args.insert(args.end(), Args2.begin(), Args2.end());
    assert(Args1.size() == Args2.size());

    auto inInv = makeOp("IN_INV", args);

    return makeBinOp("=>", inInv, makeBinOp("and", clause, preClause));
}

SMTRef inInvariant(MonoPair<const llvm::Function *> funs, SMTRef body,
                   Memory memory, const llvm::Module &mod1,
                   const llvm::Module &mod2, bool strings) {

    vector<SMTRef> args;
    const auto funArgsPair =
        functionArgs(*funs.first, *funs.second)
            .indexedMap<vector<string>>(
                [memory](vector<string> args, int index) -> vector<string> {
                    string indexString = std::to_string(index);
                    if (memory & HEAP_MASK) {
                        args.push_back("HEAP$" + indexString);
                    }
                    if (memory & STACK_MASK) {
                        args.push_back("STACK$" + indexString);
                    }
                    return args;
                });
    vector<string> Args1 = funArgsPair.first;
    vector<string> Args2 = funArgsPair.second;

    assert(Args1.size() == Args2.size());

    vector<SortedVar> funArgs = concat(funArgsPair.map<vector<SortedVar>>(
        [](vector<string> args) -> vector<SortedVar> {
            vector<SortedVar> varArgs;
            for (auto arg : args) {
                varArgs.push_back(SortedVar(arg, argSort(arg)));
            }
            return varArgs;
        }));
    for (auto argPair : makeZip(Args1, Args2)) {
        args.push_back(makeBinOp("=", argPair.first, argPair.second));
    }
    if (body == nullptr) {
        body = make_shared<Op>("and", args);
    }
    if (strings) {
        // Add values of static arrays, strings and similar things
        vector<SMTRef> smtArgs = {body};
        makeMonoPair(&mod1, &mod2)
            .indexedMap<vector<SMTRef>>([&args](const llvm::Module *mod,
                                                int index) {
                return stringConstants(*mod, "HEAP$" + std::to_string(index));
            })
            .forEach([&smtArgs](vector<SMTRef> constants) {
                if (!constants.empty()) {
                    smtArgs.push_back(make_shared<Op>("and", constants));
                }
            });
        body = make_shared<Op>("and", smtArgs);
    }

    return make_shared<FunDef>("IN_INV", funArgs, "Bool", body);
}

SMTRef outInvariant(SMTRef body, Memory memory) {
    vector<SortedVar> funArgs = {SortedVar("result$1", "Int"),
                                 SortedVar("result$2", "Int")};
    if (memory & HEAP_MASK) {
        funArgs.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
        funArgs.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
    }
    if (body == nullptr) {
        body = makeBinOp("=", "result$1", "result$2");
        if (memory & HEAP_MASK) {
            body = makeBinOp("and", body, makeBinOp("=", "HEAP$1", "HEAP$2"));
        }
    }

    return make_shared<FunDef>("OUT_INV", funArgs, "Bool", body);
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(vector<string> funArgs, vector<string> funArgs1,
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
    if (memory & HEAP_MASK) {
        outArgs.push_back("HEAP$1_res");
        outArgs.push_back("HEAP$2_res");
    }
    const auto equalResults = makeBinOp(
        "=>", makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both, funName),
                     args),
        makeOp("OUT_INV", outArgs));
    preInvArgs = fillUpArgs(preInvArgs, freeVarsMap, memory,
                            ProgramSelection::Both, InvariantAttr::PRE);
    const auto preInv = makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                             funName, InvariantAttr::PRE),
                               preInvArgs);

    const auto equalArgs =
        makeFunArgsEqual(equalResults, preInv, funArgs1, funArgs2);
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
                        !op->getName().empty()) {
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
                            !incoming->getName().empty()) {
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
                            !op->getName().empty()) {
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
    freeVarsMap[UNREACHABLE_MARK] = set<string>();
    // search for a least fixpoint
    // don't tell anyone I wrote that
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
        SMTRef condition = assignments.condition;
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

vector<SMTRef> stringConstants(const llvm::Module &mod, string memory) {
    vector<SMTRef> stringConstants;
    for (const auto &global : mod.globals()) {
        const string globalName = global.getName();
        vector<SMTRef> stringConstant;
        if (global.hasInitializer() && global.isConstant()) {
            if (const auto arr = llvm::dyn_cast<llvm::ConstantDataArray>(
                    global.getInitializer())) {
                for (unsigned int i = 0; i < arr->getNumElements(); ++i) {
                    stringConstant.push_back(makeBinOp(
                        "=", name(std::to_string(arr->getElementAsInteger(i))),
                        makeBinOp(
                            "select", name(memory),
                            makeBinOp("+", globalName, std::to_string(i)))));
                }
            }
        }
        if (!stringConstant.empty()) {
            stringConstants.push_back(make_shared<Op>("and", stringConstant));
        }
    }
    return stringConstants;
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
    auto clause = endClause;
    vector<Path> dontLoopPaths;
    for (auto pathMapIt : pathMap.at(startIndex)) {
        if (pathMapIt.first == startIndex) {
            for (auto path : pathMapIt.second) {
                dontLoopPaths.push_back(path);
            }
        }
    }
    vector<SMTRef> dontLoopExprs;
    for (auto path : dontLoopPaths) {
        auto defs = assignmentsOnPath(path, prog, freeVars.at(startIndex),
                                      false, memory);
        auto smt = nonmutualSMT(name("false"), defs, prog, memory);
        dontLoopExprs.push_back(smt);
    }
    if (!dontLoopExprs.empty()) {
        auto andExpr = make_shared<Op>("and", dontLoopExprs);
        clause = makeBinOp("=>", andExpr, clause);
    }
    return clause;
}

auto addMemory(vector<SMTRef> &implArgs, Memory memory)
    -> function<void(CallInfo call, int index)> {
    return [&implArgs, memory](CallInfo call, int index) {
        string indexString = std::to_string(index);
        for (auto arg : call.args) {
            implArgs.push_back(arg);
        }
        if (memory & HEAP_MASK) {
            implArgs.push_back(name("HEAP$" + indexString));
        }
        if (memory & STACK_MASK) {
            implArgs.push_back(name("STACK$" + indexString));
        }
    };
}

vector<SMTRef> declareVariables(FreeVarsMap freeVarsMap) {
    set<string> uniqueVars;
    for (auto it : freeVarsMap) {
        for (const string &var : it.second) {
            uniqueVars.insert(var);
        }
    }
    vector<SMTRef> variables;
    for (string var : uniqueVars) {
        string type = "Int";
        if (std::regex_match(var, HEAP_REGEX)) {
            type = "(Array Int Int)";
        }
        variables.push_back(make_shared<VarDecl>(var + "_old", type));
    }
    return variables;
}
