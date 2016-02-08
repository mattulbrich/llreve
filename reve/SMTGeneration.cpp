#include "SMTGeneration.h"

#include "AnnotStackPass.h"
#include "Compat.h"
#include "Invariant.h"
#include "MarkAnalysis.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Intrinsics.h"

using llvm::CmpInst;

#include <iostream>

using std::vector;
using std::map;
using std::function;

vector<SMTRef> convertToSMT(llvm::Function &fun1, llvm::Function &fun2,
                            shared_ptr<llvm::FunctionAnalysisManager> fam1,
                            shared_ptr<llvm::FunctionAnalysisManager> fam2,
                            bool offByN, vector<SMTRef> &declarations,
                            Memory heap, bool everythingSigned) {
    const auto pathMap1 = fam1->getResult<PathAnalysis>(fun1);
    const auto pathMap2 = fam2->getResult<PathAnalysis>(fun2);
    checkPathMaps(pathMap1, pathMap2);
    const auto marked1 = fam1->getResult<MarkAnalysis>(fun1);
    const auto marked2 = fam2->getResult<MarkAnalysis>(fun2);
    const std::string funName = fun1.getName();
    const std::pair<vector<string>, vector<string>> funArgsPair =
        functionArgs(fun1, fun2);
    vector<string> funArgs;
    for (auto arg : funArgsPair.first) {
        funArgs.push_back(arg);
    }
    for (auto arg : funArgsPair.second) {
        funArgs.push_back(arg);
    }
    std::map<int, vector<string>> freeVarsMap =
        freeVars(pathMap1, pathMap2, funArgs, heap);
    vector<SMTRef> smtExprs;
    vector<SMTRef> pathExprs;

    // we only need pre invariants for mutual invariants
    const auto invariants =
        invariantDeclaration(ENTRY_MARK, freeVarsMap[ENTRY_MARK],
                             ProgramSelection::Both, funName, heap);
    declarations.push_back(invariants.first);
    declarations.push_back(invariants.second);
    const auto invariants1 =
        invariantDeclaration(ENTRY_MARK, filterVars(1, freeVarsMap[ENTRY_MARK]),
                             ProgramSelection::First, funName, heap);
    declarations.push_back(invariants1.first);
    declarations.push_back(invariants1.second);
    const auto invariants2 =
        invariantDeclaration(ENTRY_MARK, filterVars(2, freeVarsMap[ENTRY_MARK]),
                             ProgramSelection::Second, funName, heap);
    declarations.push_back(invariants2.first);
    declarations.push_back(invariants2.second);

    const auto synchronizedPaths =
        getSynchronizedPaths(pathMap1, pathMap2, freeVarsMap, funName,
                             declarations, heap, everythingSigned);

    // add actual path smts
    pathExprs.insert(pathExprs.end(), synchronizedPaths.begin(),
                     synchronizedPaths.end());

    // generate forbidden paths
    pathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    const auto forbiddenPaths =
        getForbiddenPaths(pathMap1, pathMap2, marked1, marked2, freeVarsMap,
                          offByN, funName, false, heap, everythingSigned);
    pathExprs.insert(pathExprs.end(), forbiddenPaths.begin(),
                     forbiddenPaths.end());

    if (offByN) {
        // generate off by n paths
        pathExprs.push_back(make_shared<Comment>("OFF BY N"));
        const auto offByNPaths =
            getOffByNPaths(pathMap1, pathMap2, freeVarsMap, funName, false,
                           heap, everythingSigned);
        for (auto it : offByNPaths) {
            int startIndex = it.first;
            for (auto it2 : it.second) {
                for (auto pathFun : it2.second) {
                    pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                        pathFun(nullptr), freeVarsMap.at(startIndex),
                        startIndex, ProgramSelection::Both, funName, false)));
                }
            }
        }
    }

    smtExprs.insert(smtExprs.end(), pathExprs.begin(), pathExprs.end());

    return smtExprs;
}

vector<SMTRef> mainAssertion(llvm::Function &fun1, llvm::Function &fun2,
                             shared_ptr<llvm::FunctionAnalysisManager> fam1,
                             shared_ptr<llvm::FunctionAnalysisManager> fam2,
                             bool offByN, vector<SMTRef> &declarations,
                             bool onlyRec, Memory heap, bool everythingSigned,
                             bool dontNest) {
    const auto pathMap1 = fam1->getResult<PathAnalysis>(fun1);
    const auto pathMap2 = fam2->getResult<PathAnalysis>(fun2);
    checkPathMaps(pathMap1, pathMap2);
    const auto marked1 = fam1->getResult<MarkAnalysis>(fun1);
    const auto marked2 = fam2->getResult<MarkAnalysis>(fun2);
    std::vector<SMTRef> smtExprs;
    const std::string funName = fun1.getName();
    const std::pair<vector<string>, vector<string>> funArgsPair =
        functionArgs(fun1, fun2);
    vector<string> funArgs;
    for (auto arg : funArgsPair.first) {
        funArgs.push_back(arg);
    }
    for (auto arg : funArgsPair.second) {
        funArgs.push_back(arg);
    }
    std::map<int, vector<string>> freeVarsMap =
        freeVars(pathMap1, pathMap2, funArgs, heap);

    if (onlyRec) {
        smtExprs.push_back(equalInputsEqualOutputs(
            freeVarsMap[ENTRY_MARK], filterVars(1, freeVarsMap[ENTRY_MARK]),
            filterVars(2, freeVarsMap[ENTRY_MARK]), funName, heap));
        return smtExprs;
    }

    auto synchronizedPaths =
        mainSynchronizedPaths(pathMap1, pathMap2, freeVarsMap, funName,
                              declarations, heap, everythingSigned);
    const auto forbiddenPaths =
        getForbiddenPaths(pathMap1, pathMap2, marked1, marked2, freeVarsMap,
                          offByN, funName, true, heap, everythingSigned);
    if (offByN) {
        smtExprs.push_back(make_shared<Comment>("offbyn main"));
        const auto offByNPaths =
            getOffByNPaths(pathMap1, pathMap2, freeVarsMap, funName, true, heap,
                           everythingSigned);
        synchronizedPaths = mergePathFuns(synchronizedPaths, offByNPaths);
    }
    auto transposedPaths = transpose(synchronizedPaths);
    // remove cycles
    for (auto &it : transposedPaths) {
        it.second.erase(it.first);
    }
    for (auto it : synchronizedPaths) {
        const int startIndex = it.first;
        std::vector<SMTRef> pathsStartingHere;
        for (auto it2 : it.second) {
            const int endIndex = it2.first;
            auto endInvariant = mainInvariant(
                endIndex, freeVarsMap.at(endIndex), funName, heap);
            for (auto pathFun : it2.second) {
                pathsStartingHere.push_back(pathFun(endInvariant));
            }
        }
        auto clause =
            forallStartingAt(make_shared<Op>("and", pathsStartingHere),
                             freeVarsMap.at(startIndex), startIndex,
                             ProgramSelection::Both, funName, true);
        if (!dontNest &&
            (transposedPaths.find(startIndex) != transposedPaths.end())) {
            if (transposedPaths.at(startIndex).size() == 1) {
                auto it = transposedPaths.at(startIndex).begin();
                const int comingFrom = it->first;
                if (it->second.size() == 1) {
                    const auto nestFun = it->second.at(0);
                    clause = forallStartingAt(
                        nestFun(clause), freeVarsMap.at(comingFrom), comingFrom,
                        ProgramSelection::Both, funName, true);
                }
            }
        }
        smtExprs.push_back(make_shared<Assert>(clause));
    }
    smtExprs.push_back(make_shared<Comment>("forbidden main"));
    smtExprs.insert(smtExprs.end(), forbiddenPaths.begin(),
                    forbiddenPaths.end());
    smtExprs.push_back(make_shared<Comment>("end"));
    return smtExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

vector<SMTRef> getSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                                    std::map<int, vector<string>> freeVarsMap,
                                    std::string funName,
                                    vector<SMTRef> &declarations, Memory heap,
                                    bool everythingSigned) {
    vector<SMTRef> pathExprs;
    for (auto &pathMapIt : pathMap1) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK) {
            // ignore entry node
            const auto invariants =
                invariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                     ProgramSelection::Both, funName, heap);
            declarations.push_back(invariants.first);
            declarations.push_back(invariants.second);
        }
        for (auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            const auto paths = pathMap2.at(startIndex).at(endIndex);
            for (auto &path1 : innerPathMapIt.second) {
                for (auto &path2 : paths) {
                    const auto endInvariant = invariant(
                        startIndex, endIndex, freeVarsMap.at(startIndex),
                        freeVarsMap.at(endIndex), ProgramSelection::Both,
                        funName, heap);
                    const auto defs1 = assignmentsOnPath(
                        path1, Program::First, freeVarsMap.at(startIndex),
                        endIndex == EXIT_MARK, heap, everythingSigned);
                    const auto defs2 = assignmentsOnPath(
                        path2, Program::Second, freeVarsMap.at(startIndex),
                        endIndex == EXIT_MARK, heap, everythingSigned);
                    pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                        interleaveAssignments(endInvariant, defs1, defs2, heap),
                        freeVarsMap.at(startIndex), startIndex,
                        ProgramSelection::Both, funName, false)));
                }
            }
        }
    }
    nonmutualPaths(pathMap1, pathExprs, freeVarsMap, Program::First, funName,
                   declarations, heap, everythingSigned);
    nonmutualPaths(pathMap2, pathExprs, freeVarsMap, Program::Second, funName,
                   declarations, heap, everythingSigned);

    return pathExprs;
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
mainSynchronizedPaths(PathMap pathMap1, PathMap pathMap2,
                      std::map<int, vector<string>> freeVarsMap,
                      std::string funName, vector<SMTRef> &declarations,
                      Memory heap, bool everythingSigned) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> pathFuns;
    for (const auto &pathMapIt : pathMap1) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK) {
            // ignore entry node
            const auto invariant =
                mainInvariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                         ProgramSelection::Both, funName);
            declarations.push_back(invariant);
        }
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            if (pathMap2.at(startIndex).find(endIndex) !=
                pathMap2.at(startIndex).end()) {
                const auto paths = pathMap2.at(startIndex).at(endIndex);
                for (const auto &path1 : innerPathMapIt.second) {
                    for (const auto &path2 : paths) {
                        const auto endInvariant = mainInvariant(
                            endIndex, freeVarsMap.at(endIndex), funName, heap);
                        const auto defs1 = assignmentsOnPath(
                            path1, Program::First, freeVarsMap.at(startIndex),
                            endIndex == EXIT_MARK, heap, everythingSigned);
                        const auto defs2 = assignmentsOnPath(
                            path2, Program::Second, freeVarsMap.at(startIndex),
                            endIndex == EXIT_MARK, heap, everythingSigned);
                        pathFuns[startIndex][endIndex].push_back(
                            [=](SMTRef end) {
                                return interleaveAssignments(end, defs1, defs2,
                                                             heap);
                            });
                    }
                }
            }
        }
    }

    return pathFuns;
}

vector<SMTRef> getForbiddenPaths(PathMap pathMap1, PathMap pathMap2,
                                 BidirBlockMarkMap marked1,
                                 BidirBlockMarkMap marked2,
                                 std::map<int, vector<string>> freeVarsMap,
                                 bool offByN, std::string funName, bool main,
                                 Memory heap, bool everythingSigned) {
    vector<SMTRef> pathExprs;
    for (const auto &pathMapIt : pathMap1) {
        const int startIndex = pathMapIt.first;
        for (const auto &innerPathMapIt1 : pathMapIt.second) {
            const int endIndex1 = innerPathMapIt1.first;
            for (auto &innerPathMapIt2 : pathMap2.at(startIndex)) {
                const auto endIndex2 = innerPathMapIt2.first;
                if (endIndex1 != endIndex2) {
                    for (const auto &path1 : innerPathMapIt1.second) {
                        for (const auto &path2 : innerPathMapIt2.second) {
                            const auto endBlock1 = lastBlock(path1);
                            const auto endBlock2 = lastBlock(path2);
                            const auto endIndices1 =
                                marked1.BlockToMarksMap[endBlock1];
                            const auto endIndices2 =
                                marked2.BlockToMarksMap[endBlock2];
                            if (!offByN ||
                                ((startIndex != endIndex1 && // no circles
                                  startIndex != endIndex2) &&
                                 intersection(endIndices1, endIndices2)
                                     .empty())) {
                                const auto smt2 = assignmentsOnPath(
                                    path2, Program::Second,
                                    freeVarsMap.at(startIndex),
                                    endIndex2 == EXIT_MARK, heap,
                                    everythingSigned);
                                const auto smt1 = assignmentsOnPath(
                                    path1, Program::First,
                                    freeVarsMap.at(startIndex),
                                    endIndex1 == EXIT_MARK, heap,
                                    everythingSigned);
                                // We need to interleave here, because otherwise
                                // extern functions are not matched
                                const auto smt = interleaveAssignments(
                                    name("false"), smt1, smt2, heap);
                                pathExprs.push_back(
                                    make_shared<Assert>(forallStartingAt(
                                        smt, freeVarsMap.at(startIndex),
                                        startIndex, ProgramSelection::Both,
                                        funName, main)));
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
                    std::map<int, vector<string>> freeVarsMap, Program prog,
                    std::string funName, vector<SMTRef> &declarations,
                    Memory heap, bool everythingSigned) {
    const int progIndex = programIndex(prog);
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK) {
            const auto invariants = invariantDeclaration(
                startIndex, filterVars(progIndex, freeVarsMap.at(startIndex)),
                asSelection(prog), funName, heap);
            declarations.push_back(invariants.first);
            declarations.push_back(invariants.second);
        }
        for (const auto &innerPathMapIt : pathMapIt.second) {
            const int endIndex = innerPathMapIt.first;
            for (const auto &path : innerPathMapIt.second) {
                const auto endInvariant1 = invariant(
                    startIndex, endIndex, freeVarsMap.at(startIndex),
                    freeVarsMap.at(endIndex), asSelection(prog), funName, heap);
                const auto defs = assignmentsOnPath(
                    path, prog, freeVarsMap.at(startIndex),
                    endIndex == EXIT_MARK, heap, everythingSigned);
                pathExprs.push_back(make_shared<Assert>(forallStartingAt(
                    nonmutualSMT(endInvariant1, defs, prog, heap),
                    filterVars(progIndex, freeVarsMap.at(startIndex)),
                    startIndex, asSelection(prog), funName, false)));
            }
        }
    }
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
getOffByNPaths(PathMap pathMap1, PathMap pathMap2,
               std::map<int, vector<string>> freeVarsMap, std::string funName,
               bool main, Memory heap, bool everythingSigned) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> pathFuns;
    vector<SMTRef> paths;
    const auto firstPaths =
        offByNPathsOneDir(pathMap1, pathMap2, freeVarsMap, Program::First,
                          funName, main, heap, everythingSigned);
    const auto secondPaths =
        offByNPathsOneDir(pathMap2, pathMap1, freeVarsMap, Program::Second,
                          funName, main, heap, everythingSigned);
    return mergePathFuns(firstPaths, secondPaths);
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
offByNPathsOneDir(PathMap pathMap, PathMap otherPathMap,
                  std::map<int, vector<string>> freeVarsMap, Program prog,
                  std::string funName, bool main, Memory heap,
                  bool everythingSigned) {
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
                            mainInvariant(startIndex, args, funName, heap);
                    } else {
                        endInvariant = invariant(
                            startIndex, startIndex, freeVarsMap.at(startIndex),
                            args, ProgramSelection::Both, funName, heap);
                    }
                    const auto dontLoopInvariant = getDontLoopInvariant(
                        endInvariant, startIndex, otherPathMap, freeVarsMap,
                        swapProgram(prog), heap, everythingSigned);
                    const auto defs = assignmentsOnPath(
                        path, prog, freeVarsMap.at(endIndex),
                        endIndex == EXIT_MARK, heap, everythingSigned);
                    pathFuns[startIndex][startIndex].push_back(
                        [=](SMTRef /*unused*/) {
                            return nonmutualSMT(dontLoopInvariant, defs, prog,
                                                heap);
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
                                              vector<std::string> freeVars,
                                              bool toEnd, Memory heap,
                                              bool everythingSigned) {
    const int progIndex = programIndex(prog);
    const auto filteredFreeVars = filterVars(progIndex, freeVars);

    vector<AssignmentCallBlock> allDefs;
    set<string> constructed;
    vector<CallInfo> callInfos;

    // Set the new values to the initial values
    vector<DefOrCallInfo> oldDefs;
    for (auto var : filteredFreeVars) {
        oldDefs.push_back(DefOrCallInfo(
            std::make_shared<Assignment>(var, name(var + "_old"))));
    }
    allDefs.push_back(AssignmentCallBlock(oldDefs, nullptr));

    // First block of path, this is special, because we don’t have a
    // previous
    // block so we can’t resolve phi nodes
    const auto startDefs = blockAssignments(*path.Start, nullptr, false, prog,
                                            heap, everythingSigned);
    allDefs.push_back(AssignmentCallBlock(startDefs, nullptr));

    auto prev = path.Start;

    // Rest of the path
    unsigned int i = 0;
    for (auto edge : path.Edges) {
        i++;
        const bool last = i == path.Edges.size();
        const auto defs = blockAssignments(*edge.Block, prev, last && !toEnd,
                                           prog, heap, everythingSigned);
        allDefs.push_back(AssignmentCallBlock(
            defs, edge.Cond == nullptr ? nullptr : edge.Cond->toSmt()));
        prev = edge.Block;
    }
    return allDefs;
}

SMTRef interleaveAssignments(SMTRef endClause,
                             vector<AssignmentCallBlock> AssignmentCallBlocks1,
                             vector<AssignmentCallBlock> AssignmentCallBlocks2,
                             Memory heap) {
    SMTRef clause = endClause;
    const auto splitAssignments1 = splitAssignments(AssignmentCallBlocks1);
    const auto splitAssignments2 = splitAssignments(AssignmentCallBlocks2);
    const auto AssignmentBlocks1 = splitAssignments1.first;
    const auto AssignmentBlocks2 = splitAssignments2.first;
    const auto CallInfo1 = splitAssignments1.second;
    const auto CallInfo2 = splitAssignments2.second;

    const auto interleaveSteps = matchFunCalls(CallInfo1, CallInfo2);

    assert(AssignmentBlocks1.size() == CallInfo1.size() + 1);
    assert(AssignmentBlocks2.size() == CallInfo2.size() + 1);
    assert(AssignmentCallBlocks1.size() >= 1);
    assert(AssignmentCallBlocks2.size() >= 1);

    auto CallIt1 = CallInfo1.rbegin();
    auto CallIt2 = CallInfo2.rbegin();
    auto AssignmentIt1 = AssignmentBlocks1.rbegin();
    auto AssignmentIt2 = AssignmentBlocks2.rbegin();

    // We step through the matched calls in reverse to build up the smt from
    // the
    // bottom up
    for (InterleaveStep step : makeReverse(interleaveSteps)) {
        switch (step) {
        case InterleaveStep::StepFirst:
            for (auto assgns : makeReverse(*AssignmentIt1)) {
                clause = nestLets(clause, assgns.definitions);
                if (assgns.condition) {
                    clause = makeBinOp("=>", assgns.condition, clause);
                }
            }
            clause = nonmutualRecursiveForall(clause, *CallIt1, Program::First,
                                              heap);
            ++CallIt1;
            ++AssignmentIt1;
            break;
        case InterleaveStep::StepSecond:
            for (auto assgns : makeReverse(*AssignmentIt2)) {
                clause = nestLets(clause, assgns.definitions);
                if (assgns.condition) {
                    clause = makeBinOp("=>", assgns.condition, clause);
                }
            }
            clause = nonmutualRecursiveForall(clause, *CallIt2, Program::Second,
                                              heap);
            ++CallIt2;
            ++AssignmentIt2;
            break;
        case InterleaveStep::StepBoth:
            assert(CallIt1->callName == CallIt2->callName);
            for (auto assgns : makeReverse(*AssignmentIt2)) {
                clause = nestLets(clause, assgns.definitions);
                if (assgns.condition) {
                    clause = makeBinOp("=>", assgns.condition, clause);
                }
            }
            for (auto assgns : makeReverse(*AssignmentIt1)) {
                clause = nestLets(clause, assgns.definitions);
                if (assgns.condition) {
                    clause = makeBinOp("=>", assgns.condition, clause);
                }
            }
            clause = mutualRecursiveForall(clause, *CallIt1, *CallIt2, heap);
            ++CallIt1;
            ++CallIt2;
            ++AssignmentIt1;
            ++AssignmentIt2;
            break;
        }
    }
    // There is always one more block than there are calls, so we have to
    // add it
    // separately at the end
    for (auto assgns : makeReverse(*AssignmentIt2)) {
        clause = nestLets(clause, assgns.definitions);
        if (assgns.condition) {
            clause = makeBinOp("=>", assgns.condition, clause);
        }
    }
    for (auto assgns : makeReverse(*AssignmentIt1)) {
        clause = nestLets(clause, assgns.definitions);
        if (assgns.condition) {
            clause = makeBinOp("=>", assgns.condition, clause);
        }
    }
    ++AssignmentIt1;
    ++AssignmentIt2;

    assert(CallIt1 == CallInfo1.rend());
    assert(CallIt2 == CallInfo2.rend());
    assert(AssignmentIt1 == AssignmentBlocks1.rend());
    assert(AssignmentIt2 == AssignmentBlocks2.rend());

    return clause;
}

SMTRef nonmutualSMT(SMTRef endClause,
                    vector<AssignmentCallBlock> assignmentCallBlocks,
                    Program prog, Memory heap) {
    SMTRef clause = endClause;
    const auto splittedAssignments = splitAssignments(assignmentCallBlocks);
    const auto AssignmentBlocks = splittedAssignments.first;
    const auto CallInfos = splittedAssignments.second;
    assert(AssignmentBlocks.size() == CallInfos.size() + 1);
    bool first = true;
    auto callIt = CallInfos.rbegin();
    for (auto assgnsVec : makeReverse(AssignmentBlocks)) {
        if (first) {
            first = false;
        } else {
            clause = nonmutualRecursiveForall(clause, *callIt, prog, heap);
            ++callIt;
        }
        for (auto assgns : makeReverse(assgnsVec)) {
            clause = nestLets(clause, assgns.definitions);
            if (assgns.condition) {
                clause = makeBinOp("=>", assgns.condition, clause);
            }
        }
    }
    return clause;
}

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

SMTRef mutualRecursiveForall(SMTRef clause, CallInfo call1, CallInfo call2,
                             Memory heap) {
    const uint32_t varArgs = static_cast<uint32_t>(call1.args.size()) -
                             call1.fun.getFunctionType()->getNumParams();
    vector<SortedVar> args;
    args.push_back(SortedVar(call1.assignedTo, "Int"));
    args.push_back(SortedVar(call2.assignedTo, "Int"));
    if (heap & HEAP_MASK) {
        args.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        args.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    vector<SMTRef> implArgs;
    vector<SMTRef> preArgs;

    if (call1.externFun) {
        for (auto arg : call1.args) {
            implArgs.push_back(arg);
        }
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("HEAP$1"));
        }
        for (auto arg : call2.args) {
            implArgs.push_back(arg);
        }
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("HEAP$2"));
        }
        implArgs.push_back(name(call1.assignedTo));
        implArgs.push_back(name(call2.assignedTo));
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("HEAP$1_res"));
            implArgs.push_back(name("HEAP$2_res"));
        }

        const SMTRef postInvariant = std::make_shared<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both, call1.callName,
                          varArgs),
            implArgs);
        clause = makeBinOp("=>", postInvariant, clause);
        return make_shared<Forall>(args, clause);
    } else {
        for (auto arg : call1.args) {
            implArgs.push_back(arg);
        }
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("i1"));
            implArgs.push_back(makeBinOp("select", "HEAP$1", "i1"));
        }
        if (heap & STACK_MASK) {
            implArgs.push_back(name("i1_stack"));
            implArgs.push_back(makeBinOp("select", "STACK$1", "i1_stack"));
        }
        for (auto arg : call2.args) {
            implArgs.push_back(arg);
        }
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("i2"));
            implArgs.push_back(makeBinOp("select", "HEAP$2", "i2"));
        }
        if (heap & STACK_MASK) {
            implArgs.push_back(name("i2_stack"));
            implArgs.push_back(makeBinOp("select", "STACK$2", "i2_stack"));
        }
        preArgs.insert(preArgs.end(), implArgs.begin(), implArgs.end());

        implArgs.push_back(name(call1.assignedTo));
        implArgs.push_back(name(call2.assignedTo));
        if (heap & HEAP_MASK) {
            implArgs.push_back(name("i1_res"));
            implArgs.push_back(makeBinOp("select", "HEAP$1_res", "i1_res"));
            implArgs.push_back(name("i2_res"));
            implArgs.push_back(makeBinOp("select", "HEAP$2_res", "i2_res"));
        }
        SMTRef postInvariant = std::make_shared<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both, call1.callName),
            implArgs);
        postInvariant = wrapHeap(postInvariant, heap,
                                 {"i1", "i2", "i1_res", "i2_res", "i1_stack",
                                  "i2_stack", "STACK$1", "STACK$2"});
        clause = makeBinOp("=>", postInvariant, clause);
        clause = make_shared<Forall>(args, clause);
        const auto preInv = wrapHeap(
            std::make_shared<Op>(invariantName(ENTRY_MARK,
                                               ProgramSelection::Both,
                                               call1.callName) +
                                     "_PRE",
                                 preArgs),
            heap, {"i1", "i2", "i1_stack", "i2_stack", "STACK$1", "STACK$2"});
        return makeBinOp("and", preInv, clause);
    }
}

SMTRef nonmutualRecursiveForall(SMTRef clause, CallInfo call, Program prog,
                                Memory heap) {
    vector<SortedVar> forallArgs;
    vector<SMTRef> implArgs;
    vector<SMTRef> preArgs;

    const int progIndex = programIndex(prog);
    const string programS = std::to_string(progIndex);

    const uint32_t varArgs = static_cast<uint32_t>(call.args.size()) -
                             call.fun.getFunctionType()->getNumParams();
    forallArgs.push_back(SortedVar(call.assignedTo, "Int"));
    if (heap & HEAP_MASK) {
        forallArgs.push_back(
            SortedVar("HEAP$" + programS + "_res", "(Array Int Int)"));
    }
    if (call.externFun) {
        if (heap & HEAP_MASK) {
            call.args.push_back(name("HEAP$" + programS));
        }
        call.args.push_back(name(call.assignedTo));
        if (heap & HEAP_MASK) {
            call.args.push_back(name("HEAP$" + programS + "_res"));
        }
        const SMTRef endInvariant =
            make_shared<Op>(invariantName(ENTRY_MARK, asSelection(prog),
                                          call.callName, varArgs),
                            call.args);
        clause = makeBinOp("=>", endInvariant, clause);
        return make_shared<Forall>(forallArgs, clause);
    } else {
        if (heap & HEAP_MASK) {
            call.args.push_back(name("i" + programS));
            call.args.push_back(
                makeBinOp("select", "HEAP$" + programS, "i" + programS));
        }
        if (heap & STACK_MASK) {
            call.args.push_back(name("i" + programS + "_stack"));
            call.args.push_back(
                makeBinOp("select", "STACK$" + programS, "i" + programS));
        }
        implArgs.insert(implArgs.end(), call.args.begin(), call.args.end());
        preArgs.insert(preArgs.end(), call.args.begin(), call.args.end());

        implArgs.push_back(name(call.assignedTo));
        if (heap & HEAP_MASK) {
            if (call.externFun) {
                implArgs.push_back(name("HEAP$" + programS + "_res"));
            } else {
                implArgs.push_back(name("i" + programS + "_res"));
                implArgs.push_back(makeBinOp("select",
                                             "HEAP$" + programS + "_res",
                                             "i" + programS + "_res"));
            }
        }

        SMTRef endInvariant = make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(prog), call.callName),
            implArgs);
        if (heap & STACK_MASK) {
            endInvariant =
                wrapHeap(endInvariant, heap,
                         {"i" + programS, "i" + programS + "_res",
                          "i" + programS + "_stack", "STACK$" + programS});
        } else {
            endInvariant = wrapHeap(endInvariant, heap,
                                    {"i" + programS, "i" + programS + "_res"});
        }
        clause = makeBinOp("=>", endInvariant, clause);
        clause = make_shared<Forall>(forallArgs, clause);
        const auto preInv = std::make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(prog), call.callName) +
                "_PRE",
            preArgs);
        if (heap & STACK_MASK) {
            return makeBinOp("and",
                             wrapHeap(preInv, heap, {"i" + programS,
                                                     "i" + programS + "_stack",
                                                     "STACK$" + programS}),
                             clause);
        } else {
            return makeBinOp("and", wrapHeap(preInv, heap, {"i" + programS}),
                             clause);
        }
    }
}

/// Wrap the clause in a forall
SMTRef forallStartingAt(SMTRef clause, vector<string> freeVars, int blockIndex,
                        ProgramSelection prog, std::string funName, bool main) {
    vector<SortedVar> vars;
    vector<string> preVars;
    Memory heap = 0;
    for (const auto &arg : freeVars) {
        std::smatch matchResult;
        if (std::regex_match(arg, matchResult, HEAP_REGEX)) {
            vars.push_back(SortedVar(arg + "_old", "(Array Int Int)"));
            const string i = matchResult[2];
            string index = "i" + i;
            if (matchResult[1] == "STACK") {
                index += "_stack";
            }
            preVars.push_back(index);
            preVars.push_back("(select " + arg + "_old " + index + ")");
            heap |= HEAP_MASK;
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
        auto preInv = makeOp(invariantName(blockIndex, prog, funName) +
                                 (main ? "_MAIN" : "_PRE"),
                             preVars);
        preInv = wrapHeap(preInv, heap, preVars);
        clause = makeBinOp("=>", preInv, clause);
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

SMTRef inInvariant(const llvm::Function &fun1, const llvm::Function &fun2,
                   SMTRef body, Memory heap, const llvm::Module &mod1,
                   const llvm::Module &mod2, bool strings) {

    vector<SMTRef> args;
    const std::pair<vector<string>, vector<string>> funArgsPair =
        functionArgs(fun1, fun2);
    vector<string> Args1 = funArgsPair.first;
    vector<string> Args2 = funArgsPair.second;
    if (heap & HEAP_MASK) {
        Args1.push_back("HEAP$1");
    }
    if (heap & STACK_MASK) {
        Args1.push_back("STACK$1");
    }
    if (heap & HEAP_MASK) {
        Args2.push_back("HEAP$2");
    }
    if (heap & STACK_MASK) {
        Args2.push_back("STACK$2");
    }
    assert(Args1.size() == Args2.size());
    vector<SortedVar> funArgs;
    vector<string> pointers;
    vector<string> unsignedVariables;
    for (auto &arg : fun1.args()) {
        if (arg.getType()->isPointerTy()) {
            pointers.push_back(arg.getName());
        }
    }
    for (auto &arg : fun2.args()) {
        if (arg.getType()->isPointerTy()) {
            pointers.push_back(arg.getName());
        }
    }
    for (auto arg : Args1) {
        funArgs.push_back(SortedVar(arg, argSort(arg)));
    }
    for (auto arg : Args2) {
        funArgs.push_back(SortedVar(arg, argSort(arg)));
    }
    for (auto argPair : makeZip(Args1, Args2)) {
        const vector<SortedVar> forallArgs = {SortedVar("i", "Int")};
        if (argPair.first == "HEAP$1") {
            args.push_back(make_shared<Forall>(
                forallArgs, makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                      makeBinOp("select", "HEAP$2", "i"))));
        } else {
            args.push_back(makeBinOp("=", argPair.first, argPair.second));
        }
    }
    if (strings) {
        const auto stringConstants1 = stringConstants(mod1, "HEAP$1");
        if (!stringConstants1.empty()) {
            args.push_back(make_shared<Op>("and", stringConstants1));
        }
        const auto stringConstants2 = stringConstants(mod2, "HEAP$2");
        if (!stringConstants2.empty()) {
            args.push_back(make_shared<Op>("and", stringConstants2));
        }
    }
    if (body == nullptr) {
        body = make_shared<Op>("and", args);
    }

    return make_shared<FunDef>("IN_INV", funArgs, "Bool", body);
}

SMTRef outInvariant(SMTRef body, Memory heap) {
    vector<SortedVar> funArgs = {SortedVar("result$1", "Int"),
                                 SortedVar("result$2", "Int")};
    if (heap & HEAP_MASK) {
        funArgs.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
        funArgs.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
    }
    if (body == nullptr) {
        vector<SortedVar> forallArgs;
        forallArgs.push_back(SortedVar("i", "Int"));
        body = makeBinOp("=", "result$1", "result$2");
        if (heap & HEAP_MASK) {
            body =
                makeBinOp("and", body,
                          make_shared<Forall>(
                              forallArgs,
                              makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                        makeBinOp("select", "HEAP$2", "i"))));
        }
    }

    return make_shared<FunDef>("OUT_INV", funArgs, "Bool", body);
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(vector<string> funArgs, vector<string> funArgs1,
                               vector<string> funArgs2, std::string funName,
                               Memory heap) {
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
    if (heap & HEAP_MASK) {
        forallArgs.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        forallArgs.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    args.push_back("result$1");
    args.push_back("result$2");
    if (heap & HEAP_MASK) {
        args.push_back("HEAP$1_res");
        args.push_back("HEAP$2_res");
    }
    heap = false;
    args = resolveHeapReferences(args, "", heap);

    vector<string> outArgs = {"result$1", "result$2"};
    if (heap & HEAP_MASK) {
        outArgs.push_back("HEAP$1_res");
        outArgs.push_back("HEAP$2_res");
    }
    const auto equalResults = makeBinOp(
        "=>", wrapHeap(makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                            funName),
                              args),
                       heap, args),
        makeOp("OUT_INV", outArgs));
    preInvArgs = resolveHeapReferences(preInvArgs, "", heap);
    const auto preInv = wrapHeap(
        makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both, funName) +
                   "_PRE",
               preInvArgs),
        heap, preInvArgs);

    const auto equalArgs =
        makeFunArgsEqual(equalResults, preInv, funArgs1, funArgs2);
    const auto forallInputs = make_shared<Forall>(forallArgs, equalArgs);
    return make_shared<Assert>(forallInputs);
}

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

/// Collect the free variables for the entry block of the PathMap
/// A variable is free if we use it but didn't create it
std::pair<set<string>, std::map<int, set<string>>>
freeVarsForBlock(std::map<int, Paths> pathMap) {
    set<string> freeVars;
    std::map<int, set<string>> constructedIntersection;
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
    return std::make_pair(freeVars, constructedIntersection);
}

std::map<int, vector<string>> freeVars(PathMap map1, PathMap map2,
                                       vector<string> funArgs, Memory heap) {
    std::map<int, set<string>> freeVarsMap;
    std::map<int, vector<string>> freeVarsMapVect;
    std::map<int, std::map<int, set<string>>> constructed;
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

    for (auto it : freeVarsMap) {
        const int index = it.first;
        vector<string> varsVect;
        for (auto var : it.second) {
            varsVect.push_back(var);
        }
        const vector<string> vars1 = filterVars(1, varsVect);
        const vector<string> vars2 = filterVars(2, varsVect);
        vector<string> vars;
        vars.insert(vars.end(), vars1.begin(), vars1.end());
        if (heap & HEAP_MASK) {
            vars.push_back("HEAP$1");
        }
        if (heap & STACK_MASK) {
            vars.push_back("STACK$1");
        }
        vars.insert(vars.end(), vars2.begin(), vars2.end());
        if (heap & HEAP_MASK) {
            vars.push_back("HEAP$2");
        }
        if (heap & STACK_MASK) {
            vars.push_back("STACK$2");
        }
        freeVarsMapVect[index] = vars;
    }
    auto args1 = filterVars(1, funArgs);
    auto args2 = filterVars(2, funArgs);
    if (heap & HEAP_MASK) {
        args1.push_back("HEAP$1");
    }
    if (heap & STACK_MASK) {
        args1.push_back("STACK$1");
    }
    if (heap & HEAP_MASK) {
        args2.push_back("HEAP$2");
    }
    if (heap & STACK_MASK) {
        args2.push_back("STACK$2");
    }
    args1.insert(args1.end(), args2.begin(), args2.end());

    freeVarsMapVect[ENTRY_MARK] = args1;

    return freeVarsMapVect;
}

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

std::pair<vector<string>, vector<string>>
functionArgs(const llvm::Function &fun1, const llvm::Function &fun2) {
    vector<string> args1;
    for (auto &arg : fun1.args()) {
        args1.push_back(arg.getName());
    }
    vector<string> args2;
    for (auto &arg : fun2.args()) {
        args2.push_back(arg.getName());
    }
    return std::make_pair(args1, args2);
}

/// Swap the program index
int swapIndex(int I) {
    assert(I == 1 || I == 2);
    return I == 1 ? 2 : 1;
}

/// Split the assignment blocks on each call
std::pair<vector<vector<AssignmentBlock>>, vector<CallInfo>>
splitAssignments(vector<AssignmentCallBlock> assignmentCallBlocks) {
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
    return make_pair(assignmentBlocks, callInfos);
}

vector<SMTRef> stringConstants(const llvm::Module &mod, string heap) {
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
                            "select", name(heap),
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
                            std::map<int, vector<string>> freeVars,
                            Program prog, Memory heap, bool everythingSigned) {
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
                                      false, heap, everythingSigned);
        auto smt = nonmutualSMT(name("false"), defs, prog, heap);
        dontLoopExprs.push_back(smt);
    }
    if (!dontLoopExprs.empty()) {
        auto andExpr = make_shared<Op>("and", dontLoopExprs);
        clause = makeBinOp("=>", andExpr, clause);
    }
    return clause;
}
