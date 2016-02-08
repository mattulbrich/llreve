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

vector<SMTRef> convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                            shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                            shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                            bool OffByN, vector<SMTRef> &Declarations,
                            Memory Heap, bool Signed) {
    const auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    const auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    checkPathMaps(PathMap1, PathMap2);
    const auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    const auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    const std::string FunName = Fun1.getName();
    const std::pair<vector<string>, vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    vector<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.push_back(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.push_back(Arg);
    }
    std::map<int, vector<string>> FreeVarsMap =
        freeVars(PathMap1, PathMap2, FunArgs, Heap);
    vector<SMTRef> SMTExprs;
    vector<SMTRef> PathExprs;

    // we only need pre invariants for mutual invariants
    const auto Invariants =
        invariantDeclaration(ENTRY_MARK, FreeVarsMap[ENTRY_MARK],
                             ProgramSelection::Both, FunName, Heap);
    Declarations.push_back(Invariants.first);
    Declarations.push_back(Invariants.second);
    const auto Invariants_1 =
        invariantDeclaration(ENTRY_MARK, filterVars(1, FreeVarsMap[ENTRY_MARK]),
                             ProgramSelection::First, FunName, Heap);
    Declarations.push_back(Invariants_1.first);
    Declarations.push_back(Invariants_1.second);
    const auto Invariants_2 =
        invariantDeclaration(ENTRY_MARK, filterVars(2, FreeVarsMap[ENTRY_MARK]),
                             ProgramSelection::Second, FunName, Heap);
    Declarations.push_back(Invariants_2.first);
    Declarations.push_back(Invariants_2.second);

    const auto SynchronizedPaths = synchronizedPaths(
        PathMap1, PathMap2, FreeVarsMap, FunName, Declarations, Heap, Signed);

    // add actual path smts
    PathExprs.insert(PathExprs.end(), SynchronizedPaths.begin(),
                     SynchronizedPaths.end());

    // generate forbidden paths
    PathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    const auto ForbiddenPaths =
        forbiddenPaths(PathMap1, PathMap2, Marked1, Marked2, FreeVarsMap,
                       OffByN, FunName, false, Heap, Signed);
    PathExprs.insert(PathExprs.end(), ForbiddenPaths.begin(),
                     ForbiddenPaths.end());

    if (OffByN) {
        // generate off by n paths
        PathExprs.push_back(make_shared<Comment>("OFF BY N"));
        const auto OffByNPaths = offByNPaths(PathMap1, PathMap2, FreeVarsMap,
                                             FunName, false, Heap, Signed);
        for (auto It : OffByNPaths) {
            int StartIndex = It.first;
            for (auto It2 : It.second) {
                for (auto PathFun : It2.second) {
                    PathExprs.push_back(make_shared<Assert>(forallStartingAt(
                        PathFun(nullptr), FreeVarsMap.at(StartIndex),
                        StartIndex, ProgramSelection::Both, FunName, false)));
                }
            }
        }
    }

    SMTExprs.insert(SMTExprs.end(), PathExprs.begin(), PathExprs.end());

    return SMTExprs;
}

vector<SMTRef> mainAssertion(llvm::Function &Fun1, llvm::Function &Fun2,
                             shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                             shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                             bool OffByN, vector<SMTRef> &Declarations,
                             bool OnlyRec, Memory Heap, bool Signed,
                             bool DontNest) {
    const auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    const auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    checkPathMaps(PathMap1, PathMap2);
    const auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    const auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    std::vector<SMTRef> SMTExprs;
    const std::string FunName = Fun1.getName();
    const std::pair<vector<string>, vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    vector<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.push_back(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.push_back(Arg);
    }
    std::map<int, vector<string>> FreeVarsMap =
        freeVars(PathMap1, PathMap2, FunArgs, Heap);

    if (OnlyRec) {
        SMTExprs.push_back(equalInputsEqualOutputs(
            FreeVarsMap[ENTRY_MARK], filterVars(1, FreeVarsMap[ENTRY_MARK]),
            filterVars(2, FreeVarsMap[ENTRY_MARK]), FunName, Heap));
        return SMTExprs;
    }

    auto SynchronizedPaths = mainSynchronizedPaths(
        PathMap1, PathMap2, FreeVarsMap, FunName, Declarations, Heap, Signed);
    const auto ForbiddenPaths =
        forbiddenPaths(PathMap1, PathMap2, Marked1, Marked2, FreeVarsMap,
                       OffByN, FunName, true, Heap, Signed);
    if (OffByN) {
        SMTExprs.push_back(make_shared<Comment>("offbyn main"));
        const auto OffByNPaths = offByNPaths(PathMap1, PathMap2, FreeVarsMap,
                                             FunName, true, Heap, Signed);
        SynchronizedPaths = mergePathFuns(SynchronizedPaths, OffByNPaths);
    }
    auto TransposedPaths = transpose(SynchronizedPaths);
    // remove cycles
    for (auto &It : TransposedPaths) {
        It.second.erase(It.first);
    }
    for (auto It : SynchronizedPaths) {
        const int StartIndex = It.first;
        std::vector<SMTRef> PathsStartingHere;
        for (auto It2 : It.second) {
            const int EndIndex = It2.first;
            auto EndInvariant = mainInvariant(
                EndIndex, FreeVarsMap.at(EndIndex), FunName, Heap);
            for (auto PathFun : It2.second) {
                PathsStartingHere.push_back(PathFun(EndInvariant));
            }
        }
        auto Clause =
            forallStartingAt(make_shared<Op>("and", PathsStartingHere),
                             FreeVarsMap.at(StartIndex), StartIndex,
                             ProgramSelection::Both, FunName, true);
        if (!DontNest &&
            (TransposedPaths.find(StartIndex) != TransposedPaths.end())) {
            if (TransposedPaths.at(StartIndex).size() == 1) {
                auto It = TransposedPaths.at(StartIndex).begin();
                const int ComingFrom = It->first;
                if (It->second.size() == 1) {
                    const auto NestFun = It->second.at(0);
                    Clause = forallStartingAt(
                        NestFun(Clause), FreeVarsMap.at(ComingFrom), ComingFrom,
                        ProgramSelection::Both, FunName, true);
                }
            }
        }
        SMTExprs.push_back(make_shared<Assert>(Clause));
    }
    SMTExprs.push_back(make_shared<Comment>("forbidden main"));
    SMTExprs.insert(SMTExprs.end(), ForbiddenPaths.begin(),
                    ForbiddenPaths.end());
    SMTExprs.push_back(make_shared<Comment>("end"));
    return SMTExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

vector<SMTRef> synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                                 std::map<int, vector<string>> FreeVarsMap,
                                 std::string FunName,
                                 vector<SMTRef> &Declarations, Memory Heap,
                                 bool Signed) {
    vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        const int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            // ignore entry node
            const auto Invariants =
                invariantDeclaration(StartIndex, FreeVarsMap.at(StartIndex),
                                     ProgramSelection::Both, FunName, Heap);
            Declarations.push_back(Invariants.first);
            Declarations.push_back(Invariants.second);
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            const auto Paths = PathMap2.at(StartIndex).at(EndIndex);
            for (auto &Path1 : InnerPathMapIt.second) {
                for (auto &Path2 : Paths) {
                    const auto EndInvariant = invariant(
                        StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                        FreeVarsMap.at(EndIndex), ProgramSelection::Both,
                        FunName, Heap);
                    const auto Defs1 = assignmentsOnPath(
                        Path1, Program::First, FreeVarsMap.at(StartIndex),
                        EndIndex == EXIT_MARK, Heap, Signed);
                    const auto Defs2 = assignmentsOnPath(
                        Path2, Program::Second, FreeVarsMap.at(StartIndex),
                        EndIndex == EXIT_MARK, Heap, Signed);
                    PathExprs.push_back(make_shared<Assert>(forallStartingAt(
                        interleaveAssignments(EndInvariant, Defs1, Defs2, Heap),
                        FreeVarsMap.at(StartIndex), StartIndex,
                        ProgramSelection::Both, FunName, false)));
                }
            }
        }
    }
    nonmutualPaths(PathMap1, PathExprs, FreeVarsMap, Program::First, FunName,
                   Declarations, Heap, Signed);
    nonmutualPaths(PathMap2, PathExprs, FreeVarsMap, Program::Second, FunName,
                   Declarations, Heap, Signed);

    return PathExprs;
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
mainSynchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                      std::map<int, vector<string>> FreeVarsMap,
                      std::string FunName, vector<SMTRef> &Declarations,
                      Memory Heap, bool Signed) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> PathFuns;
    for (const auto &PathMapIt : PathMap1) {
        const int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            // ignore entry node
            const auto Invariant =
                mainInvariantDeclaration(StartIndex, FreeVarsMap.at(StartIndex),
                                         ProgramSelection::Both, FunName);
            Declarations.push_back(Invariant);
        }
        for (const auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            if (PathMap2.at(StartIndex).find(EndIndex) !=
                PathMap2.at(StartIndex).end()) {
                const auto Paths = PathMap2.at(StartIndex).at(EndIndex);
                for (const auto &Path1 : InnerPathMapIt.second) {
                    for (const auto &Path2 : Paths) {
                        const auto EndInvariant = mainInvariant(
                            EndIndex, FreeVarsMap.at(EndIndex), FunName, Heap);
                        const auto Defs1 = assignmentsOnPath(
                            Path1, Program::First, FreeVarsMap.at(StartIndex),
                            EndIndex == EXIT_MARK, Heap, Signed);
                        const auto Defs2 = assignmentsOnPath(
                            Path2, Program::Second, FreeVarsMap.at(StartIndex),
                            EndIndex == EXIT_MARK, Heap, Signed);
                        PathFuns[StartIndex][EndIndex].push_back(
                            [=](SMTRef End) {
                                return interleaveAssignments(End, Defs1, Defs2,
                                                             Heap);
                            });
                    }
                }
            }
        }
    }

    return PathFuns;
}

vector<SMTRef> forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
                              BidirBlockMarkMap Marked1,
                              BidirBlockMarkMap Marked2,
                              std::map<int, vector<string>> FreeVarsMap,
                              bool OffByN, std::string FunName, bool Main,
                              Memory Heap, bool Signed) {
    vector<SMTRef> PathExprs;
    for (const auto &PathMapIt : PathMap1) {
        const int StartIndex = PathMapIt.first;
        for (const auto &InnerPathMapIt1 : PathMapIt.second) {
            const int EndIndex1 = InnerPathMapIt1.first;
            for (auto &InnerPathMapIt2 : PathMap2.at(StartIndex)) {
                const auto EndIndex2 = InnerPathMapIt2.first;
                if (EndIndex1 != EndIndex2) {
                    for (const auto &Path1 : InnerPathMapIt1.second) {
                        for (const auto &Path2 : InnerPathMapIt2.second) {
                            const auto EndBlock1 = lastBlock(Path1);
                            const auto EndBlock2 = lastBlock(Path2);
                            const auto EndIndices1 =
                                Marked1.BlockToMarksMap[EndBlock1];
                            const auto EndIndices2 =
                                Marked2.BlockToMarksMap[EndBlock2];
                            if (!OffByN ||
                                ((StartIndex != EndIndex1 && // no circles
                                  StartIndex != EndIndex2) &&
                                 intersection(EndIndices1, EndIndices2)
                                     .empty())) {
                                const auto Smt2 = assignmentsOnPath(
                                    Path2, Program::Second,
                                    FreeVarsMap.at(StartIndex),
                                    EndIndex2 == EXIT_MARK, Heap, Signed);
                                const auto Smt1 = assignmentsOnPath(
                                    Path1, Program::First,
                                    FreeVarsMap.at(StartIndex),
                                    EndIndex1 == EXIT_MARK, Heap, Signed);
                                // We need to interleave here, because otherwise
                                // extern functions are not matched
                                const auto SMT = interleaveAssignments(
                                    name("false"), Smt1, Smt2, Heap);
                                PathExprs.push_back(
                                    make_shared<Assert>(forallStartingAt(
                                        SMT, FreeVarsMap.at(StartIndex),
                                        StartIndex, ProgramSelection::Both,
                                        FunName, Main)));
                            }
                        }
                    }
                }
            }
        }
    }
    return PathExprs;
}

void nonmutualPaths(PathMap PathMap, vector<SMTRef> &PathExprs,
                    std::map<int, vector<string>> FreeVarsMap, Program Prog,
                    std::string FunName, vector<SMTRef> &Declarations,
                    Memory Heap, bool Signed) {
    const int ProgramIndex = programIndex(Prog);
    for (const auto &PathMapIt : PathMap) {
        const int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            const auto Invariants = invariantDeclaration(
                StartIndex,
                filterVars(ProgramIndex, FreeVarsMap.at(StartIndex)),
                asSelection(Prog), FunName, Heap);
            Declarations.push_back(Invariants.first);
            Declarations.push_back(Invariants.second);
        }
        for (const auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            for (const auto &Path : InnerPathMapIt.second) {
                const auto EndInvariant1 = invariant(
                    StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                    FreeVarsMap.at(EndIndex), asSelection(Prog), FunName, Heap);
                const auto Defs =
                    assignmentsOnPath(Path, Prog, FreeVarsMap.at(StartIndex),
                                      EndIndex == EXIT_MARK, Heap, Signed);
                PathExprs.push_back(make_shared<Assert>(forallStartingAt(
                    nonmutualSMT(EndInvariant1, Defs, Prog, Heap),
                    filterVars(ProgramIndex, FreeVarsMap.at(StartIndex)),
                    StartIndex, asSelection(Prog), FunName, false)));
            }
        }
    }
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
offByNPaths(PathMap PathMap1, PathMap PathMap2,
            std::map<int, vector<string>> FreeVarsMap, std::string FunName,
            bool Main, Memory Heap, bool Signed) {
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> PathFuns;
    vector<SMTRef> Paths;
    const auto FirstPaths =
        offByNPathsOneDir(PathMap1, PathMap2, FreeVarsMap, Program::First,
                          FunName, Main, Heap, Signed);
    const auto SecondPaths =
        offByNPathsOneDir(PathMap2, PathMap1, FreeVarsMap, Program::Second,
                          FunName, Main, Heap, Signed);
    return mergePathFuns(FirstPaths, SecondPaths);
}

map<int, map<int, vector<function<SMTRef(SMTRef)>>>>
offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                  std::map<int, vector<string>> FreeVarsMap, Program Prog,
                  std::string FunName, bool Main, Memory Heap, bool Signed) {
    const int ProgramIndex = programIndex(Prog);
    map<int, map<int, vector<function<SMTRef(SMTRef)>>>> PathFuns;
    for (const auto &PathMapIt : PathMap_) {
        const int StartIndex = PathMapIt.first;
        for (const auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            if (StartIndex == EndIndex) {
                // we found a loop
                for (const auto &Path : InnerPathMapIt.second) {
                    const auto EndArgs2 = filterVars(
                        swapIndex(ProgramIndex), FreeVarsMap.at(StartIndex));
                    const auto EndArgs =
                        filterVars(ProgramIndex, FreeVarsMap.at(StartIndex));
                    vector<string> Args;
                    if (Prog == Program::First) {
                        for (auto Arg : EndArgs) {
                            Args.push_back(Arg);
                        }
                        for (auto Arg : EndArgs2) {
                            Args.push_back(Arg + "_old");
                        }

                    } else {
                        for (auto Arg : EndArgs2) {
                            Args.push_back(Arg + "_old");
                        }
                        for (auto Arg : EndArgs) {
                            Args.push_back(Arg);
                        }
                    }
                    SMTRef EndInvariant;
                    if (Main) {
                        EndInvariant =
                            mainInvariant(StartIndex, Args, FunName, Heap);
                    } else {
                        EndInvariant = invariant(
                            StartIndex, StartIndex, FreeVarsMap.at(StartIndex),
                            Args, ProgramSelection::Both, FunName, Heap);
                    }
                    const auto DontLoopInvariant = dontLoopInvariant(
                        EndInvariant, StartIndex, OtherPathMap, FreeVarsMap,
                        swapProgram(Prog), Heap, Signed);
                    const auto Defs =
                        assignmentsOnPath(Path, Prog, FreeVarsMap.at(EndIndex),
                                          EndIndex == EXIT_MARK, Heap, Signed);
                    PathFuns[StartIndex][StartIndex].push_back(
                        [=](SMTRef /*unused*/) {
                            return nonmutualSMT(DontLoopInvariant, Defs, Prog,
                                                Heap);
                        });
                }
            }
        }
    }
    return PathFuns;
}

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

vector<AssignmentCallBlock> assignmentsOnPath(Path Path, Program Prog,
                                              vector<std::string> FreeVars,
                                              bool ToEnd, Memory Heap,
                                              bool Signed) {
    const int ProgramIndex = programIndex(Prog);
    const auto FilteredFreeVars = filterVars(ProgramIndex, FreeVars);

    vector<AssignmentCallBlock> AllDefs;
    set<string> Constructed;
    vector<CallInfo> CallInfos;

    // Set the new values to the initial values
    vector<DefOrCallInfo> OldDefs;
    for (auto Var : FilteredFreeVars) {
        OldDefs.push_back(DefOrCallInfo(
            std::make_shared<Assignment>(Var, name(Var + "_old"))));
    }
    AllDefs.push_back(AssignmentCallBlock(OldDefs, nullptr));

    // First block of path, this is special, because we don’t have a
    // previous
    // block so we can’t resolve phi nodes
    const auto StartDefs =
        blockAssignments(*Path.Start, nullptr, false, Prog, Heap, Signed);
    AllDefs.push_back(AssignmentCallBlock(StartDefs, nullptr));

    auto Prev = Path.Start;

    // Rest of the path
    unsigned int i = 0;
    for (auto Edge : Path.Edges) {
        i++;
        const bool Last = i == Path.Edges.size();
        const auto Defs = blockAssignments(*Edge.Block, Prev, Last && !ToEnd,
                                           Prog, Heap, Signed);
        AllDefs.push_back(AssignmentCallBlock(
            Defs, Edge.Cond == nullptr ? nullptr : Edge.Cond->toSmt()));
        Prev = Edge.Block;
    }
    return AllDefs;
}

SMTRef interleaveAssignments(SMTRef EndClause,
                             vector<AssignmentCallBlock> AssignmentCallBlocks1,
                             vector<AssignmentCallBlock> AssignmentCallBlocks2,
                             Memory Heap) {
    SMTRef Clause = EndClause;
    const auto SplitAssignments1 = splitAssignments(AssignmentCallBlocks1);
    const auto SplitAssignments2 = splitAssignments(AssignmentCallBlocks2);
    const auto AssignmentBlocks1 = SplitAssignments1.first;
    const auto AssignmentBlocks2 = SplitAssignments2.first;
    const auto CallInfo1 = SplitAssignments1.second;
    const auto CallInfo2 = SplitAssignments2.second;

    const auto InterleaveSteps = matchFunCalls(CallInfo1, CallInfo2);

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
    for (InterleaveStep Step : makeReverse(InterleaveSteps)) {
        switch (Step) {
        case InterleaveStep::StepFirst:
            for (auto Assgns : makeReverse(*AssignmentIt1)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            Clause = nonmutualRecursiveForall(Clause, *CallIt1, Program::First,
                                              Heap);
            ++CallIt1;
            ++AssignmentIt1;
            break;
        case InterleaveStep::StepSecond:
            for (auto Assgns : makeReverse(*AssignmentIt2)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            Clause = nonmutualRecursiveForall(Clause, *CallIt2, Program::Second,
                                              Heap);
            ++CallIt2;
            ++AssignmentIt2;
            break;
        case InterleaveStep::StepBoth:
            assert(CallIt1->CallName == CallIt2->CallName);
            for (auto Assgns : makeReverse(*AssignmentIt2)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            for (auto Assgns : makeReverse(*AssignmentIt1)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            Clause = mutualRecursiveForall(Clause, *CallIt1, *CallIt2, Heap);
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
    for (auto Assgns : makeReverse(*AssignmentIt2)) {
        Clause = nestLets(Clause, Assgns.Definitions);
        if (Assgns.Condition) {
            Clause = makeBinOp("=>", Assgns.Condition, Clause);
        }
    }
    for (auto Assgns : makeReverse(*AssignmentIt1)) {
        Clause = nestLets(Clause, Assgns.Definitions);
        if (Assgns.Condition) {
            Clause = makeBinOp("=>", Assgns.Condition, Clause);
        }
    }
    ++AssignmentIt1;
    ++AssignmentIt2;

    assert(CallIt1 == CallInfo1.rend());
    assert(CallIt2 == CallInfo2.rend());
    assert(AssignmentIt1 == AssignmentBlocks1.rend());
    assert(AssignmentIt2 == AssignmentBlocks2.rend());

    return Clause;
}

SMTRef nonmutualSMT(SMTRef EndClause,
                    vector<AssignmentCallBlock> AssignmentCallBlocks,
                    Program Prog, Memory Heap) {
    SMTRef Clause = EndClause;
    const auto SplitAssignments = splitAssignments(AssignmentCallBlocks);
    const auto AssignmentBlocks = SplitAssignments.first;
    const auto CallInfos = SplitAssignments.second;
    assert(AssignmentBlocks.size() == CallInfos.size() + 1);
    bool first = true;
    auto CallIt = CallInfos.rbegin();
    for (auto AssgnsVec : makeReverse(AssignmentBlocks)) {
        if (first) {
            first = false;
        } else {
            Clause = nonmutualRecursiveForall(Clause, *CallIt, Prog, Heap);
            ++CallIt;
        }
        for (auto Assgns : makeReverse(AssgnsVec)) {
            Clause = nestLets(Clause, Assgns.Definitions);
            if (Assgns.Condition) {
                Clause = makeBinOp("=>", Assgns.Condition, Clause);
            }
        }
    }
    return Clause;
}

/* -------------------------------------------------------------------------- */
// Functions to generate various foralls

SMTRef mutualRecursiveForall(SMTRef Clause, CallInfo Call1, CallInfo Call2,
                             Memory Heap) {
    const uint32_t VarArgs = static_cast<uint32_t>(Call1.Args.size()) -
                             Call1.Fun.getFunctionType()->getNumParams();
    vector<SortedVar> Args;
    Args.push_back(SortedVar(Call1.AssignedTo, "Int"));
    Args.push_back(SortedVar(Call2.AssignedTo, "Int"));
    if (Heap & HEAP_MASK) {
        Args.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        Args.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    vector<SMTRef> ImplArgs;
    vector<SMTRef> PreArgs;

    if (Call1.Extern) {
        for (auto Arg : Call1.Args) {
            ImplArgs.push_back(Arg);
        }
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("HEAP$1"));
        }
        for (auto Arg : Call2.Args) {
            ImplArgs.push_back(Arg);
        }
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("HEAP$2"));
        }
        ImplArgs.push_back(name(Call1.AssignedTo));
        ImplArgs.push_back(name(Call2.AssignedTo));
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("HEAP$1_res"));
            ImplArgs.push_back(name("HEAP$2_res"));
        }

        const SMTRef PostInvariant = std::make_shared<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both, Call1.CallName,
                          VarArgs),
            ImplArgs);
        Clause = makeBinOp("=>", PostInvariant, Clause);
        return make_shared<Forall>(Args, Clause);
    } else {
        for (auto Arg : Call1.Args) {
            ImplArgs.push_back(Arg);
        }
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("i1"));
            ImplArgs.push_back(makeBinOp("select", "HEAP$1", "i1"));
        }
        if (Heap & STACK_MASK) {
            ImplArgs.push_back(name("i1_stack"));
            ImplArgs.push_back(makeBinOp("select", "STACK$1", "i1_stack"));
        }
        for (auto Arg : Call2.Args) {
            ImplArgs.push_back(Arg);
        }
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("i2"));
            ImplArgs.push_back(makeBinOp("select", "HEAP$2", "i2"));
        }
        if (Heap & STACK_MASK) {
            ImplArgs.push_back(name("i2_stack"));
            ImplArgs.push_back(makeBinOp("select", "STACK$2", "i2_stack"));
        }
        PreArgs.insert(PreArgs.end(), ImplArgs.begin(), ImplArgs.end());

        ImplArgs.push_back(name(Call1.AssignedTo));
        ImplArgs.push_back(name(Call2.AssignedTo));
        if (Heap & HEAP_MASK) {
            ImplArgs.push_back(name("i1_res"));
            ImplArgs.push_back(makeBinOp("select", "HEAP$1_res", "i1_res"));
            ImplArgs.push_back(name("i2_res"));
            ImplArgs.push_back(makeBinOp("select", "HEAP$2_res", "i2_res"));
        }
        SMTRef PostInvariant = std::make_shared<Op>(
            invariantName(ENTRY_MARK, ProgramSelection::Both, Call1.CallName),
            ImplArgs);
        PostInvariant = wrapHeap(PostInvariant, Heap,
                                 {"i1", "i2", "i1_res", "i2_res", "i1_stack",
                                  "i2_stack", "STACK$1", "STACK$2"});
        Clause = makeBinOp("=>", PostInvariant, Clause);
        Clause = make_shared<Forall>(Args, Clause);
        const auto PreInv = wrapHeap(
            std::make_shared<Op>(invariantName(ENTRY_MARK,
                                               ProgramSelection::Both,
                                               Call1.CallName) +
                                     "_PRE",
                                 PreArgs),
            Heap, {"i1", "i2", "i1_stack", "i2_stack", "STACK$1", "STACK$2"});
        return makeBinOp("and", PreInv, Clause);
    }
}

SMTRef nonmutualRecursiveForall(SMTRef Clause, CallInfo Call, Program Prog,
                                Memory Heap) {
    vector<SortedVar> ForallArgs;
    vector<SMTRef> ImplArgs;
    vector<SMTRef> PreArgs;

    const int ProgramIndex = programIndex(Prog);
    const string ProgramS = std::to_string(ProgramIndex);

    const uint32_t VarArgs = static_cast<uint32_t>(Call.Args.size()) -
                             Call.Fun.getFunctionType()->getNumParams();
    ForallArgs.push_back(SortedVar(Call.AssignedTo, "Int"));
    if (Heap & HEAP_MASK) {
        ForallArgs.push_back(
            SortedVar("HEAP$" + ProgramS + "_res", "(Array Int Int)"));
    }
    if (Call.Extern) {
        if (Heap & HEAP_MASK) {
            Call.Args.push_back(name("HEAP$" + ProgramS));
        }
        Call.Args.push_back(name(Call.AssignedTo));
        if (Heap & HEAP_MASK) {
            Call.Args.push_back(name("HEAP$" + ProgramS + "_res"));
        }
        const SMTRef EndInvariant =
            make_shared<Op>(invariantName(ENTRY_MARK, asSelection(Prog),
                                          Call.CallName, VarArgs),
                            Call.Args);
        Clause = makeBinOp("=>", EndInvariant, Clause);
        return make_shared<Forall>(ForallArgs, Clause);
    } else {
        if (Heap & HEAP_MASK) {
            Call.Args.push_back(name("i" + ProgramS));
            Call.Args.push_back(
                makeBinOp("select", "HEAP$" + ProgramS, "i" + ProgramS));
        }
        if (Heap & STACK_MASK) {
            Call.Args.push_back(name("i" + ProgramS + "_stack"));
            Call.Args.push_back(
                makeBinOp("select", "STACK$" + ProgramS, "i" + ProgramS));
        }
        ImplArgs.insert(ImplArgs.end(), Call.Args.begin(), Call.Args.end());
        PreArgs.insert(PreArgs.end(), Call.Args.begin(), Call.Args.end());

        ImplArgs.push_back(name(Call.AssignedTo));
        if (Heap & HEAP_MASK) {
            if (Call.Extern) {
                ImplArgs.push_back(name("HEAP$" + ProgramS + "_res"));
            } else {
                ImplArgs.push_back(name("i" + ProgramS + "_res"));
                ImplArgs.push_back(makeBinOp("select",
                                             "HEAP$" + ProgramS + "_res",
                                             "i" + ProgramS + "_res"));
            }
        }

        SMTRef EndInvariant = make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(Prog), Call.CallName),
            ImplArgs);
        if (Heap & STACK_MASK) {
            EndInvariant =
                wrapHeap(EndInvariant, Heap,
                         {"i" + ProgramS, "i" + ProgramS + "_res",
                          "i" + ProgramS + "_stack", "STACK$" + ProgramS});
        } else {
            EndInvariant = wrapHeap(EndInvariant, Heap,
                                    {"i" + ProgramS, "i" + ProgramS + "_res"});
        }
        Clause = makeBinOp("=>", EndInvariant, Clause);
        Clause = make_shared<Forall>(ForallArgs, Clause);
        const auto PreInv = std::make_shared<Op>(
            invariantName(ENTRY_MARK, asSelection(Prog), Call.CallName) +
                "_PRE",
            PreArgs);
        if (Heap & STACK_MASK) {
            return makeBinOp("and",
                             wrapHeap(PreInv, Heap, {"i" + ProgramS,
                                                     "i" + ProgramS + "_stack",
                                                     "STACK$" + ProgramS}),
                             Clause);
        } else {
            return makeBinOp("and", wrapHeap(PreInv, Heap, {"i" + ProgramS}),
                             Clause);
        }
    }
}

/// Wrap the clause in a forall
SMTRef forallStartingAt(SMTRef Clause, vector<string> FreeVars, int BlockIndex,
                        ProgramSelection For, std::string FunName, bool Main) {
    vector<SortedVar> Vars;
    vector<string> PreVars;
    Memory Heap = 0;
    for (const auto &Arg : FreeVars) {
        std::smatch MatchResult;
        if (std::regex_match(Arg, MatchResult, HEAP_REGEX)) {
            Vars.push_back(SortedVar(Arg + "_old", "(Array Int Int)"));
            const string I = MatchResult[2];
            string index = "i" + I;
            if (MatchResult[1] == "STACK") {
                index += "_stack";
            }
            PreVars.push_back(index);
            PreVars.push_back("(select " + Arg + "_old " + index + ")");
            Heap |= HEAP_MASK;
        } else {
            Vars.push_back(SortedVar(Arg + "_old", "Int"));
            PreVars.push_back(Arg + "_old");
        }
    }

    if (Vars.empty()) {
        return Clause;
    }

    SMTRef PreInv;
    if (Main && BlockIndex == ENTRY_MARK) {
        vector<string> Args;
        for (auto Arg : FreeVars) {
            Args.push_back(Arg + "_old");
        }
        Clause = makeBinOp("=>", makeOp("IN_INV", Args), Clause);
    } else {
        auto PreInv = makeOp(invariantName(BlockIndex, For, FunName) +
                                 (Main ? "_MAIN" : "_PRE"),
                             PreVars);
        PreInv = wrapHeap(PreInv, Heap, PreVars);
        Clause = makeBinOp("=>", PreInv, Clause);
    }

    return make_shared<Forall>(Vars, Clause);
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SMTRef makeFunArgsEqual(SMTRef Clause, SMTRef PreClause, vector<string> Args1,
                        vector<string> Args2) {
    vector<string> Args;
    Args.insert(Args.end(), Args1.begin(), Args1.end());
    Args.insert(Args.end(), Args2.begin(), Args2.end());
    assert(Args1.size() == Args2.size());

    auto InInv = makeOp("IN_INV", Args);

    return makeBinOp("=>", InInv, makeBinOp("and", Clause, PreClause));
}

SMTRef inInvariant(const llvm::Function &Fun1, const llvm::Function &Fun2,
                   SMTRef Body, Memory Heap, const llvm::Module &Mod1,
                   const llvm::Module &Mod2, bool Strings) {

    vector<SMTRef> Args;
    const std::pair<vector<string>, vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    vector<string> Args1 = FunArgsPair.first;
    vector<string> Args2 = FunArgsPair.second;
    if (Heap & HEAP_MASK) {
        Args1.push_back("HEAP$1");
    }
    if (Heap & STACK_MASK) {
        Args1.push_back("STACK$1");
    }
    if (Heap & HEAP_MASK) {
        Args2.push_back("HEAP$2");
    }
    if (Heap & STACK_MASK) {
        Args2.push_back("STACK$2");
    }
    assert(Args1.size() == Args2.size());
    vector<SortedVar> FunArgs;
    vector<string> Pointers;
    vector<string> Unsigned;
    for (auto &Arg : Fun1.args()) {
        if (Arg.getType()->isPointerTy()) {
            Pointers.push_back(Arg.getName());
        }
    }
    for (auto &Arg : Fun2.args()) {
        if (Arg.getType()->isPointerTy()) {
            Pointers.push_back(Arg.getName());
        }
    }
    for (auto Arg : Args1) {
        FunArgs.push_back(SortedVar(Arg, argSort(Arg)));
    }
    for (auto Arg : Args2) {
        FunArgs.push_back(SortedVar(Arg, argSort(Arg)));
    }
    for (auto ArgPair : makeZip(Args1, Args2)) {
        const vector<SortedVar> ForallArgs = {SortedVar("i", "Int")};
        if (ArgPair.first == "HEAP$1") {
            Args.push_back(make_shared<Forall>(
                ForallArgs, makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                      makeBinOp("select", "HEAP$2", "i"))));
        } else {
            Args.push_back(makeBinOp("=", ArgPair.first, ArgPair.second));
        }
    }
    if (Strings) {
        const auto StringConstants1 = stringConstants(Mod1, "HEAP$1");
        if (!StringConstants1.empty()) {
            Args.push_back(make_shared<Op>("and", StringConstants1));
        }
        const auto StringConstants2 = stringConstants(Mod2, "HEAP$2");
        if (!StringConstants2.empty()) {
            Args.push_back(make_shared<Op>("and", StringConstants2));
        }
    }
    if (Body == nullptr) {
        Body = make_shared<Op>("and", Args);
    }

    return make_shared<FunDef>("IN_INV", FunArgs, "Bool", Body);
}

SMTRef outInvariant(SMTRef Body, Memory Heap) {
    vector<SortedVar> FunArgs = {SortedVar("result$1", "Int"),
                                 SortedVar("result$2", "Int")};
    if (Heap & HEAP_MASK) {
        FunArgs.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
        FunArgs.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
    }
    if (Body == nullptr) {
        vector<SortedVar> ForallArgs;
        ForallArgs.push_back(SortedVar("i", "Int"));
        Body = makeBinOp("=", "result$1", "result$2");
        if (Heap & HEAP_MASK) {
            Body =
                makeBinOp("and", Body,
                          make_shared<Forall>(
                              ForallArgs,
                              makeBinOp("=", makeBinOp("select", "HEAP$1", "i"),
                                        makeBinOp("select", "HEAP$2", "i"))));
        }
    }

    return make_shared<FunDef>("OUT_INV", FunArgs, "Bool", Body);
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(vector<string> FunArgs, vector<string> FunArgs1,
                               vector<string> FunArgs2, std::string FunName,
                               Memory Heap) {
    vector<SortedVar> ForallArgs;
    vector<string> Args;
    vector<string> PreInvArgs;
    Args.insert(Args.end(), FunArgs.begin(), FunArgs.end());
    PreInvArgs = Args;

    for (auto Arg : FunArgs) {
        ForallArgs.push_back(SortedVar(Arg, argSort(Arg)));
    }
    ForallArgs.push_back(SortedVar("result$1", "Int"));
    ForallArgs.push_back(SortedVar("result$2", "Int"));
    if (Heap & HEAP_MASK) {
        ForallArgs.push_back(SortedVar("HEAP$1_res", "(Array Int Int)"));
        ForallArgs.push_back(SortedVar("HEAP$2_res", "(Array Int Int)"));
    }
    Args.push_back("result$1");
    Args.push_back("result$2");
    if (Heap & HEAP_MASK) {
        Args.push_back("HEAP$1_res");
        Args.push_back("HEAP$2_res");
    }
    Heap = false;
    Args = resolveHeapReferences(Args, "", Heap);

    vector<string> OutArgs = {"result$1", "result$2"};
    if (Heap & HEAP_MASK) {
        OutArgs.push_back("HEAP$1_res");
        OutArgs.push_back("HEAP$2_res");
    }
    const auto EqualResults = makeBinOp(
        "=>", wrapHeap(makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both,
                                            FunName),
                              Args),
                       Heap, Args),
        makeOp("OUT_INV", OutArgs));
    PreInvArgs = resolveHeapReferences(PreInvArgs, "", Heap);
    const auto PreInv = wrapHeap(
        makeOp(invariantName(ENTRY_MARK, ProgramSelection::Both, FunName) +
                   "_PRE",
               PreInvArgs),
        Heap, PreInvArgs);

    const auto EqualArgs =
        makeFunArgsEqual(EqualResults, PreInv, FunArgs1, FunArgs2);
    const auto ForallInputs = make_shared<Forall>(ForallArgs, EqualArgs);
    return make_shared<Assert>(ForallInputs);
}

/* -------------------------------------------------------------------------- */
// Functions  related to the search for free variables

/// Collect the free variables for the entry block of the PathMap
/// A variable is free if we use it but didn't create it
std::pair<set<string>, std::map<int, set<string>>>
freeVarsForBlock(std::map<int, Paths> PathMap) {
    set<string> FreeVars;
    std::map<int, set<string>> ConstructedIntersection;
    for (const auto &Paths : PathMap) {
        for (const auto &Path : Paths.second) {
            const llvm::BasicBlock *Prev = Path.Start;
            set<string> Constructed;

            // the first block is special since we can't resolve phi
            // nodes here
            for (auto &Instr : *Path.Start) {
                Constructed.insert(Instr.getName());
                if (llvm::isa<llvm::PHINode>(Instr)) {
                    FreeVars.insert(Instr.getName());
                    continue;
                }
                if (const auto CallInst =
                        llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                    for (unsigned int i = 0; i < CallInst->getNumArgOperands();
                         i++) {
                        const auto Arg = CallInst->getArgOperand(i);
                        if (!Arg->getName().empty() &&
                            Constructed.find(Arg->getName()) ==
                                Constructed.end()) {
                            FreeVars.insert(Arg->getName());
                        }
                    }
                    continue;
                }
                for (const auto Op : Instr.operand_values()) {
                    if (Constructed.find(Op->getName()) == Constructed.end() &&
                        !Op->getName().empty()) {
                        FreeVars.insert(Op->getName());
                    }
                }
            }

            // now deal with the rest
            for (const auto &Edge : Path.Edges) {
                for (auto &Instr : *Edge.Block) {
                    Constructed.insert(Instr.getName());
                    if (const auto PhiInst =
                            llvm::dyn_cast<llvm::PHINode>(&Instr)) {
                        const auto Incoming =
                            PhiInst->getIncomingValueForBlock(Prev);
                        if (Constructed.find(Incoming->getName()) ==
                                Constructed.end() &&
                            !Incoming->getName().empty()) {
                            FreeVars.insert(Incoming->getName());
                        }
                        continue;
                    }
                    if (const auto CallInst =
                            llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                        for (unsigned int i = 0;
                             i < CallInst->getNumArgOperands(); i++) {
                            const auto Arg = CallInst->getArgOperand(i);
                            if (!Arg->getName().empty() &&
                                Constructed.find(Arg->getName()) ==
                                    Constructed.end()) {
                                FreeVars.insert(Arg->getName());
                            }
                        }
                        continue;
                    }
                    for (const auto Op : Instr.operand_values()) {
                        if (Constructed.find(Op->getName()) ==
                                Constructed.end() &&
                            !Op->getName().empty()) {
                            FreeVars.insert(Op->getName());
                        }
                    }
                }
                Prev = Edge.Block;
            }

            set<string> NewConstructedIntersection;
            if (ConstructedIntersection.find(Paths.first) ==
                ConstructedIntersection.end()) {
                ConstructedIntersection.insert(
                    make_pair(Paths.first, Constructed));
                ;
            } else {
                std::set_intersection(
                    Constructed.begin(), Constructed.end(),
                    ConstructedIntersection.at(Paths.first).begin(),
                    ConstructedIntersection.at(Paths.first).end(),
                    inserter(NewConstructedIntersection,
                             NewConstructedIntersection.begin()));
                ConstructedIntersection.insert(
                    make_pair(Paths.first, NewConstructedIntersection));
            }
        }
    }
    return std::make_pair(FreeVars, ConstructedIntersection);
}

std::map<int, vector<string>> freeVars(PathMap Map1, PathMap Map2,
                                       vector<string> FunArgs, Memory Heap) {
    std::map<int, set<string>> FreeVarsMap;
    std::map<int, vector<string>> FreeVarsMapVect;
    std::map<int, std::map<int, set<string>>> Constructed;
    for (const auto &It : Map1) {
        const int Index = It.first;
        auto FreeVars1 = freeVarsForBlock(Map1.at(Index));
        const auto FreeVars2 = freeVarsForBlock(Map2.at(Index));
        for (auto Var : FreeVars2.first) {
            FreeVars1.first.insert(Var);
        }
        FreeVarsMap.insert(make_pair(Index, FreeVars1.first));

        // constructed variables
        for (auto MapIt : FreeVars2.second) {
            for (auto Var : MapIt.second) {
                FreeVars1.second[MapIt.first].insert(Var);
            }
        }

        Constructed.insert(make_pair(Index, FreeVars1.second));
    }

    FreeVarsMap[EXIT_MARK] = set<string>();
    FreeVarsMap[UNREACHABLE_MARK] = set<string>();
    // search for a least fixpoint
    // don't tell anyone I wrote that
    bool Changed = true;
    while (Changed) {
        Changed = false;
        for (const auto &It : Map1) {
            const int StartIndex = It.first;
            for (const auto &ItInner : It.second) {
                const int EndIndex = ItInner.first;
                for (auto Var : FreeVarsMap.at(EndIndex)) {
                    if (Constructed.at(StartIndex).at(EndIndex).find(Var) ==
                        Constructed.at(StartIndex).at(EndIndex).end()) {
                        const auto Inserted =
                            FreeVarsMap.at(StartIndex).insert(Var);
                        Changed = Changed || Inserted.second;
                    }
                }
            }
        }
    }

    for (auto It : FreeVarsMap) {
        const int Index = It.first;
        vector<string> VarsVect;
        for (auto Var : It.second) {
            VarsVect.push_back(Var);
        }
        const vector<string> Vars1 = filterVars(1, VarsVect);
        const vector<string> Vars2 = filterVars(2, VarsVect);
        vector<string> Vars;
        Vars.insert(Vars.end(), Vars1.begin(), Vars1.end());
        if (Heap & HEAP_MASK) {
            Vars.push_back("HEAP$1");
        }
        if (Heap & STACK_MASK) {
            Vars.push_back("STACK$1");
        }
        Vars.insert(Vars.end(), Vars2.begin(), Vars2.end());
        if (Heap & HEAP_MASK) {
            Vars.push_back("HEAP$2");
        }
        if (Heap & STACK_MASK) {
            Vars.push_back("STACK$2");
        }
        FreeVarsMapVect[Index] = Vars;
    }
    auto Args1 = filterVars(1, FunArgs);
    auto Args2 = filterVars(2, FunArgs);
    if (Heap & HEAP_MASK) {
        Args1.push_back("HEAP$1");
    }
    if (Heap & STACK_MASK) {
        Args1.push_back("STACK$1");
    }
    if (Heap & HEAP_MASK) {
        Args2.push_back("HEAP$2");
    }
    if (Heap & STACK_MASK) {
        Args2.push_back("STACK$2");
    }
    Args1.insert(Args1.end(), Args2.begin(), Args2.end());

    FreeVarsMapVect[ENTRY_MARK] = Args1;

    return FreeVarsMapVect;
}

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

std::pair<vector<string>, vector<string>>
functionArgs(const llvm::Function &Fun1, const llvm::Function &Fun2) {
    vector<string> Args1;
    for (auto &Arg : Fun1.args()) {
        Args1.push_back(Arg.getName());
    }
    vector<string> Args2;
    for (auto &Arg : Fun2.args()) {
        Args2.push_back(Arg.getName());
    }
    return std::make_pair(Args1, Args2);
}

/// Swap the program index
int swapIndex(int I) {
    assert(I == 1 || I == 2);
    return I == 1 ? 2 : 1;
}

/// Split the assignment blocks on each call
std::pair<vector<vector<AssignmentBlock>>, vector<CallInfo>>
splitAssignments(vector<AssignmentCallBlock> AssignmentCallBlocks) {
    vector<vector<AssignmentBlock>> AssignmentBlocks;
    vector<CallInfo> CallInfos;
    vector<struct AssignmentBlock> CurrentAssignmentsList;
    for (auto Assignments : AssignmentCallBlocks) {
        SMTRef Condition = Assignments.Condition;
        vector<Assignment> CurrentDefinitions;
        for (auto DefOrCall : Assignments.Definitions) {
            if (DefOrCall.Tag == DefOrCallInfoTag::Def) {
                CurrentDefinitions.push_back(*DefOrCall.Definition);
            } else {
                CurrentAssignmentsList.push_back(
                    AssignmentBlock(CurrentDefinitions, Condition));
                CurrentDefinitions.clear();
                AssignmentBlocks.push_back(CurrentAssignmentsList);
                CurrentAssignmentsList.clear();
                Condition = nullptr;
                CallInfos.push_back(*DefOrCall.CallInfo_);
            }
        }
        CurrentAssignmentsList.push_back(
            AssignmentBlock(CurrentDefinitions, Condition));
    }
    AssignmentBlocks.push_back(CurrentAssignmentsList);
    return make_pair(AssignmentBlocks, CallInfos);
}

vector<SMTRef> stringConstants(const llvm::Module &Mod, string Heap) {
    vector<SMTRef> StringConstants;
    for (const auto &Global : Mod.globals()) {
        const string GlobalName = Global.getName();
        vector<SMTRef> StringConstant;
        if (Global.hasInitializer() && Global.isConstant()) {
            if (const auto Arr = llvm::dyn_cast<llvm::ConstantDataArray>(
                    Global.getInitializer())) {
                for (unsigned int i = 0; i < Arr->getNumElements(); ++i) {
                    StringConstant.push_back(makeBinOp(
                        "=", name(std::to_string(Arr->getElementAsInteger(i))),
                        makeBinOp(
                            "select", name(Heap),
                            makeBinOp("+", GlobalName, std::to_string(i)))));
                }
            }
        }
        if (!StringConstant.empty()) {
            StringConstants.push_back(make_shared<Op>("and", StringConstant));
        }
    }
    return StringConstants;
}

vector<InterleaveStep> matchFunCalls(vector<CallInfo> CallInfos1,
                                     vector<CallInfo> CallInfos2) {
    vector<vector<size_t>> Table(CallInfos1.size() + 1,
                                 vector<size_t>(CallInfos2.size() + 1, 0));
    for (uint32_t i = 0; i <= CallInfos1.size(); ++i) {
        Table[i][0] = i;
    }
    for (uint32_t j = 0; j <= CallInfos2.size(); ++j) {
        Table[0][j] = j;
    }
    for (uint32_t i = 1; i <= CallInfos1.size(); ++i) {
        for (uint32_t j = 1; j <= CallInfos2.size(); ++j) {
            if (CallInfos1[i - 1] == CallInfos2[j - 1]) {
                Table[i][j] = Table[i - 1][j - 1];
            } else {
                Table[i][j] =
                    std::min(Table[i - 1][j] + 1, Table[i][j - 1] + 1);
            }
        }
    }
    vector<InterleaveStep> InterleaveSteps;
    uint64_t i = CallInfos1.size(), j = CallInfos2.size();
    while (i > 0 && j > 0) {
        if (CallInfos1[i - 1] == CallInfos2[j - 1]) {
            InterleaveSteps.push_back(InterleaveStep::StepBoth);
            --i;
            --j;
        } else {
            if (Table[i - 1][j] <= Table[i][j - 1]) {
                InterleaveSteps.push_back(InterleaveStep::StepFirst);
                --i;
            } else {
                InterleaveSteps.push_back(InterleaveStep::StepSecond);
                --j;
            }
        }
    }
    while (i > 0) {
        InterleaveSteps.push_back(InterleaveStep::StepFirst);
        --i;
    }
    while (j > 0) {
        InterleaveSteps.push_back(InterleaveStep::StepSecond);
        --j;
    }
    std::reverse(InterleaveSteps.begin(), InterleaveSteps.end());
    return InterleaveSteps;
}

/// Check if the marks match
void checkPathMaps(PathMap Map1, PathMap Map2) {
    if (!mapSubset(Map1, Map2) || !mapSubset(Map2, Map1)) {
        exit(1);
    }
}

bool mapSubset(PathMap Map1, PathMap Map2) {
    for (auto Pair : Map1) {
        if (Map2.find(Pair.first) == Map2.end()) {
            logError("Mark '" + std::to_string(Pair.first) +
                     "' doesn’t exist in both files\n");
            return false;
        }
    }
    return true;
}

SMTRef dontLoopInvariant(SMTRef EndClause, int StartIndex, PathMap PathMap,
                         std::map<int, vector<string>> FreeVars, Program Prog,
                         Memory Heap, bool Signed) {
    auto Clause = EndClause;
    vector<Path> DontLoopPaths;
    for (auto PathMapIt : PathMap.at(StartIndex)) {
        if (PathMapIt.first == StartIndex) {
            for (auto Path : PathMapIt.second) {
                DontLoopPaths.push_back(Path);
            }
        }
    }
    vector<SMTRef> DontLoopExprs;
    for (auto Path : DontLoopPaths) {
        auto Defs = assignmentsOnPath(Path, Prog, FreeVars.at(StartIndex),
                                      false, Heap, Signed);
        auto SMT = nonmutualSMT(name("false"), Defs, Prog, Heap);
        DontLoopExprs.push_back(SMT);
    }
    if (!DontLoopExprs.empty()) {
        auto AndExpr = make_shared<Op>("and", DontLoopExprs);
        Clause = makeBinOp("=>", AndExpr, Clause);
    }
    return Clause;
}
