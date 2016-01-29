#include "SMTGeneration.h"

#include "Compat.h"
#include "Helper.h"
#include "MarkAnalysis.h"
#include "AnnotStackPass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Intrinsics.h"

using llvm::CmpInst;

#include <iostream>

using std::vector;

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
    const auto Invariants = invariantDeclaration(
        ENTRY_MARK, FreeVarsMap[ENTRY_MARK], Both, FunName, Heap);
    Declarations.push_back(Invariants.first);
    Declarations.push_back(Invariants.second);
    const auto Invariants_1 =
        invariantDeclaration(ENTRY_MARK, filterVars(1, FreeVarsMap[ENTRY_MARK]),
                             First, FunName, Heap);
    Declarations.push_back(Invariants_1.first);
    Declarations.push_back(Invariants_1.second);
    const auto Invariants_2 =
        invariantDeclaration(ENTRY_MARK, filterVars(2, FreeVarsMap[ENTRY_MARK]),
                             Second, FunName, Heap);
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
        PathExprs.insert(PathExprs.end(), OffByNPaths.begin(),
                         OffByNPaths.end());
    }

    SMTExprs.insert(SMTExprs.end(), PathExprs.begin(), PathExprs.end());

    return SMTExprs;
}

vector<SMTRef> mainAssertion(llvm::Function &Fun1, llvm::Function &Fun2,
                             shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                             shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                             bool OffByN, vector<SMTRef> &Declarations,
                             bool OnlyRec, Memory Heap, bool Signed) {
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

    const auto SynchronizedPaths = mainSynchronizedPaths(
        PathMap1, PathMap2, FreeVarsMap, FunName, Declarations, Heap, Signed);
    const auto ForbiddenPaths =
        forbiddenPaths(PathMap1, PathMap2, Marked1, Marked2, FreeVarsMap,
                       OffByN, FunName, true, Heap, Signed);
    SMTExprs.insert(SMTExprs.end(), SynchronizedPaths.begin(),
                    SynchronizedPaths.end());
    SMTExprs.push_back(make_shared<Comment>("forbidden main"));
    SMTExprs.insert(SMTExprs.end(), ForbiddenPaths.begin(),
                    ForbiddenPaths.end());
    if (OffByN) {
        SMTExprs.push_back(make_shared<Comment>("offbyn main"));
        const auto OffByNPaths = offByNPaths(PathMap1, PathMap2, FreeVarsMap,
                                             FunName, true, Heap, Signed);
        SMTExprs.insert(SMTExprs.end(), OffByNPaths.begin(), OffByNPaths.end());
    }
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
            const auto Invariants = invariantDeclaration(
                StartIndex, FreeVarsMap.at(StartIndex), Both, FunName, Heap);
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
                        FreeVarsMap.at(EndIndex), Both, FunName, Heap);
                    const auto Defs1 =
                        assignmentsOnPath(Path1, 1, FreeVarsMap.at(StartIndex),
                                          EndIndex == EXIT_MARK, Heap, Signed);
                    const auto Defs2 =
                        assignmentsOnPath(Path2, 2, FreeVarsMap.at(StartIndex),
                                          EndIndex == EXIT_MARK, Heap, Signed);
                    PathExprs.push_back(assertForall(
                        interleaveAssignments(EndInvariant, Defs1, Defs2, Heap),
                        FreeVarsMap.at(StartIndex), StartIndex, Both, FunName,
                        false));
                }
            }
        }
    }
    nonmutualPaths(PathMap1, PathExprs, FreeVarsMap, First, FunName,
                   Declarations, Heap, Signed);
    nonmutualPaths(PathMap2, PathExprs, FreeVarsMap, Second, FunName,
                   Declarations, Heap, Signed);

    return PathExprs;
}

vector<SMTRef> mainSynchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                                     std::map<int, vector<string>> FreeVarsMap,
                                     std::string FunName,
                                     vector<SMTRef> &Declarations, Memory Heap,
                                     bool Signed) {
    vector<SMTRef> PathExprs;
    for (const auto &PathMapIt : PathMap1) {
        const int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            // ignore entry node
            const auto Invariant = mainInvariantDeclaration(
                StartIndex, FreeVarsMap.at(StartIndex), Both, FunName);
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
                            Path1, 1, FreeVarsMap.at(StartIndex),
                            EndIndex == EXIT_MARK, Heap, Signed);
                        const auto Defs2 = assignmentsOnPath(
                            Path2, 2, FreeVarsMap.at(StartIndex),
                            EndIndex == EXIT_MARK, Heap, Signed);
                        PathExprs.push_back(
                            assertForall(interleaveAssignments(
                                             EndInvariant, Defs1, Defs2, Heap),
                                         FreeVarsMap.at(StartIndex), StartIndex,
                                         Both, FunName, true));
                    }
                }
            }
        }
    }

    return PathExprs;
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
                                    Path2, 2, vector<string>(),
                                    EndIndex2 == EXIT_MARK, Heap, Signed);
                                const auto Smt1 = assignmentsOnPath(
                                    Path1, 1, vector<string>(),
                                    EndIndex1 == EXIT_MARK, Heap, Signed);
                                // We need to interleave here, because otherwise
                                // extern functions are not matched
                                const auto SMT = interleaveAssignments(
                                    name("false"), Smt1, Smt2, Heap);
                                PathExprs.push_back(assertForall(
                                    SMT, FreeVarsMap.at(StartIndex), StartIndex,
                                    Both, FunName, Main));
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
                    std::map<int, vector<string>> FreeVarsMap, SMTFor For,
                    std::string FunName, vector<SMTRef> &Declarations,
                    Memory Heap, bool Signed) {
    const int Program = For == First ? 1 : 2;
    for (const auto &PathMapIt : PathMap) {
        const int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            const auto Invariants = invariantDeclaration(
                StartIndex, filterVars(Program, FreeVarsMap.at(StartIndex)),
                For, FunName, Heap);
            Declarations.push_back(Invariants.first);
            Declarations.push_back(Invariants.second);
        }
        for (const auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            for (const auto &Path : InnerPathMapIt.second) {
                const auto EndInvariant1 =
                    invariant(StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                              FreeVarsMap.at(EndIndex), For, FunName, Heap);
                const auto Defs =
                    assignmentsOnPath(Path, Program, FreeVarsMap.at(StartIndex),
                                      EndIndex == EXIT_MARK, Heap, Signed);
                PathExprs.push_back(assertForall(
                    nonmutualSMT(EndInvariant1, Defs, For, Heap),
                    filterVars(Program, FreeVarsMap.at(StartIndex)), StartIndex,
                    For, FunName, false));
            }
        }
    }
}

vector<SMTRef> offByNPaths(PathMap PathMap1, PathMap PathMap2,
                           std::map<int, vector<string>> FreeVarsMap,
                           std::string FunName, bool Main, Memory Heap,
                           bool Signed) {
    vector<SMTRef> Paths;
    const auto FirstPaths = offByNPathsOneDir(
        PathMap1, PathMap2, FreeVarsMap, 1, First, FunName, Main, Heap, Signed);
    const auto SecondPaths =
        offByNPathsOneDir(PathMap2, PathMap1, FreeVarsMap, 2, Second, FunName,
                          Main, Heap, Signed);
    Paths.insert(Paths.end(), FirstPaths.begin(), FirstPaths.end());
    Paths.insert(Paths.end(), SecondPaths.begin(), SecondPaths.end());
    return Paths;
}

vector<SMTRef> offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                                 std::map<int, vector<string>> FreeVarsMap,
                                 int Program, SMTFor For, std::string FunName,
                                 bool Main, Memory Heap, bool Signed) {
    vector<SMTRef> Paths;
    for (const auto &PathMapIt : PathMap_) {
        const int StartIndex = PathMapIt.first;
        for (const auto &InnerPathMapIt : PathMapIt.second) {
            const int EndIndex = InnerPathMapIt.first;
            if (StartIndex == EndIndex) {
                // we found a loop
                for (const auto &Path : InnerPathMapIt.second) {
                    const auto EndArgs2 = filterVars(
                        swapIndex(Program), FreeVarsMap.at(StartIndex));
                    const auto EndArgs =
                        filterVars(Program, FreeVarsMap.at(StartIndex));
                    vector<string> Args;
                    if (For == First) {
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
                        EndInvariant = invariant(StartIndex, StartIndex,
                                                 FreeVarsMap.at(StartIndex),
                                                 Args, Both, FunName, Heap);
                    }
                    const auto DontLoopInvariant = dontLoopInvariant(
                        EndInvariant, StartIndex, OtherPathMap, FreeVarsMap,
                        swapIndex(Program), For == First ? Second : First, Heap,
                        Signed);
                    const auto Defs = assignmentsOnPath(
                        Path, Program, FreeVarsMap.at(EndIndex),
                        EndIndex == EXIT_MARK, Heap, Signed);
                    Paths.push_back(assertForall(
                        nonmutualSMT(DontLoopInvariant, Defs, For, Heap),
                        FreeVarsMap.at(StartIndex), StartIndex, Both, FunName,
                        Main));
                }
            }
        }
    }
    return Paths;
}

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

vector<AssignmentCallBlock> assignmentsOnPath(Path Path, int Program,
                                              vector<std::string> FreeVars,
                                              bool ToEnd, Memory Heap,
                                              bool Signed) {
    const auto FilteredFreeVars = filterVars(Program, FreeVars);

    vector<AssignmentCallBlock> AllDefs;
    set<string> Constructed;
    vector<CallInfo> CallInfos;

    const auto StartDefs = blockAssignments(*Path.Start, nullptr, true, false,
                                            Program, Constructed, Heap, Signed);
    AllDefs.push_back(AssignmentCallBlock(StartDefs, nullptr));

    auto Prev = Path.Start;

    unsigned int i = 0;
    for (auto Edge : Path.Edges) {
        i++;
        const bool Last = i == Path.Edges.size();
        const auto Defs =
            blockAssignments(*Edge.Block, Prev, false, Last && !ToEnd, Program,
                             Constructed, Heap, Signed);
        AllDefs.push_back(AssignmentCallBlock(
            Defs,
            Edge.Cond == nullptr ? nullptr : Edge.Cond->toSmt(Constructed)));
        Prev = Edge.Block;
    }

    vector<DefOrCallInfo> OldDefs;
    for (auto Var : FilteredFreeVars) {
        if (Constructed.find(Var) == Constructed.end()) {
            // Set the new value to the old value, if it hasn't already been set
            OldDefs.push_back(DefOrCallInfo(
                std::make_shared<Assignment>(Var, name(Var + "_old"))));
        }
    }
    AllDefs.push_back(AssignmentCallBlock(OldDefs, nullptr));
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

    for (InterleaveStep Step : makeReverse(InterleaveSteps)) {
        switch (Step) {
        case StepFirst:
            Clause = nonmutualRecursiveForall(Clause, *CallIt1, First, Heap);
            for (auto Assgns : makeReverse(*AssignmentIt1)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            ++CallIt1;
            ++AssignmentIt1;
            break;
        case StepSecond:
            Clause = nonmutualRecursiveForall(Clause, *CallIt2, Second, Heap);
            for (auto Assgns : makeReverse(*AssignmentIt2)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            ++CallIt2;
            ++AssignmentIt2;
            break;
        case StepBoth:
            assert(CallIt1->CallName == CallIt2->CallName);
            Clause = mutualRecursiveForall(Clause, *CallIt1, *CallIt2, Heap);
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
            ++CallIt1;
            ++CallIt2;
            ++AssignmentIt1;
            ++AssignmentIt2;
            break;
        }
    }

    assert(CallIt1 == CallInfo1.rend());
    assert(CallIt2 == CallInfo2.rend());
    assert(AssignmentIt1 == AssignmentBlocks1.rend());
    assert(AssignmentIt2 == AssignmentBlocks2.rend());

    return Clause;
}

SMTRef nonmutualSMT(SMTRef EndClause,
                    vector<AssignmentCallBlock> AssignmentCallBlocks,
                    SMTFor For, Memory Heap) {
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
            Clause = nonmutualRecursiveForall(Clause, *CallIt, For, Heap);
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
// Functions related to generating invariants

SMTRef invariant(int StartIndex, int EndIndex, vector<string> InputArgs,
                 vector<string> EndArgs, SMTFor SMTFor, std::string FunName,
                 Memory Heap) {
    // This is the actual invariant we want to establish
    auto FilteredArgs = InputArgs;
    auto FilteredEndArgs = EndArgs;
    if (SMTFor == First) {
        FilteredArgs = filterVars(1, FilteredArgs);
        FilteredEndArgs = filterVars(1, FilteredEndArgs);
    }
    if (SMTFor == Second) {
        FilteredArgs = filterVars(2, FilteredArgs);
        FilteredEndArgs = filterVars(2, FilteredEndArgs);
    }
    vector<string> ResultArgs;
    switch (SMTFor) {
    case First:
        ResultArgs.push_back("result$1");
        break;
    case Second:
        ResultArgs.push_back("result$2");
        break;
    case Both:
        ResultArgs.push_back("result$1");
        ResultArgs.push_back("result$2");
        break;
    }
    if (Heap & HEAP_MASK) {
        switch (SMTFor) {
        case First:
            ResultArgs.push_back("HEAP$1_res");
            break;
        case Second:
            ResultArgs.push_back("HEAP$2_res");
            break;
        case Both:
            ResultArgs.push_back("HEAP$1_res");
            ResultArgs.push_back("HEAP$2_res");
            break;
        }
    }
    vector<string> EndArgsVect;
    Heap = 0;
    EndArgsVect = FilteredArgs;
    EndArgsVect.insert(EndArgsVect.end(), ResultArgs.begin(), ResultArgs.end());
    EndArgsVect = resolveHeapReferences(EndArgsVect, "_old", Heap);

    auto EndInvariant =
        makeOp(invariantName(StartIndex, SMTFor, FunName), EndArgsVect);
    EndInvariant = wrapHeap(EndInvariant, Heap, EndArgsVect);
    auto Clause = EndInvariant;

    if (EndIndex != EXIT_MARK) {
        // We require the result of another call to establish our invariant so
        // make sure that it satisfies the invariant of the other call and then
        // assert our own invariant
        vector<SortedVar> ForallArgs;
        for (auto ResultArg : ResultArgs) {
            ForallArgs.push_back(SortedVar(ResultArg, argSort(ResultArg)));
        }
        if (EndIndex != UNREACHABLE_MARK) {
            vector<string> UsingArgsVect;
            UsingArgsVect.insert(UsingArgsVect.begin(), FilteredEndArgs.begin(),
                                 FilteredEndArgs.end());
            Memory Heap = 0;
            UsingArgsVect = resolveHeapReferences(UsingArgsVect, "", Heap);
            const auto PreInv =
                makeOp(invariantName(EndIndex, SMTFor, FunName) + "_PRE",
                       UsingArgsVect);
            UsingArgsVect.insert(UsingArgsVect.end(), ResultArgs.begin(),
                                 ResultArgs.end());
            UsingArgsVect = resolveHeapReferences(UsingArgsVect, "", Heap);
            Clause = makeBinOp(
                "=>", wrapHeap(makeOp(invariantName(EndIndex, SMTFor, FunName),
                                      UsingArgsVect),
                               Heap, UsingArgsVect),
                Clause);
            if (SMTFor == Both) {
                Clause = makeBinOp("and", wrapHeap(PreInv, Heap, UsingArgsVect),
                                   Clause);
            }
        }
        Clause = make_shared<Forall>(ForallArgs, Clause);
    }
    return Clause;
}

SMTRef mainInvariant(int EndIndex, vector<string> FreeVars, string FunName,
                     Memory Heap) {
    if (EndIndex == EXIT_MARK) {
        vector<string> Args = {"result$1", "result$2"};
        if (Heap & HEAP_MASK) {
            Args.push_back("HEAP$1_res");
            Args.push_back("HEAP$2_res");
        }
        return makeOp("OUT_INV", Args);
    }
    if (EndIndex == UNREACHABLE_MARK) {
        return name("true");
    }
    FreeVars = resolveHeapReferences(FreeVars, "", Heap);
    return wrapHeap(
        makeOp(invariantName(EndIndex, Both, FunName) + "_MAIN", FreeVars),
        Heap, FreeVars);
}

/// Declare an invariant
std::pair<SMTRef, SMTRef> invariantDeclaration(int BlockIndex,
                                               vector<string> FreeVars,
                                               SMTFor For, std::string FunName,
                                               Memory Heap) {
    // + 1 for each result
    auto NumArgs = FreeVars.size() + 1 + (For == Both ? 1 : 0);
    if (Heap) {
        // index + value at that index
        if (For == Both) {
            NumArgs += 4;
        } else {
            NumArgs += 2;
        }
    }
    NumArgs = adaptSizeToHeap(NumArgs, FreeVars);
    const vector<string> Args(NumArgs, "Int");
    const vector<string> PreArgs(NumArgs - (For == Both ? 2 : 1) -
                                     (Heap ? (For == Both ? 4 : 2) : 0),
                                 "Int");

    return std::make_pair(
        std::make_shared<class FunDecl>(invariantName(BlockIndex, For, FunName),
                                        Args, "Bool"),
        std::make_shared<class FunDecl>(
            invariantName(BlockIndex, For, FunName) + "_PRE", PreArgs, "Bool"));
}

SMTRef mainInvariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                SMTFor For, std::string FunName) {
    auto NumArgs = FreeVars.size();
    NumArgs = adaptSizeToHeap(NumArgs, FreeVars);
    const vector<string> Args(NumArgs, "Int");

    return std::make_shared<class FunDecl>(
        invariantName(BlockIndex, For, FunName) + "_MAIN", Args, "Bool");
}

/// Return the invariant name, special casing the entry block
string invariantName(int Index, SMTFor For, std::string FunName,
                     uint32_t VarArgs) {
    string Name;
    if (Index == ENTRY_MARK) {
        Name = "INV_REC_" + FunName;
    } else {
        Name = "INV_" + std::to_string(Index);
    }
    if (VarArgs > 0) {
        Name += "_" + std::to_string(VarArgs) + "varargs";
    }
    if (For == First) {
        return Name + "__1";
    }
    if (For == Second) {
        return Name + "__2";
    }
    return Name;
}

SMTRef dontLoopInvariant(SMTRef EndClause, int StartIndex, PathMap PathMap,
                         std::map<int, vector<string>> FreeVars, int Program,
                         SMTFor For, Memory Heap, bool Signed) {
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
        auto Defs = assignmentsOnPath(Path, Program, FreeVars.at(StartIndex),
                                      false, Heap, Signed);
        auto SMT = nonmutualSMT(name("false"), Defs, For, Heap);
        DontLoopExprs.push_back(SMT);
    }
    if (!DontLoopExprs.empty()) {
        auto AndExpr = make_shared<Op>("and", DontLoopExprs);
        Clause = makeBinOp("=>", AndExpr, Clause);
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
            invariantName(ENTRY_MARK, Both, Call1.CallName, VarArgs), ImplArgs);
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
            invariantName(ENTRY_MARK, Both, Call1.CallName), ImplArgs);
        PostInvariant = wrapHeap(PostInvariant, Heap,
                                 {"i1", "i2", "i1_res", "i2_res", "i1_stack",
                                  "i2_stack", "STACK$1", "STACK$2"});
        Clause = makeBinOp("=>", PostInvariant, Clause);
        Clause = make_shared<Forall>(Args, Clause);
        const auto PreInv = wrapHeap(
            std::make_shared<Op>(
                invariantName(ENTRY_MARK, Both, Call1.CallName) + "_PRE",
                PreArgs),
            Heap, {"i1", "i2", "i1_stack", "i2_stack", "STACK$1", "STACK$2"});
        return makeBinOp("and", PreInv, Clause);
    }
}

SMTRef nonmutualRecursiveForall(SMTRef Clause, CallInfo Call, SMTFor For,
                                Memory Heap) {
    vector<SortedVar> ForallArgs;
    vector<SMTRef> ImplArgs;
    vector<SMTRef> PreArgs;

    const int Program = For == First ? 1 : 2;
    const string ProgramS = std::to_string(Program);

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
        const SMTRef EndInvariant = make_shared<Op>(
            invariantName(ENTRY_MARK, For, Call.CallName, VarArgs), Call.Args);
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
            invariantName(ENTRY_MARK, For, Call.CallName), ImplArgs);
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
            invariantName(ENTRY_MARK, For, Call.CallName) + "_PRE", PreArgs);
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
SMTRef assertForall(SMTRef Clause, vector<string> FreeVars, int BlockIndex,
                    SMTFor For, std::string FunName, bool Main) {
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
        return make_shared<Assert>(Clause);
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

    return make_shared<Assert>(make_shared<Forall>(Vars, Clause));
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

SMTRef inInvariant(llvm::Function &Fun1, llvm::Function &Fun2, SMTRef Body,
                   Memory Heap, llvm::Module &Mod1, llvm::Module &Mod2,
                   bool Strings) {

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
        "=>", wrapHeap(makeOp(invariantName(ENTRY_MARK, Both, FunName), Args),
                       Heap, Args),
        makeOp("OUT_INV", OutArgs));
    PreInvArgs = resolveHeapReferences(PreInvArgs, "", Heap);
    const auto PreInv = wrapHeap(
        makeOp(invariantName(ENTRY_MARK, Both, FunName) + "_PRE", PreInvArgs),
        Heap, PreInvArgs);

    const auto EqualArgs =
        makeFunArgsEqual(EqualResults, PreInv, FunArgs1, FunArgs2);
    const auto ForallInputs = make_shared<Forall>(ForallArgs, EqualArgs);
    return make_shared<Assert>(ForallInputs);
}

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic blocks to
// SMT assignments

/// Convert a basic block to a list of assignments
vector<DefOrCallInfo> blockAssignments(llvm::BasicBlock &BB,
                                       const llvm::BasicBlock *PrevBB,
                                       bool IgnorePhis, bool OnlyPhis,
                                       int Program, set<string> &Constructed,
                                       Memory Heap, bool Signed) {
    vector<DefOrCallInfo> Definitions;
    assert(BB.size() >= 1); // There should be at least a terminator instruction
    for (auto Instr = BB.begin(), E = std::prev(BB.end(), 1); Instr != E;
         ++Instr) {
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!IgnorePhis && llvm::isa<llvm::PHINode>(Instr)) {
            Definitions.push_back(DefOrCallInfo(
                instrAssignment(*Instr, PrevBB, Constructed, Program, Signed)));
            Constructed.insert(Instr->getName());
        }
        if (!OnlyPhis && !llvm::isa<llvm::PHINode>(Instr)) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(Instr)) {
                const auto Fun = CallInst->getCalledFunction();
                if (!Fun) {
                    logErrorData("Call to undeclared function\n", *CallInst);
                    exit(1);
                }
                if (Fun->getIntrinsicID() == llvm::Intrinsic::memcpy) {
                    const vector<DefOrCallInfo> Defs =
                        memcpyIntrinsic(CallInst, Constructed, Program);
                    Definitions.insert(Definitions.end(), Defs.begin(),
                                       Defs.end());
                } else {
                    if (Heap & HEAP_MASK) {
                        Definitions.push_back(DefOrCallInfo(
                            std::make_shared<std::tuple<string, SMTRef>>(
                                "HEAP$" + std::to_string(Program),
                                name(resolveName("HEAP$" +
                                                     std::to_string(Program),
                                                 Constructed)))));
                        Constructed.insert("HEAP$" + std::to_string(Program));
                    }
                    Definitions.push_back(DefOrCallInfo(toCallInfo(
                        CallInst->getName(), Program, *CallInst, Constructed)));
                    if (Heap & HEAP_MASK) {
                        Definitions.push_back(DefOrCallInfo(
                            std::make_shared<std::tuple<string, SMTRef>>(
                                "HEAP$" + std::to_string(Program),
                                name("HEAP$" + std::to_string(Program) +
                                     "_res"))));
                    }
                }
            } else {
                Definitions.push_back(DefOrCallInfo(instrAssignment(
                    *Instr, PrevBB, Constructed, Program, Signed)));
            }
            Constructed.insert(Instr->getName());
        }
    }
    if (const auto RetInst =
            llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator())) {
        // TODO (moritz): use a more clever approach for void functions
        auto RetName = name("0");
        if (RetInst->getReturnValue() != nullptr) {
            RetName = instrNameOrVal(RetInst->getReturnValue(),
                                     RetInst->getType(), Constructed);
        }
        Definitions.push_back(
            DefOrCallInfo(make_shared<std::tuple<string, SMTRef>>(
                "result$" + std::to_string(Program), RetName)));
        if (Heap & HEAP_MASK) {
            Definitions.push_back(
                DefOrCallInfo(make_shared<std::tuple<string, SMTRef>>(
                    "HEAP$" + std::to_string(Program) + "_res",
                    name(resolveName("HEAP$" + std::to_string(Program),
                                     Constructed)))));
        }
    }
    return Definitions;
}

/// Convert a single instruction to an assignment
std::shared_ptr<std::tuple<string, SMTRef>>
instrAssignment(llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
                set<string> &Constructed, int Program, bool Signed) {
    if (const auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        if (BinOp->getOpcode() == Instruction::Sub) {
            if (const auto Instr0 =
                    llvm::dyn_cast<llvm::Instruction>(BinOp->getOperand(0))) {
                if (const auto Instr1 = llvm::dyn_cast<llvm::Instruction>(
                        BinOp->getOperand(1))) {
                    if (Instr0->getMetadata("reve.ptr_to_int") &&
                        Instr1->getMetadata("reve.ptr_to_int")) {
                        flagInstr(Instr, "reve.ptr_diff");
                    }
                }
            }
        }
        if (BinOp->getOpcode() == Instruction::SDiv) {
            if (const auto Instr =
                    llvm::dyn_cast<llvm::Instruction>(BinOp->getOperand(0))) {
                if (const auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(
                        BinOp->getOperand(1))) {
                    if (ConstInt->getSExtValue() == 4 &&
                        Instr->getMetadata("reve.ptr_diff")) {
                        return make_shared<std::tuple<string, SMTRef>>(
                            BinOp->getName(),
                            instrNameOrVal(BinOp->getOperand(0),
                                           BinOp->getOperand(0)->getType(),
                                           Constructed));
                    }
                }
            }
        }
        if (BinOp->getOpcode() == Instruction::Or ||
            BinOp->getOpcode() == Instruction::And ||
            BinOp->getOpcode() == Instruction::Xor) {
            if (!(BinOp->getOperand(0)->getType()->isIntegerTy(1) &&
                  BinOp->getOperand(1)->getType()->isIntegerTy(1))) {
                logWarningData(
                    "Bitwise operators of bitwidth > 1 is not supported\n",
                    *BinOp);
            }
        }
        return make_shared<std::tuple<string, SMTRef>>(
            BinOp->getName(),
            makeBinOp(
                opName(*BinOp),
                instrNameOrVal(BinOp->getOperand(0),
                               BinOp->getOperand(0)->getType(), Constructed),
                instrNameOrVal(BinOp->getOperand(1),
                               BinOp->getOperand(1)->getType(), Constructed)));
    }
    if (const auto CmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto Fun = predicateFun(*CmpInst, Signed);
        const auto Cmp = makeBinOp(
            predicateName(CmpInst->getPredicate()),
            Fun(instrNameOrVal(CmpInst->getOperand(0),
                               CmpInst->getOperand(0)->getType(), Constructed)),
            Fun(instrNameOrVal(CmpInst->getOperand(1),
                               CmpInst->getOperand(0)->getType(),
                               Constructed)));
        return make_shared<std::tuple<string, SMTRef>>(CmpInst->getName(), Cmp);
    }
    if (const auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        const auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return make_shared<std::tuple<string, SMTRef>>(
            PhiInst->getName(),
            instrNameOrVal(Val, Val->getType(), Constructed));
    }
    if (const auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        const auto Cond = SelectInst->getCondition();
        const auto TrueVal = SelectInst->getTrueValue();
        const auto FalseVal = SelectInst->getFalseValue();
        const vector<SMTRef> Args = {
            instrNameOrVal(Cond, Cond->getType(), Constructed),
            instrNameOrVal(TrueVal, TrueVal->getType(), Constructed),
            instrNameOrVal(FalseVal, FalseVal->getType(), Constructed)};
        return make_shared<std::tuple<string, SMTRef>>(
            SelectInst->getName(), std::make_shared<class Op>("ite", Args));
    }
    if (const auto PtrToIntInst = llvm::dyn_cast<llvm::PtrToIntInst>(&Instr)) {
        flagInstr(Instr, "reve.ptr_to_int");
        return make_shared<std::tuple<string, SMTRef>>(
            PtrToIntInst->getName(),
            instrNameOrVal(PtrToIntInst->getPointerOperand(),
                           PtrToIntInst->getType(), Constructed));
    }
    if (const auto SExtInst = llvm::dyn_cast<llvm::SExtInst>(&Instr)) {
        return make_shared<std::tuple<string, SMTRef>>(
            SExtInst->getName(),
            instrNameOrVal(SExtInst->getOperand(0), SExtInst->getType(),
                           Constructed));
    }
    if (const auto GetElementPtrInst =
            llvm::dyn_cast<llvm::GetElementPtrInst>(&Instr)) {
        return make_shared<std::tuple<string, SMTRef>>(
            GetElementPtrInst->getName(),
            resolveGEP(*GetElementPtrInst, Constructed));
    }
    if (const auto LoadInst = llvm::dyn_cast<llvm::LoadInst>(&Instr)) {
        SMTRef Pointer =
            instrNameOrVal(LoadInst->getOperand(0),
                           LoadInst->getOperand(0)->getType(), Constructed);
        const auto Load = makeBinOp(
            "select",
            name(resolveName("HEAP$" + std::to_string(Program), Constructed)),
            Pointer);
        return make_shared<std::tuple<string, SMTRef>>(LoadInst->getName(),
                                                       Load);
    }
    if (const auto StoreInst = llvm::dyn_cast<llvm::StoreInst>(&Instr)) {
        string Heap = "HEAP$" + std::to_string(Program);
        const auto Val = instrNameOrVal(StoreInst->getValueOperand(),
                                        StoreInst->getValueOperand()->getType(),
                                        Constructed);
        const auto Pointer = instrNameOrVal(
            StoreInst->getPointerOperand(),
            StoreInst->getPointerOperand()->getType(), Constructed);
        const std::vector<SMTRef> Args = {name(resolveName(Heap, Constructed)),
                                          Pointer, Val};
        const auto Store = make_shared<Op>("store", Args);
        Constructed.insert(Heap);
        return make_shared<std::tuple<string, SMTRef>>(
            "HEAP$" + std::to_string(Program), Store);
    }
    if (const auto TruncInst = llvm::dyn_cast<llvm::TruncInst>(&Instr)) {
        const auto Val =
            instrNameOrVal(TruncInst->getOperand(0),
                           TruncInst->getOperand(0)->getType(), Constructed);
        return make_shared<std::tuple<string, SMTRef>>(TruncInst->getName(),
                                                       Val);
    }
    if (const auto ZExt = llvm::dyn_cast<llvm::ZExtInst>(&Instr)) {
        const auto Operand = ZExt->getOperand(0);
        const auto Val =
            instrNameOrVal(Operand, Operand->getType(), Constructed);
        const auto RetTy = ZExt->getType();
        if (RetTy->isIntegerTy() && RetTy->getIntegerBitWidth() > 1 &&
            Operand->getType()->isIntegerTy(1)) {
            std::vector<SMTRef> Args;
            Args.push_back(Val);
            Args.push_back(name("1"));
            Args.push_back(name("0"));
            return make_shared<std::tuple<string, SMTRef>>(
                ZExt->getName(), make_shared<Op>("ite", Args));
        } else {
            return make_shared<std::tuple<string, SMTRef>>(ZExt->getName(),
                                                           Val);
        }
    }
    if (const auto BitCast = llvm::dyn_cast<llvm::CastInst>(&Instr)) {
        const auto Val =
            instrNameOrVal(BitCast->getOperand(0),
                           BitCast->getOperand(0)->getType(), Constructed);
        return make_shared<std::tuple<string, SMTRef>>(BitCast->getName(), Val);
    }
    if (const auto AllocaInst = llvm::dyn_cast<llvm::AllocaInst>(&Instr)) {
        return make_shared<std::tuple<string, SMTRef>>(
            AllocaInst->getName(),
            name(llvm::cast<llvm::MDString>(
                     AllocaInst->getMetadata("reve.stack_pointer")
                         ->getOperand(0))
                     ->getString()));
    }
    logErrorData("Couldn’t convert instruction to def\n", Instr);
    return make_shared<std::tuple<string, SMTRef>>("UNKNOWN INSTRUCTION",
                                                   name("UNKNOWN ARGS"));
}

/// Convert an LLVM predicate to an SMT predicate
string predicateName(llvm::CmpInst::Predicate Pred) {
    switch (Pred) {
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_ULT:
        return "<";
    case CmpInst::ICMP_SLE:
    case CmpInst::ICMP_ULE:
        return "<=";
    case CmpInst::ICMP_EQ:
        return "=";
    case CmpInst::ICMP_SGE:
    case CmpInst::ICMP_UGE:
        return ">=";
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_UGT:
        return ">";
    case CmpInst::ICMP_NE:
        return "distinct";
    default:
        return "unsupported predicate";
    }
}

/// A function that is abblied to the arguments of a predicate
std::function<SMTRef(SMTRef)> predicateFun(const llvm::CmpInst::CmpInst &Cmp,
                                           bool Signed) {
    if (Cmp.isUnsigned() && !Signed) {
        return [](SMTRef Signed) { return makeUnaryOp("abs", Signed); };
    }
    return [](SMTRef Signed) { return Signed; };
}

/// Convert an LLVM op to an SMT op
string opName(const llvm::BinaryOperator &Op) {
    switch (Op.getOpcode()) {
    case Instruction::Add:
        return "+";
    case Instruction::Sub:
        return "-";
    case Instruction::Mul:
        return "*";
    case Instruction::SDiv:
        return "div";
    case Instruction::UDiv:
        return "div";
    case Instruction::SRem:
        return "mod";
    case Instruction::URem:
        return "mod";
    case Instruction::Or:
        return "or";
    case Instruction::And:
        return "and";
    case Instruction::Xor:
        return "xor";
    default:
        logError("Unknown opcode: " + std::string(Op.getOpcodeName()) + "\n");
        return Op.getOpcodeName();
    }
}

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef instrNameOrVal(const llvm::Value *Val, const llvm::Type *Ty,
                      set<string> Constructed) {
    if (const auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        const auto ApInt = ConstInt->getValue();
        if (ApInt.isIntN(1) && Ty->isIntegerTy(1)) {
            return name(ApInt.getBoolValue() ? "true" : "false");
        }
        if (ApInt.isNegative()) {
            return makeUnaryOp(
                "-", name(ApInt.toString(10, true).substr(1, string::npos)));
        }
        return name(ApInt.toString(10, true));
    }
    if (llvm::isa<llvm::ConstantPointerNull>(Val)) {
        return name("0");
    }
    if (const auto GEP = llvm::dyn_cast<llvm::GEPOperator>(Val)) {
        if (!llvm::isa<llvm::Instruction>(Val)) {
            return resolveGEP(*GEP, Constructed);
        }
    }
    if (llvm::isa<llvm::GlobalValue>(Val)) {
        return name(Val->getName());
    }
    if (Val->getName().empty()) {
        logErrorData("Unnamed variable\n", *Val);
        exit(1);
    }
    resolveName(Val->getName(), Constructed);
    if (Constructed.find(Val->getName()) == Constructed.end()) {
        const string Name = Val->getName();
        return name(Name + "_old");
    }
    return name(Val->getName());
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

std::pair<vector<string>, vector<string>> functionArgs(llvm::Function &Fun1,
                                                       llvm::Function &Fun2) {
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

/// Filter vars to only include the ones from Program
vector<string> filterVars(int Program, vector<string> Vars) {
    vector<string> FilteredVars;
    const string ProgramName = std::to_string(Program);
    for (auto Var : Vars) {
        const auto Pos = Var.rfind("$");
        if (Var.substr(Pos + 1, ProgramName.length()) == ProgramName) {
            FilteredVars.push_back(Var);
        }
    }
    return FilteredVars;
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
            if (DefOrCall.Tag == Def) {
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

std::shared_ptr<CallInfo> toCallInfo(string AssignedTo, int Program,
                                     const llvm::CallInst &CallInst,
                                     set<string> Constructed) {
    vector<SMTRef> Args;
    if (AssignedTo.empty()) {
        AssignedTo = "res" + std::to_string(Program);
    }
    uint32_t i = 0;
    const auto &FunTy = *CallInst.getFunctionType();
    const llvm::Function &Fun = *CallInst.getCalledFunction();
    for (auto &Arg : CallInst.arg_operands()) {
        Args.push_back(instrNameOrVal(Arg, FunTy.getParamType(i), Constructed));
        ++i;
    }
    return make_shared<CallInfo>(AssignedTo, Fun.getName(), Args,
                                 Fun.isDeclaration(), Fun);
}

std::vector<std::string> resolveHeapReferences(std::vector<std::string> Args,
                                               string Suffix, Memory &Heap) {
    Heap = 0;
    vector<string> Result;
    for (auto Arg : Args) {
        std::smatch MatchResult;
        if (std::regex_match(Arg, MatchResult, HEAP_REGEX)) {
            const string I = MatchResult[2];
            string Index = "i" + I;
            if (MatchResult[1] == "STACK") {
                Index += "_stack";
            }
            Result.push_back(Index);
            Result.push_back("(select " + Arg + Suffix + " " + Index + ")");
            Heap |= HEAP_MASK;
        } else if (Arg == "HEAP$1_res" || Arg == "HEAP$2_res") {
            const string Index = "i" + Arg.substr(5, 6);
            Result.push_back(Index);
            Result.push_back("(select " + Arg + " " + Index + ")");
            Heap |= HEAP_MASK;
        } else {
            if (Arg == "result$1" || Arg == "result$2") {
                Result.push_back(Arg);
            } else {
                Result.push_back(Arg + Suffix);
            }
        }
    }
    return Result;
}

SMTRef wrapHeap(SMTRef Inv, Memory Heap, vector<string> FreeVars) {
    if (!Heap) {
        return Inv;
    }
    std::vector<SortedVar> Args;
    for (auto Var : FreeVars) {
        if (std::regex_match(Var, INDEX_REGEX)) {
            Args.push_back(SortedVar(Var, "Int"));
        }
        if (Var == "STACK$1" || Var == "STACK$2") {
            Args.push_back(SortedVar(Var, "(Array Int Int)"));
        }
    }
    return make_shared<Forall>(Args, Inv);
}

unsigned long adaptSizeToHeap(unsigned long Size, vector<string> FreeVars) {
    if (std::find(FreeVars.begin(), FreeVars.end(), "HEAP$1") !=
        FreeVars.end()) {
        Size++;
    }
    if (std::find(FreeVars.begin(), FreeVars.end(), "STACK$1") !=
        FreeVars.end()) {
        Size++;
    }
    if (std::find(FreeVars.begin(), FreeVars.end(), "HEAP$2") !=
        FreeVars.end()) {
        Size++;
    }
    if (std::find(FreeVars.begin(), FreeVars.end(), "STACK$2") !=
        FreeVars.end()) {
        Size++;
    }
    return Size;
}

void flagInstr(llvm::Instruction &Instr, string Flag) {
    llvm::LLVMContext &Cxt = Instr.getContext();
    llvm::MDTuple *Unit =
        llvm::MDTuple::get(Cxt, llvm::ArrayRef<llvm::Metadata *>());
    Instr.setMetadata(Flag, Unit);
}

template <typename T> SMTRef resolveGEP(T &GEP, set<string> Constructed) {
    std::vector<SMTRef> Args;
    Args.push_back(instrNameOrVal(GEP.getPointerOperand(),
                                  GEP.getPointerOperand()->getType(),
                                  Constructed));
    const auto Type = GEP.getSourceElementType();
    std::vector<llvm::Value *> Indices;
    for (auto Ix = GEP.idx_begin(), E = GEP.idx_end(); Ix != E; ++Ix) {
        Indices.push_back(*Ix);
        const auto Size = typeSize(llvm::GetElementPtrInst::getIndexedType(
            Type, llvm::ArrayRef<llvm::Value *>(Indices)));
        if (Size == 1) {
            Args.push_back(instrNameOrVal(*Ix, (*Ix)->getType(), Constructed));
        } else {
            Args.push_back(
                makeBinOp("*", name(std::to_string(Size)),
                          instrNameOrVal(*Ix, (*Ix)->getType(), Constructed)));
        }
    }
    return make_shared<Op>("+", Args);
}

bool isStackOp(const llvm::Instruction &Inst) {
    return Inst.getMetadata("reve.stackop");
}

string argSort(string Arg) {
    if (std::regex_match(Arg, HEAP_REGEX) || Arg == "HEAP$1_res" ||
        Arg == "HEAP$2_res") {
        return "(Array Int Int)";
    }
    return "Int";
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
            InterleaveSteps.push_back(StepBoth);
            --i;
            --j;
        } else {
            if (Table[i - 1][j] <= Table[i][j - 1]) {
                InterleaveSteps.push_back(StepFirst);
                --i;
            } else {
                InterleaveSteps.push_back(StepSecond);
                --j;
            }
        }
    }
    while (i > 0) {
        InterleaveSteps.push_back(StepFirst);
        --i;
    }
    while (j > 0) {
        InterleaveSteps.push_back(StepSecond);
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

vector<DefOrCallInfo> memcpyIntrinsic(const llvm::CallInst *CallInst,
                                      set<string> &Constructed, int Program) {
    vector<DefOrCallInfo> Definitions;
    const auto CastInst0 =
        llvm::dyn_cast<llvm::CastInst>(CallInst->getArgOperand(0));
    const auto CastInst1 =
        llvm::dyn_cast<llvm::CastInst>(CallInst->getArgOperand(1));
    if (CastInst0 && CastInst1) {
        const auto Ty0 =
            llvm::dyn_cast<llvm::PointerType>(CastInst0->getSrcTy());
        const auto Ty1 =
            llvm::dyn_cast<llvm::PointerType>(CastInst1->getSrcTy());
        const auto StructTy0 =
            llvm::dyn_cast<llvm::StructType>(Ty0->getElementType());
        const auto StructTy1 =
            llvm::dyn_cast<llvm::StructType>(Ty1->getElementType());
        if (StructTy0 && StructTy1) {
            assert(StructTy0->isLayoutIdentical(StructTy1));
            const SMTRef BasePointerDest = instrNameOrVal(
                CallInst->getArgOperand(0),
                CallInst->getArgOperand(0)->getType(), Constructed);
            const SMTRef BasePointerSrc = instrNameOrVal(
                CallInst->getArgOperand(1),
                CallInst->getArgOperand(1)->getType(), Constructed);
            string HeapNameSelect = "HEAP$" + std::to_string(Program);
            if (isStackOp(*CastInst1)) {
                HeapNameSelect = "STACK$" + std::to_string(Program);
            }
            string HeapNameStore = "HEAP$" + std::to_string(Program);
            if (isStackOp(*CastInst0)) {
                HeapNameStore = "STACK$" + std::to_string(Program);
            }
            int i = 0;
            for (const auto ElTy : StructTy0->elements()) {
                const SMTRef HeapSelect =
                    name(resolveName(HeapNameSelect, Constructed));
                const SMTRef HeapStore =
                    name(resolveName(HeapNameStore, Constructed));
                for (int j = 0; j < typeSize(ElTy); ++j) {
                    const SMTRef Select =
                        makeBinOp("select", HeapSelect,
                                  makeBinOp("+", BasePointerSrc,
                                            name(std::to_string(i))));
                    const vector<SMTRef> Args = {
                        HeapStore, makeBinOp("+", BasePointerDest,
                                             name(std::to_string(i))),
                        Select};
                    const SMTRef Store = make_shared<Op>("store", Args);
                    Definitions.push_back(
                        make_shared<std::tuple<string, SMTRef>>(HeapNameStore,
                                                                Store));
                    ++i;
                }
                Constructed.insert(HeapNameStore);
            }
        } else {
            logError("currently only memcpy of structs is "
                     "supported\n");
            exit(1);
        }
    } else {
        logError("currently only memcpy of "
                 "bitcasted pointers is supported\n");
        exit(1);
    }
    return Definitions;
}
