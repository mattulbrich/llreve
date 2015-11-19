#include "SMTGeneration.h"

#include "Compat.h"
#include "MarkAnalysis.h"

#include "llvm/IR/Constants.h"

using llvm::CmpInst;

#include <iostream>
using std::vector;

vector<SMTRef> convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                            shared_ptr<llvm::FunctionAnalysisManager> Fam1,
                            shared_ptr<llvm::FunctionAnalysisManager> Fam2,
                            bool OffByN, vector<SMTRef> &Declarations) {
    // TODO(moritz): check that the marks are the same
    auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    std::string FunName = Fun1.getName();
    std::pair<vector<string>, vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    vector<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.push_back(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.push_back(Arg);
    }
    std::map<int, vector<string>> FreeVarsMap =
        freeVars(PathMap1, PathMap2, FunArgs);
    vector<SMTRef> SMTExprs;
    vector<SMTRef> PathExprs;

    // we only need pre invariants for mutual invariants
    auto Invariants = invariantDeclaration(ENTRY_MARK, FunArgs, Both, FunName);
    Declarations.push_back(Invariants.first);
    Declarations.push_back(Invariants.second);
    auto Invariants_1 = invariantDeclaration(ENTRY_MARK, filterVars(1, FunArgs),
                                             First, FunName);
    Declarations.push_back(Invariants_1.first);
    Declarations.push_back(Invariants_1.second);
    auto Invariants_2 = invariantDeclaration(ENTRY_MARK, filterVars(2, FunArgs),
                                             Second, FunName);
    Declarations.push_back(Invariants_2.first);
    Declarations.push_back(Invariants_2.second);

    auto SynchronizedPaths =
        synchronizedPaths(PathMap1, PathMap2, FreeVarsMap, FunArgsPair.first,
                          FunArgsPair.second, FunName, Declarations);

    // add actual path smts
    PathExprs.insert(PathExprs.end(), SynchronizedPaths.begin(),
                     SynchronizedPaths.end());

    // generate forbidden paths
    PathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    auto ForbiddenPaths = forbiddenPaths(PathMap1, PathMap2, Marked1, Marked2,
                                         FreeVarsMap, OffByN, FunName, false);
    PathExprs.insert(PathExprs.end(), ForbiddenPaths.begin(),
                     ForbiddenPaths.end());

    if (OffByN) {
        // generate off by n paths
        PathExprs.push_back(make_shared<Comment>("OFF BY N"));
        auto OffByNPaths =
            offByNPaths(PathMap1, PathMap2, FreeVarsMap, FunName, false);
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
                             bool OnlyRec) {
    auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    std::vector<SMTRef> SMTExprs;
    std::string FunName = Fun1.getName();
    std::pair<vector<string>, vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    vector<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.push_back(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.push_back(Arg);
    }
    std::map<int, vector<string>> FreeVarsMap =
        freeVars(PathMap1, PathMap2, FunArgs);
    if (OnlyRec) {
        SMTExprs.push_back(equalInputsEqualOutputs(
            FunArgs, FunArgsPair.first, FunArgsPair.second, FunName));
        return SMTExprs;
    }
    auto SynchronizedPaths = mainSynchronizedPaths(
        PathMap1, PathMap2, FreeVarsMap, FunArgsPair.first, FunArgsPair.second,
        FunName, Declarations);
    auto ForbiddenPaths = forbiddenPaths(PathMap1, PathMap2, Marked1, Marked2,
                                         FreeVarsMap, OffByN, FunName, true);
    SMTExprs.insert(SMTExprs.end(), SynchronizedPaths.begin(),
                    SynchronizedPaths.end());
    SMTExprs.push_back(make_shared<Comment>("forbidden main"));
    SMTExprs.insert(SMTExprs.end(), ForbiddenPaths.begin(),
                    ForbiddenPaths.end());
    if (OffByN) {
        SMTExprs.push_back(make_shared<Comment>("offbyn main"));
        auto OffByNPaths =
            offByNPaths(PathMap1, PathMap2, FreeVarsMap, FunName, true);
        SMTExprs.insert(SMTExprs.end(), OffByNPaths.begin(), OffByNPaths.end());
    }
    SMTExprs.push_back(make_shared<Comment>("end"));
    return SMTExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

vector<SMTRef> synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                                 std::map<int, vector<string>> FreeVarsMap,
                                 vector<string> FunArgs1,
                                 vector<string> FunArgs2, std::string FunName,
                                 vector<SMTRef> &Declarations) {
    vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            // ignore entry node
            auto Invariants = invariantDeclaration(
                StartIndex, FreeVarsMap.at(StartIndex), Both, FunName);
            Declarations.push_back(Invariants.first);
            Declarations.push_back(Invariants.second);
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            auto Paths = PathMap2.at(StartIndex).at(EndIndex);
            for (auto &Path1 : InnerPathMapIt.second) {
                for (auto &Path2 : Paths) {
                    auto EndInvariant = invariant(
                        StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                        FreeVarsMap.at(EndIndex), Both, FunName);
                    auto Defs1 =
                        assignmentsOnPath(Path1, 1, FreeVarsMap.at(EndIndex),
                                          EndIndex == EXIT_MARK);
                    auto Defs2 =
                        assignmentsOnPath(Path2, 2, FreeVarsMap.at(EndIndex),
                                          EndIndex == EXIT_MARK);
                    PathExprs.push_back(assertForall(
                        interleaveAssignments(EndInvariant, Defs1, Defs2,
                                              FunArgs1, FunArgs2),
                        FreeVarsMap.at(StartIndex), StartIndex, Both, FunName,
                        false));
                }
            }
        }
    }
    nonmutualPaths(PathMap1, PathExprs, FreeVarsMap, First, FunName,
                   Declarations);
    nonmutualPaths(PathMap2, PathExprs, FreeVarsMap, Second, FunName,
                   Declarations);

    return PathExprs;
}

vector<SMTRef> mainSynchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                                     std::map<int, vector<string>> FreeVarsMap,
                                     vector<string> FunArgs1,
                                     vector<string> FunArgs2,
                                     std::string FunName,
                                     vector<SMTRef> &Declarations) {
    vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            // ignore entry node
            auto Invariant = mainInvariantDeclaration(
                StartIndex, FreeVarsMap.at(StartIndex), Both, FunName);
            Declarations.push_back(Invariant);
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            auto Paths = PathMap2.at(StartIndex).at(EndIndex);
            for (auto &Path1 : InnerPathMapIt.second) {
                for (auto &Path2 : Paths) {
                    auto EndInvariant = mainInvariant(
                        EndIndex, FreeVarsMap.at(EndIndex), FunName);
                    auto Defs1 =
                        assignmentsOnPath(Path1, 1, FreeVarsMap.at(EndIndex),
                                          EndIndex == EXIT_MARK);
                    auto Defs2 =
                        assignmentsOnPath(Path2, 2, FreeVarsMap.at(EndIndex),
                                          EndIndex == EXIT_MARK);
                    PathExprs.push_back(assertForall(
                        interleaveAssignments(EndInvariant, Defs1, Defs2,
                                              FunArgs1, FunArgs2),
                        FreeVarsMap.at(StartIndex), StartIndex, Both, FunName,
                        true));
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
                              bool OffByN, std::string FunName, bool Main) {
    vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        for (auto &InnerPathMapIt1 : PathMapIt.second) {
            int EndIndex1 = InnerPathMapIt1.first;
            for (auto &InnerPathMapIt2 : PathMap2.at(StartIndex)) {
                auto EndIndex2 = InnerPathMapIt2.first;
                if (EndIndex1 != EndIndex2) {
                    for (auto &Path1 : InnerPathMapIt1.second) {
                        for (auto &Path2 : InnerPathMapIt2.second) {
                            auto EndBlock1 = lastBlock(Path1);
                            auto EndBlock2 = lastBlock(Path2);
                            auto EndIndices1 = Marked1.BlockToMarksMap[EndBlock1];
                            auto EndIndices2 = Marked2.BlockToMarksMap[EndBlock2];
                            if (!OffByN ||
                                ((StartIndex != EndIndex1 && // no circles
                                  StartIndex != EndIndex2) &&
                                 intersection(EndIndices1, EndIndices2).empty())) {
                                auto Smt2 = assignmentsOnPath(
                                    Path2, 2, vector<string>(),
                                    EndIndex2 == EXIT_MARK);
                                auto Smt1 = assignmentsOnPath(
                                    Path1, 1, vector<string>(),
                                    EndIndex1 == EXIT_MARK);
                                auto SMT =
                                    nonmutualSMT(name("false"), Smt2, Second);
                                SMT = nonmutualSMT(SMT, Smt1, First);
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
                    std::string FunName, vector<SMTRef> &Declarations) {
    int Program = For == First ? 1 : 2;
    for (auto &PathMapIt : PathMap) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != ENTRY_MARK) {
            auto Invariants = invariantDeclaration(
                StartIndex, filterVars(Program, FreeVarsMap.at(StartIndex)),
                For, FunName);
            Declarations.push_back(Invariants.first);
            Declarations.push_back(Invariants.second);
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            for (auto &Path : InnerPathMapIt.second) {
                auto EndInvariant1 =
                    invariant(StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                              FreeVarsMap.at(EndIndex), For, FunName);
                auto Defs =
                    assignmentsOnPath(Path, Program, FreeVarsMap.at(EndIndex),
                                      EndIndex == EXIT_MARK);
                PathExprs.push_back(assertForall(
                    nonmutualSMT(EndInvariant1, Defs, For),
                    filterVars(Program, FreeVarsMap.at(StartIndex)), StartIndex,
                    For, FunName, false));
            }
        }
    }
}

vector<SMTRef> offByNPaths(PathMap PathMap1, PathMap PathMap2,
                           std::map<int, vector<string>> FreeVarsMap,
                           std::string FunName, bool Main) {
    vector<SMTRef> Paths;
    auto FirstPaths = offByNPathsOneDir(PathMap1, PathMap2, FreeVarsMap, 1,
                                        First, FunName, Main);
    auto SecondPaths = offByNPathsOneDir(PathMap2, PathMap1, FreeVarsMap, 2,
                                         Second, FunName, Main);
    Paths.insert(Paths.end(), FirstPaths.begin(), FirstPaths.end());
    Paths.insert(Paths.end(), SecondPaths.begin(), SecondPaths.end());
    return Paths;
}

vector<SMTRef> offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                                 std::map<int, vector<string>> FreeVarsMap,
                                 int Program, SMTFor For, std::string FunName,
                                 bool Main) {
    vector<SMTRef> Paths;
    for (auto &PathMapIt : PathMap_) {
        int StartIndex = PathMapIt.first;
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            if (StartIndex == EndIndex) {
                // we found a loop
                for (auto &Path : InnerPathMapIt.second) {
                    auto EndArgs2 = filterVars(swapIndex(Program),
                                               FreeVarsMap.at(StartIndex));
                    auto EndArgs =
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
                        EndInvariant = mainInvariant(StartIndex, Args, FunName);
                    } else {
                        EndInvariant = invariant(StartIndex, StartIndex,
                                                 FreeVarsMap.at(StartIndex),
                                                 Args, Both, FunName);
                    }
                    auto DontLoopInvariant = dontLoopInvariant(
                        EndInvariant, StartIndex, OtherPathMap, FreeVarsMap,
                        swapIndex(Program), For == First ? Second : First);
                    auto Defs = assignmentsOnPath(Path, Program,
                                                  FreeVarsMap.at(EndIndex),
                                                  EndIndex == EXIT_MARK);
                    Paths.push_back(
                        assertForall(nonmutualSMT(DontLoopInvariant, Defs, For),
                                     FreeVarsMap.at(StartIndex), StartIndex,
                                     Both, FunName, Main));
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
                                              bool ToEnd) {
    auto FilteredFreeVars = filterVars(Program, FreeVars);

    vector<AssignmentCallBlock> AllDefs;
    set<string> Constructed;
    vector<CallInfo> CallInfos;

    auto StartDefs = blockAssignments(Path.Start, nullptr, true, false, Program,
                                      Constructed);
    AllDefs.push_back(AssignmentCallBlock(StartDefs, nullptr));

    auto Prev = Path.Start;

    unsigned int i = 0;
    for (auto Edge : Path.Edges) {
        i++;
        bool Last = i == Path.Edges.size();
        auto Defs = blockAssignments(Edge.Block, Prev, false, Last && !ToEnd,
                                     Program, Constructed);
        AllDefs.push_back(AssignmentCallBlock(Defs, Edge.Condition));
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
                             vector<string> FunArgs1, vector<string> FunArgs2) {
    SMTRef Clause = EndClause;
    auto SplitAssignments1 = splitAssignments(AssignmentCallBlocks1);
    auto SplitAssignments2 = splitAssignments(AssignmentCallBlocks2);
    auto AssignmentBlocks1 = SplitAssignments1.first;
    auto AssignmentBlocks2 = SplitAssignments2.first;
    auto CallInfo1 = SplitAssignments1.second;
    auto CallInfo2 = SplitAssignments2.second;

    assert(AssignmentBlocks1.size() == CallInfo1.size() + 1);
    assert(AssignmentBlocks2.size() == CallInfo2.size() + 1);
    assert(AssignmentCallBlocks1.size() >= 1);
    assert(AssignmentCallBlocks2.size() >= 1);

    vector<vector<AssignmentBlock>> MutualBlocks1;
    vector<vector<AssignmentBlock>> MutualBlocks2;
    int MutualSize = std::min(static_cast<int>(AssignmentBlocks1.size()),
                              static_cast<int>(AssignmentBlocks2.size()));
    MutualBlocks1.insert(MutualBlocks1.end(), AssignmentBlocks1.begin(),
                         std::next(AssignmentBlocks1.begin(), MutualSize));
    MutualBlocks2.insert(MutualBlocks2.end(), AssignmentBlocks2.begin(),
                         std::next(AssignmentBlocks2.begin(), MutualSize));
    vector<CallInfo> MutualCallInfo1;
    vector<CallInfo> MutualCallInfo2;
    MutualCallInfo1.insert(
        MutualCallInfo1.end(), CallInfo1.begin(),
        std::next(CallInfo1.begin(), std::max(MutualSize - 1, 0)));
    MutualCallInfo2.insert(
        MutualCallInfo2.end(), CallInfo2.begin(),
        std::next(CallInfo2.begin(), std::max(MutualSize - 1, 0)));

    auto CallIt1 = MutualCallInfo1.rbegin();
    auto CallIt2 = MutualCallInfo2.rbegin();
    vector<vector<AssignmentBlock>> NonMutualBlocks;
    vector<CallInfo> NonMutualCallInfo;
    auto NonMutual = SMTFor::Both;
    vector<string> NonMutualFunArgs;

    if (AssignmentBlocks1.size() > AssignmentBlocks2.size()) {
        NonMutual = SMTFor::First;
        NonMutualBlocks.insert(NonMutualBlocks.end(),
                               std::next(AssignmentBlocks1.begin(), MutualSize),
                               AssignmentBlocks1.end());
        NonMutualCallInfo.insert(NonMutualCallInfo.end(),
                                 std::next(CallInfo1.begin(), MutualSize - 1),
                                 CallInfo1.end());
        NonMutualFunArgs = FunArgs1;
    } else if (AssignmentBlocks2.size() > AssignmentBlocks1.size()) {
        NonMutual = SMTFor::Second;
        NonMutualBlocks.insert(NonMutualBlocks.end(),
                               std::next(AssignmentBlocks2.begin(), MutualSize),
                               AssignmentBlocks2.end());
        NonMutualCallInfo.insert(NonMutualCallInfo.end(),
                                 std::next(CallInfo2.begin(), MutualSize - 1),
                                 CallInfo2.end());
        NonMutualFunArgs = FunArgs2;
    }

    if (NonMutual != Both) {
        auto CallIt = NonMutualCallInfo.rbegin();
        for (auto AssgnsVec : makeReverse(NonMutualBlocks)) {
            for (auto Assgns : makeReverse(AssgnsVec)) {
                Clause = nestLets(Clause, Assgns.Definitions);
                if (Assgns.Condition) {
                    Clause = makeBinOp("=>", Assgns.Condition, Clause);
                }
            }
            if (CallIt != NonMutualCallInfo.rend()) {
                Clause = nonmutualRecursiveForall(Clause, CallIt->Args,
                                                  CallIt->AssignedTo, NonMutual,
                                                  CallIt->CallName);
                ++CallIt;
            }
        }
    }

    bool First = true;
    for (auto It :
         makeZip(makeReverse(MutualBlocks1), makeReverse(MutualBlocks2))) {
        if (First) {
            First = false;
        } else {
            assert(CallIt1->CallName == CallIt2->CallName);
            Clause = mutualRecursiveForall(
                Clause, CallIt1->Args, CallIt2->Args, CallIt1->AssignedTo,
                CallIt2->AssignedTo, CallIt1->CallName);
            ++CallIt1;
            ++CallIt2;
        }
        for (auto Assgns : makeReverse(It.second)) {
            Clause = nestLets(Clause, Assgns.Definitions);
            if (Assgns.Condition) {
                Clause = makeBinOp("=>", Assgns.Condition, Clause);
            }
        }
        for (auto Assgns : makeReverse(It.first)) {
            Clause = nestLets(Clause, Assgns.Definitions);
            if (Assgns.Condition) {
                Clause = makeBinOp("=>", Assgns.Condition, Clause);
            }
        }
    }
    return Clause;
}

SMTRef nonmutualSMT(SMTRef EndClause,
                    vector<AssignmentCallBlock> AssignmentCallBlocks,
                    SMTFor For) {
    SMTRef Clause = EndClause;
    auto SplitAssignments = splitAssignments(AssignmentCallBlocks);
    auto AssignmentBlocks = SplitAssignments.first;
    auto CallInfos = SplitAssignments.second;
    assert(AssignmentBlocks.size() == CallInfos.size() + 1);
    bool first = true;
    auto CallIt = CallInfos.rbegin();
    for (auto AssgnsVec : makeReverse(AssignmentBlocks)) {
        if (first) {
            first = false;
        } else {
            Clause = nonmutualRecursiveForall(Clause, CallIt->Args,
                                              CallIt->AssignedTo, For,
                                              CallIt->CallName);
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
                 vector<string> EndArgs, SMTFor SMTFor, std::string FunName) {
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
    vector<string> EndArgsVect;
    for (auto Arg : FilteredArgs) {
        EndArgsVect.push_back(Arg + "_old");
    }
    EndArgsVect.insert(EndArgsVect.end(), ResultArgs.begin(), ResultArgs.end());

    auto EndInvariant =
        makeOp(invariantName(StartIndex, SMTFor, FunName), EndArgsVect);
    auto Clause = EndInvariant;

    if (EndIndex != EXIT_MARK) {
        // We require the result of another call to establish our invariant so
        // make sure that it satisfies the invariant of the other call and then
        // assert our own invariant
        vector<SortedVar> ForallArgs;
        for (auto ResultArg : ResultArgs) {
            ForallArgs.push_back(SortedVar(ResultArg, "Int"));
        }

        vector<string> UsingArgsVect;
        UsingArgsVect.insert(UsingArgsVect.begin(), FilteredEndArgs.begin(),
                             FilteredEndArgs.end());
        auto PreInv = makeOp(invariantName(EndIndex, SMTFor, FunName) + "_PRE",
                             UsingArgsVect);
        UsingArgsVect.insert(UsingArgsVect.end(), ResultArgs.begin(),
                             ResultArgs.end());
        Clause =
            makeBinOp("=>", makeOp(invariantName(EndIndex, SMTFor, FunName),
                                   UsingArgsVect),
                      Clause);
        if (SMTFor == Both) {
            Clause = makeBinOp("and", PreInv, Clause);
        }
        Clause = make_shared<Forall>(ForallArgs, Clause);
    }
    return Clause;
}

SMTRef mainInvariant(int EndIndex, vector<string> FreeVars, string FunName) {
    if (EndIndex == EXIT_MARK) {
        return makeBinOp("=", "result$1", "result$2");
    }
    return makeOp(invariantName(EndIndex, Both, FunName) + "_MAIN", FreeVars);
}

/// Declare an invariant
std::pair<SMTRef, SMTRef> invariantDeclaration(int BlockIndex,
                                               vector<string> FreeVars,
                                               SMTFor For,
                                               std::string FunName) {
    auto NumArgs = FreeVars.size() + 1 + (For == Both ? 1 : 0);
    vector<string> Args(NumArgs, "Int");
    vector<string> PreArgs(FreeVars.size(), "Int");

    return std::make_pair(
        std::make_shared<class Fun>(invariantName(BlockIndex, For, FunName),
                                    Args, "Bool"),
        std::make_shared<class Fun>(
            invariantName(BlockIndex, For, FunName) + "_PRE", PreArgs, "Bool"));
}

SMTRef mainInvariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                SMTFor For, std::string FunName) {
    auto NumArgs = FreeVars.size();
    vector<string> Args(NumArgs, "Int");

    return std::make_shared<class Fun>(
        invariantName(BlockIndex, For, FunName) + "_MAIN", Args, "Bool");
}

/// Return the invariant name, special casing the entry block
string invariantName(int Index, SMTFor For, std::string FunName) {
    string Name;
    if (Index == ENTRY_MARK) {
        Name = "INV_REC_" + FunName;
    } else {
        Name = "INV_" + std::to_string(Index);
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
                         SMTFor For) {
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
        auto Defs =
            assignmentsOnPath(Path, Program, FreeVars.at(StartIndex), false);
        auto SMT = nonmutualSMT(name("false"), Defs, For);
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

SMTRef mutualRecursiveForall(SMTRef Clause, vector<SMTRef> Args1,
                             vector<SMTRef> Args2, std::string Ret1,
                             std::string Ret2, std::string FunName) {
    vector<SortedVar> Args;
    Args.push_back(SortedVar(Ret1, "Int"));
    Args.push_back(SortedVar(Ret2, "Int"));
    vector<SMTRef> ImplArgs;
    vector<SMTRef> PreArgs;

    for (auto Arg : Args1) {
        ImplArgs.push_back(Arg);
    }
    for (auto Arg : Args2) {
        ImplArgs.push_back(Arg);
    }
    PreArgs.insert(PreArgs.end(), ImplArgs.begin(), ImplArgs.end());

    ImplArgs.push_back(name(Ret1));
    ImplArgs.push_back(name(Ret2));
    Clause =
        makeBinOp("=>", std::make_shared<Op>(
                            invariantName(ENTRY_MARK, Both, FunName), ImplArgs),
                  Clause);
    Clause = make_shared<Forall>(Args, Clause);
    auto PreInv = std::make_shared<Op>(
        invariantName(ENTRY_MARK, Both, FunName) + "_PRE", PreArgs);
    return makeBinOp("and", PreInv, Clause);
}

SMTRef nonmutualRecursiveForall(SMTRef Clause, vector<SMTRef> Args,
                                std::string Ret, SMTFor For,
                                std::string FunName) {
    vector<SortedVar> ForallArgs;
    vector<SMTRef> ImplArgs;
    vector<SMTRef> PreArgs;

    ForallArgs.push_back(SortedVar(Ret, "Int"));

    ImplArgs.insert(ImplArgs.end(), Args.begin(), Args.end());
    PreArgs.insert(PreArgs.end(), Args.begin(), Args.end());

    ImplArgs.push_back(name(Ret));

    Clause =
        makeBinOp("=>", make_shared<Op>(invariantName(ENTRY_MARK, For, FunName),
                                        ImplArgs),
                  Clause);
    Clause = make_shared<Forall>(ForallArgs, Clause);
    auto PreInv = std::make_shared<Op>(
        invariantName(ENTRY_MARK, For, FunName) + "_PRE", PreArgs);
    return makeBinOp("and", PreInv, Clause);
}

/// Wrap the clause in a forall
SMTRef assertForall(SMTRef Clause, vector<string> FreeVars, int BlockIndex,
                    SMTFor For, std::string FunName, bool Main) {
    vector<SortedVar> Vars;
    vector<string> PreVars;
    for (auto &Arg : FreeVars) {
        // TODO(moritz): detect type
        Vars.push_back(SortedVar(Arg + "_old", "Int"));
        PreVars.push_back(Arg + "_old");
    }

    if (Vars.empty()) {
        return make_shared<Assert>(Clause);
    }

    SMTRef PreInv;
    if (Main && BlockIndex == ENTRY_MARK) {
        vector<SMTRef> Assgns;
        assert(FreeVars.size() % 2 == 0);
        size_t mid = FreeVars.size() / 2;
        for (size_t i = 0; i < mid; i++) {
            Assgns.push_back(makeBinOp("=", FreeVars.at(i) + "_old",
                                       FreeVars.at(mid + i) + "_old"));
        }
        Clause = makeBinOp("=>", make_shared<Op>("and", Assgns), Clause);
    } else {
        auto PreInv = makeOp(invariantName(BlockIndex, For, FunName) +
                                 (Main ? "_MAIN" : "_PRE"),
                             PreVars);

        Clause = makeBinOp("=>", PreInv, Clause);
    }

    return make_shared<Assert>(make_shared<Forall>(Vars, Clause));
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SMTRef makeFunArgsEqual(SMTRef Clause, SMTRef PreClause, set<string> Args1,
                        set<string> Args2) {
    vector<SMTRef> Args;
    assert(Args1.size() == Args2.size());
    for (auto ArgPair : makeZip(Args1, Args2)) {
        Args.push_back(makeBinOp("=", ArgPair.first, ArgPair.second));
    }

    auto And = make_shared<Op>("and", Args);

    return makeBinOp("=>", And, makeBinOp("and", Clause, PreClause));
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(vector<string> FunArgs, vector<string> FunArgs1,
                               vector<string> FunArgs2, std::string FunName) {
    vector<SortedVar> ForallArgs;
    vector<string> Args;
    vector<string> PreInvArgs;
    Args.insert(Args.end(), FunArgs.begin(), FunArgs.end());
    PreInvArgs = Args;

    for (auto Arg : FunArgs) {
        ForallArgs.push_back(SortedVar(Arg, "Int"));
    }
    ForallArgs.push_back(SortedVar("result$1", "Int"));
    ForallArgs.push_back(SortedVar("result$2", "Int"));
    Args.push_back("result$1");
    Args.push_back("result$2");

    auto EqualResults =
        makeBinOp("=>", makeOp(invariantName(ENTRY_MARK, Both, FunName), Args),
                  makeBinOp("=", "result$1", "result$2"));
    auto PreInv =
        makeOp(invariantName(ENTRY_MARK, Both, FunName) + "_PRE", PreInvArgs);

    set<string> FunArgs1Set, FunArgs2Set;
    std::copy(FunArgs1.begin(), FunArgs1.end(),
              std::inserter(FunArgs1Set, FunArgs1Set.end()));
    std::copy(FunArgs2.begin(), FunArgs2.end(),
              std::inserter(FunArgs2Set, FunArgs2Set.end()));

    auto EqualArgs =
        makeFunArgsEqual(EqualResults, PreInv, FunArgs1Set, FunArgs2Set);
    auto ForallInputs = make_shared<Forall>(ForallArgs, EqualArgs);
    return make_shared<Assert>(ForallInputs);
}

/* -------------------------------------------------------------------------- */
// Functions related to the conversion of single instructions/basic blocks to
// SMT assignments

/// Convert a basic block to a list of assignments
vector<DefOrCallInfo> blockAssignments(const llvm::BasicBlock *BB,
                                       const llvm::BasicBlock *PrevBB,
                                       bool IgnorePhis, bool OnlyPhis,
                                       int Program, set<string> &Constructed) {
    vector<DefOrCallInfo> Definitions;
    assert(BB->size() >=
           1); // There should be at least a terminator instruction
    for (auto Instr = BB->begin(), E = std::prev(BB->end(), 1); Instr != E;
         ++Instr) {
        assert(!Instr->getType()->isVoidTy());
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!IgnorePhis && llvm::isa<llvm::PHINode>(Instr)) {
            Definitions.push_back(
                DefOrCallInfo(instrAssignment(*Instr, PrevBB, Constructed)));
            Constructed.insert(Instr->getName());
        }
        if (!OnlyPhis && !llvm::isa<llvm::PHINode>(Instr)) {
            if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(Instr)) {
                Definitions.push_back(DefOrCallInfo(
                    toCallInfo(CallInst->getName(), CallInst, Constructed)));
            } else {
                Definitions.push_back(DefOrCallInfo(
                    instrAssignment(*Instr, PrevBB, Constructed)));
            }
            Constructed.insert(Instr->getName());
        }
    }
    if (auto RetInst = llvm::dyn_cast<llvm::ReturnInst>(BB->getTerminator())) {
        string RetName = RetInst->getReturnValue()->getName();
        if (Constructed.find(RetName) == Constructed.end()) {
            RetName += "_old";
        }
        Definitions.push_back(
            DefOrCallInfo(make_shared<std::tuple<string, SMTRef>>(
                "result$" + std::to_string(Program), name(RetName))));
    }
    return Definitions;
}

/// Convert a single instruction to an assignment
std::shared_ptr<std::tuple<string, SMTRef>>
instrAssignment(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
                set<string> &Constructed) {
    if (auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        return make_shared<std::tuple<string, SMTRef>>(
            BinOp->getName(),
            makeBinOp(
                opName(*BinOp),
                instrNameOrVal(BinOp->getOperand(0),
                               BinOp->getOperand(0)->getType(), Constructed),
                instrNameOrVal(BinOp->getOperand(1),
                               BinOp->getOperand(1)->getType(), Constructed)));
    }
    if (auto CmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto Cmp = makeBinOp(
            predicateName(CmpInst->getPredicate()),
            instrNameOrVal(CmpInst->getOperand(0),
                           CmpInst->getOperand(0)->getType(), Constructed),
            instrNameOrVal(CmpInst->getOperand(1),
                           CmpInst->getOperand(0)->getType(), Constructed));
        return make_shared<std::tuple<string, SMTRef>>(CmpInst->getName(), Cmp);
    }
    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return make_shared<std::tuple<string, SMTRef>>(
            PhiInst->getName(),
            instrNameOrVal(Val, Val->getType(), Constructed));
    }
    if (auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        auto Cond = SelectInst->getCondition();
        auto TrueVal = SelectInst->getTrueValue();
        auto FalseVal = SelectInst->getFalseValue();
        vector<SMTRef> Args = {
            instrNameOrVal(Cond, Cond->getType(), Constructed),
            instrNameOrVal(TrueVal, TrueVal->getType(), Constructed),
            instrNameOrVal(FalseVal, FalseVal->getType(), Constructed)};
        return make_shared<std::tuple<string, SMTRef>>(
            SelectInst->getName(), std::make_shared<class Op>("ite", Args));
    }
    llvm::errs() << Instr << "\n";
    llvm::errs() << "Couldn't convert instruction to def\n";
    return make_shared<std::tuple<string, SMTRef>>("UNKNOWN INSTRUCTION",
                                                   name("UNKNOWN ARGS"));
}

/// Convert an LLVM predicate to an SMT predicate
string predicateName(llvm::CmpInst::Predicate Pred) {
    switch (Pred) {
    case CmpInst::ICMP_SLT:
        return "<";
    case CmpInst::ICMP_SLE:
        return "<=";
    case CmpInst::ICMP_EQ:
        return "=";
    case CmpInst::ICMP_SGE:
        return ">=";
    case CmpInst::ICMP_SGT:
        return ">";
    case CmpInst::ICMP_NE:
        return "distinct";
    default:
        return "unsupported predicate";
    }
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
    default:
        return Op.getOpcodeName();
    }
}

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef instrNameOrVal(const llvm::Value *Val, const llvm::Type *Ty,
                      set<string> &Constructed) {
    if (auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        auto ApInt = ConstInt->getValue();
        if (ApInt.isIntN(1) && Ty->isIntegerTy(1)) {
            return name(ApInt.getBoolValue() ? "true" : "false");
        }
        if (ApInt.isNegative()) {
            return makeUnaryOp(
                "-", name(ApInt.toString(10, true).substr(1, string::npos)));
        }
        return name(ApInt.toString(10, true));
    }
    if (Constructed.find(Val->getName()) == Constructed.end()) {
        string Name = Val->getName();
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
    // set<string> ConstructedIntersection;
    for (auto &Paths : PathMap) {
        for (auto &Path : Paths.second) {
            llvm::BasicBlock *Prev = Path.Start;
            set<string> Constructed;

            // the first block is special since we can't resolve phi
            // nodes here
            for (auto &Instr : *Path.Start) {
                Constructed.insert(Instr.getName());
                if (llvm::isa<llvm::PHINode>(Instr)) {
                    FreeVars.insert(Instr.getName());
                    continue;
                }
                if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                    for (unsigned int i = 0; i < CallInst->getNumArgOperands();
                         i++) {
                        auto Arg = CallInst->getArgOperand(i);
                        if (!Arg->getName().empty() &&
                            Constructed.find(Arg->getName()) ==
                                Constructed.end()) {
                            FreeVars.insert(Arg->getName());
                        }
                    }
                    continue;
                }
                for (auto Op : Instr.operand_values()) {
                    if (Constructed.find(Op->getName()) == Constructed.end() &&
                        !Op->getName().empty()) {
                        FreeVars.insert(Op->getName());
                    }
                }
            }

            // now deal with the rest
            for (auto &Edge : Path.Edges) {
                for (auto &Instr : *Edge.Block) {
                    Constructed.insert(Instr.getName());
                    if (auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
                        auto Incoming = PhiInst->getIncomingValueForBlock(Prev);
                        if (Constructed.find(Incoming->getName()) ==
                                Constructed.end() &&
                            !Incoming->getName().empty()) {
                            FreeVars.insert(Incoming->getName());
                        }
                        continue;
                    }
                    if (auto CallInst =
                            llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                        for (unsigned int i = 0;
                             i < CallInst->getNumArgOperands(); i++) {
                            auto Arg = CallInst->getArgOperand(i);
                            if (!Arg->getName().empty() &&
                                Constructed.find(Arg->getName()) ==
                                    Constructed.end()) {
                                FreeVars.insert(Arg->getName());
                            }
                        }
                        continue;
                    }
                    for (auto Op : Instr.operand_values()) {
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
                                       vector<string> FunArgs) {
    std::map<int, set<string>> FreeVarsMap;
    std::map<int, vector<string>> FreeVarsMapVect;
    std::map<int, std::map<int, set<string>>> Constructed;
    for (auto &It : Map1) {
        int Index = It.first;
        auto FreeVars1 = freeVarsForBlock(Map1.at(Index));
        auto FreeVars2 = freeVarsForBlock(Map2.at(Index));
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
    // search for a least fixpoint
    // don't tell anyone I wrote that
    bool Changed = true;
    while (Changed) {
        Changed = false;
        for (auto &It : Map1) {
            int StartIndex = It.first;
            for (auto &ItInner : It.second) {
                int EndIndex = ItInner.first;
                for (auto Var : FreeVarsMap.at(EndIndex)) {
                    if (Constructed.at(StartIndex).at(EndIndex).find(Var) ==
                        Constructed.at(StartIndex).at(EndIndex).end()) {
                        auto Inserted = FreeVarsMap.at(StartIndex).insert(Var);
                        Changed = Inserted.second;
                    }
                }
            }
        }
    }

    for (auto It : FreeVarsMap) {
        int Index = It.first;
        vector<string> VarsVect;
        for (auto Var : It.second) {
            VarsVect.push_back(Var);
        }
        vector<string> Vars1 = filterVars(1, VarsVect);
        vector<string> Vars2 = filterVars(2, VarsVect);
        vector<string> Vars;
        Vars.insert(Vars.end(), Vars1.begin(), Vars1.end());
        Vars.insert(Vars.end(), Vars2.begin(), Vars2.end());
        FreeVarsMapVect[Index] = Vars;
    }
    FreeVarsMapVect[ENTRY_MARK] = FunArgs;

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
    string ProgramName = std::to_string(Program);
    for (auto Var : Vars) {
        auto Pos = Var.rfind("$");
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
                AssignmentBlocks.push_back(CurrentAssignmentsList);
                CurrentAssignmentsList.clear();
                Condition = nullptr;
                CallInfos.push_back(*DefOrCall.CallInfo);
            }
        }
        CurrentAssignmentsList.push_back(
            AssignmentBlock(CurrentDefinitions, Condition));
    }
    AssignmentBlocks.push_back(CurrentAssignmentsList);
    return make_pair(AssignmentBlocks, CallInfos);
}

std::shared_ptr<CallInfo> toCallInfo(string AssignedTo,
                                     const llvm::CallInst *CallInst,
                                     set<string> &Constructed) {
    vector<SMTRef> Args;
    unsigned int i = 0;
    auto FunTy = CallInst->getFunctionType();
    for (auto &Arg : CallInst->arg_operands()) {

        Args.push_back(
            instrNameOrVal(Arg, FunTy->getParamType(i), Constructed));
        ++i;
    }
    return make_shared<CallInfo>(
        AssignedTo, CallInst->getCalledFunction()->getName(), Args);
}
