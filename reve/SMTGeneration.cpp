#include "SMTGeneration.h"

#include "Compat.h"
#include "MarkAnalysis.h"

#include "llvm/IR/Constants.h"

using llvm::CmpInst;

#include <iostream>

std::vector<SMTRef> convertToSMT(llvm::Function &Fun1, llvm::Function &Fun2,
                                 unique_ptr<llvm::FunctionAnalysisManager> Fam1,
                                 unique_ptr<llvm::FunctionAnalysisManager> Fam2,
                                 bool OffByN) {
    // TODO(moritz): check that the marks are the same
    auto PathMap1 = Fam1->getResult<PathAnalysis>(Fun1);
    auto PathMap2 = Fam2->getResult<PathAnalysis>(Fun2);
    auto Marked1 = Fam1->getResult<MarkAnalysis>(Fun1);
    auto Marked2 = Fam2->getResult<MarkAnalysis>(Fun2);
    std::pair<std::vector<string>, std::vector<string>> FunArgsPair =
        functionArgs(Fun1, Fun2);
    set<string> FunArgs;
    for (auto Arg : FunArgsPair.first) {
        FunArgs.insert(Arg);
    }
    for (auto Arg : FunArgsPair.second) {
        FunArgs.insert(Arg);
    }
    std::map<int, set<string>> FreeVarsMap =
        freeVars(PathMap1, PathMap2, FunArgs);
    std::vector<SMTRef> SMTExprs;
    std::vector<SMTRef> PathExprs;

    SMTExprs.push_back(std::make_shared<SetLogic>("HORN"));

    // we only need pre invariants for mutual invariants
    auto Invariants = invariantDeclaration(-1, FunArgs, Both);
    SMTExprs.push_back(Invariants.first);
    SMTExprs.push_back(Invariants.second);
    SMTExprs.push_back(
        invariantDeclaration(-1, filterVars(1, FunArgs), First).first);
    SMTExprs.push_back(
        invariantDeclaration(-1, filterVars(2, FunArgs), Second).first);

    auto SynchronizedPaths = synchronizedPaths(
        PathMap1, PathMap2, FreeVarsMap, FunArgsPair.first, FunArgsPair.second);

    // add invariant defs
    SMTExprs.insert(SMTExprs.end(), SynchronizedPaths.first.begin(),
                    SynchronizedPaths.first.end());

    // assert equal outputs for equal inputs
    SMTExprs.push_back(equalInputsEqualOutputs(FunArgs, FunArgsPair.first,
                                               FunArgsPair.second));

    // add actual path smts
    PathExprs.insert(PathExprs.end(), SynchronizedPaths.second.begin(),
                     SynchronizedPaths.second.end());

    // generate forbidden paths
    PathExprs.push_back(make_shared<Comment>("FORBIDDEN PATHS"));
    auto ForbiddenPaths =
        forbiddenPaths(PathMap1, PathMap2, FreeVarsMap, FunArgsPair.first,
                       FunArgsPair.second, OffByN);
    PathExprs.insert(PathExprs.end(), ForbiddenPaths.begin(),
                     ForbiddenPaths.end());

    if (OffByN) {
        // generate off by n paths
        PathExprs.push_back(make_shared<Comment>("OFF BY N"));
        auto OffByNPaths = offByNPaths(PathMap1, PathMap2, FreeVarsMap,
                                       FunArgsPair.first, FunArgsPair.second);
        PathExprs.insert(PathExprs.end(), OffByNPaths.begin(),
                         OffByNPaths.end());
    }

    SMTExprs.insert(SMTExprs.end(), PathExprs.begin(), PathExprs.end());

    SMTExprs.push_back(make_shared<CheckSat>());
    SMTExprs.push_back(make_shared<GetModel>());

    return SMTExprs;
}

/* -------------------------------------------------------------------------- */
// Generate SMT for all paths

std::pair<std::vector<SMTRef>, std::vector<SMTRef>>
synchronizedPaths(PathMap PathMap1, PathMap PathMap2,
                  std::map<int, set<string>> FreeVarsMap,
                  std::vector<string> FunArgs1, std::vector<string> FunArgs2) {
    std::vector<SMTRef> InvariantDefs;
    std::vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != -1) {
            // ignore entry node
            auto Invariants = invariantDeclaration(
                StartIndex, FreeVarsMap.at(StartIndex), Both);
            InvariantDefs.push_back(Invariants.first);
            InvariantDefs.push_back(Invariants.second);
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            auto Paths = PathMap2.at(StartIndex).at(EndIndex);
            for (auto &Path1 : InnerPathMapIt.second) {
                for (auto &Path2 : Paths) {
                    auto EndInvariant = invariant(
                        StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                        FreeVarsMap.at(EndIndex), Both);
                    auto Defs1 = assignmentsOnPath(
                        Path1, 1, FreeVarsMap.at(EndIndex), EndIndex == -2);
                    auto Defs2 = assignmentsOnPath(
                        Path2, 2, FreeVarsMap.at(EndIndex), EndIndex == -2);
                    PathExprs.push_back(assertForall(
                        interleaveAssignments(EndInvariant, Defs1, Defs2,
                                              FunArgs1, FunArgs2),
                        FreeVarsMap.at(StartIndex), StartIndex, Both));
                }
            }
        }
    }
    nonmutualPaths(PathMap1, PathExprs, InvariantDefs, FreeVarsMap, FunArgs1,
                   First);
    nonmutualPaths(PathMap2, PathExprs, InvariantDefs, FreeVarsMap, FunArgs2,
                   Second);

    return make_pair(InvariantDefs, PathExprs);
}

std::vector<SMTRef> forbiddenPaths(PathMap PathMap1, PathMap PathMap2,
                                   std::map<int, set<string>> FreeVarsMap,
                                   std::vector<string> FunArgs1,
                                   std::vector<string> FunArgs2, bool OffByN) {
    std::vector<SMTRef> PathExprs;
    for (auto &PathMapIt : PathMap1) {
        int StartIndex = PathMapIt.first;
        for (auto &InnerPathMapIt1 : PathMapIt.second) {
            int EndIndex1 = InnerPathMapIt1.first;
            for (auto &InnerPathMapIt2 : PathMap2.at(StartIndex)) {
                auto EndIndex2 = InnerPathMapIt2.first;
                if (EndIndex1 != EndIndex2) {
                    for (auto &Path1 : InnerPathMapIt1.second) {
                        for (auto &Path2 : InnerPathMapIt2.second) {
                            if (!OffByN ||
                                !(StartIndex == EndIndex1 ||
                                  StartIndex == EndIndex2)) {
                                auto Smt2 = assignmentsOnPath(
                                    Path2, 2, set<string>(), EndIndex2 == -2);
                                auto Smt1 = assignmentsOnPath(
                                    Path1, 1, set<string>(), EndIndex1 == -2);
                                auto SMT = nonmutualSMT(name("false"), Smt2,
                                                        FunArgs2, Second);
                                SMT = nonmutualSMT(SMT, Smt1, FunArgs1, First);
                                PathExprs.push_back(assertForall(
                                    SMT, FreeVarsMap.at(StartIndex), StartIndex,
                                    Both));
                            }
                        }
                    }
                }
            }
        }
    }
    return PathExprs;
}

void nonmutualPaths(PathMap PathMap, std::vector<SMTRef> &PathExprs,
                    std::vector<SMTRef> &InvariantDefs,
                    std::map<int, set<string>> FreeVarsMap,
                    std::vector<string> FunArgs, SMTFor For) {
    int Program = For == First ? 1 : 2;
    for (auto &PathMapIt : PathMap) {
        int StartIndex = PathMapIt.first;
        if (StartIndex != -1) {
            auto Invariants = invariantDeclaration(
                StartIndex, filterVars(Program, FreeVarsMap.at(StartIndex)),
                For);
            InvariantDefs.push_back(Invariants.first);
            if (For == Both) {
                InvariantDefs.push_back(Invariants.second);
            }
        }
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            for (auto &Path : InnerPathMapIt.second) {
                auto EndInvariant1 =
                    invariant(StartIndex, EndIndex, FreeVarsMap.at(StartIndex),
                              FreeVarsMap.at(EndIndex), For);
                auto Defs = assignmentsOnPath(
                    Path, Program, FreeVarsMap.at(EndIndex), EndIndex == -2);
                PathExprs.push_back(assertForall(
                    nonmutualSMT(EndInvariant1, Defs, FunArgs, For),
                    filterVars(Program, FreeVarsMap.at(StartIndex)), StartIndex,
                    For));
            }
        }
    }
}

std::vector<SMTRef> offByNPaths(PathMap PathMap1, PathMap PathMap2,
                                std::map<int, set<string>> FreeVarsMap,
                                std::vector<string> FunArgs1,
                                std::vector<string> FunArgs2) {
    std::vector<SMTRef> Paths;
    auto FirstPaths = offByNPathsOneDir(PathMap1, PathMap2, FreeVarsMap, FunArgs1, FunArgs2, 1, First);
    auto SecondPaths =
        offByNPathsOneDir(PathMap2, PathMap1, FreeVarsMap, FunArgs2, FunArgs1, 2, Second);
    Paths.insert(Paths.end(), FirstPaths.begin(), FirstPaths.end());
    Paths.insert(Paths.end(), SecondPaths.begin(), SecondPaths.end());
    return Paths;
}

std::vector<SMTRef> offByNPathsOneDir(PathMap PathMap_, PathMap OtherPathMap,
                                      std::map<int, set<string>> FreeVarsMap,
                                      std::vector<string> FunArgs,
                                      std::vector<string> OtherFunArgs, int Program, SMTFor For) {
    std::vector<SMTRef> Paths;
    for (auto &PathMapIt : PathMap_) {
        int StartIndex = PathMapIt.first;
        for (auto &InnerPathMapIt : PathMapIt.second) {
            int EndIndex = InnerPathMapIt.first;
            if (StartIndex == EndIndex) {
                // we found a loop
                for (auto &Path : InnerPathMapIt.second) {
                    auto EndArgs2 = filterVars(swapIndex(Program), FreeVarsMap.at(StartIndex));
                    auto EndArgs = filterVars(Program, FreeVarsMap.at(StartIndex));
                    for (auto Arg : EndArgs2) {
                        EndArgs.insert(Arg + "_old");
                    }
                    auto EndInvariant =
                        invariant(StartIndex, StartIndex,
                                  FreeVarsMap.at(StartIndex), EndArgs, Both);
                    auto DontLoopInvariant = dontLoopInvariant(
                        EndInvariant, StartIndex, OtherPathMap, FreeVarsMap,
                        OtherFunArgs, swapIndex(Program), For == First ? Second : First);
                    auto Defs = assignmentsOnPath(
                        Path, Program, FreeVarsMap.at(EndIndex), EndIndex == -2);
                    Paths.push_back(assertForall(
                        nonmutualSMT(DontLoopInvariant, Defs, FunArgs, For),
                        FreeVarsMap.at(StartIndex), StartIndex, Both));
                }
            }
        }
    }
    return Paths;
}

/* -------------------------------------------------------------------------- */
// Functions for generating SMT for a single/mutual path

std::vector<AssignmentCallBlock>
assignmentsOnPath(Path Path, int Program, std::set<std::string> FreeVars,
                  bool ToEnd) {
    auto FilteredFreeVars = filterVars(Program, FreeVars);

    std::vector<AssignmentCallBlock> AllDefs;
    set<string> Constructed;
    std::vector<CallInfo> CallInfos;

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

    std::vector<DefOrCallInfo> OldDefs;
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

SMTRef interleaveAssignments(
    SMTRef EndClause, std::vector<AssignmentCallBlock> AssignmentCallBlocks1,
    std::vector<AssignmentCallBlock> AssignmentCallBlocks2,
    std::vector<string> FunArgs1, std::vector<string> FunArgs2) {
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

    std::vector<std::vector<AssignmentBlock>> MutualBlocks1;
    std::vector<std::vector<AssignmentBlock>> MutualBlocks2;
    int MutualSize = std::min(static_cast<int>(AssignmentBlocks1.size()),
                              static_cast<int>(AssignmentBlocks2.size()));
    MutualBlocks1.insert(MutualBlocks1.end(), AssignmentBlocks1.begin(),
                         std::next(AssignmentBlocks1.begin(), MutualSize));
    MutualBlocks2.insert(MutualBlocks2.end(), AssignmentBlocks2.begin(),
                         std::next(AssignmentBlocks2.begin(), MutualSize));
    std::vector<CallInfo> MutualCallInfo1;
    std::vector<CallInfo> MutualCallInfo2;
    MutualCallInfo1.insert(
        MutualCallInfo1.end(), CallInfo1.begin(),
        std::next(CallInfo1.begin(), std::max(MutualSize - 1, 0)));
    MutualCallInfo2.insert(
        MutualCallInfo2.end(), CallInfo2.begin(),
        std::next(CallInfo2.begin(), std::max(MutualSize - 1, 0)));

    auto CallIt1 = MutualCallInfo1.rbegin();
    auto CallIt2 = MutualCallInfo2.rbegin();
    std::vector<std::vector<AssignmentBlock>> NonMutualBlocks;
    std::vector<CallInfo> NonMutualCallInfo;
    auto NonMutual = SMTFor::Both;
    std::vector<string> NonMutualFunArgs;

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
                                                  CallIt->AssignedTo,
                                                  NonMutualFunArgs, NonMutual);
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
            Clause = mutualRecursiveForall(
                Clause, CallIt1->Args, CallIt2->Args, CallIt1->AssignedTo,
                CallIt2->AssignedTo, FunArgs1, FunArgs2);
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
                    std::vector<AssignmentCallBlock> AssignmentCallBlocks,
                    std::vector<string> FunArgs, SMTFor For) {
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
                                              CallIt->AssignedTo, FunArgs, For);
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

SMTRef invariant(int StartIndex, int EndIndex, set<string> InputArgs,
                 set<string> EndArgs, SMTFor SMTFor) {
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
    std::vector<string> ResultArgs;
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
    std::vector<string> EndArgsVect;
    for (auto Arg : FilteredArgs) {
        EndArgsVect.push_back(Arg + "_old");
    }
    EndArgsVect.insert(EndArgsVect.end(), ResultArgs.begin(), ResultArgs.end());

    auto EndInvariant = makeOp(invariantName(StartIndex, SMTFor), EndArgsVect);
    auto Clause = EndInvariant;

    if (EndIndex != -2) {
        // We require the result of another call to establish our invariant so
        // make sure that it satisfies the invariant of the other call and then
        // assert our own invariant
        std::vector<SortedVar> ForallArgs;
        for (auto ResultArg : ResultArgs) {
            ForallArgs.push_back(SortedVar(ResultArg, "Int"));
        }

        std::vector<string> UsingArgsVect;
        UsingArgsVect.insert(UsingArgsVect.begin(), FilteredEndArgs.begin(),
                             FilteredEndArgs.end());
        auto PreInv =
            makeOp(invariantName(EndIndex, SMTFor) + "_PRE", UsingArgsVect);
        UsingArgsVect.insert(UsingArgsVect.end(), ResultArgs.begin(),
                             ResultArgs.end());
        Clause = makeBinOp(
            "=>", makeOp(invariantName(EndIndex, SMTFor), UsingArgsVect),
            Clause);
        if (SMTFor == Both) {
            Clause = makeBinOp("and", PreInv, Clause);
        }
        Clause = make_shared<Forall>(ForallArgs, Clause);
    }
    return Clause;
}

/// Declare an invariant
std::pair<SMTRef, SMTRef>
invariantDeclaration(int BlockIndex, set<string> FreeVars, SMTFor For) {
    // Add two arguments for the result args
    auto NumArgs = FreeVars.size() + 1 + (For == Both ? 1 : 0);
    std::vector<string> Args(NumArgs, "Int");
    std::vector<string> PreArgs(FreeVars.size(), "Int");

    return std::make_pair(
        std::make_shared<class Fun>(invariantName(BlockIndex, For), Args,
                                    "Bool"),
        std::make_shared<class Fun>(invariantName(BlockIndex, For) + "_PRE",
                                    PreArgs, "Bool"));
}

/// Return the invariant name, special casing the entry block
string invariantName(int Index, SMTFor For) {
    string Name;
    if (Index == -1) {
        Name = "INV_REC";
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
                         std::map<int, set<string>> FreeVars,
                         std::vector<string> FunArgs, int Program, SMTFor For) {
    auto Clause = EndClause;
    std::vector<Path> DontLoopPaths;
    for (auto PathMapIt : PathMap.at(StartIndex)) {
        if (PathMapIt.first == StartIndex) {
            for (auto Path : PathMapIt.second) {
                DontLoopPaths.push_back(Path);
            }
        }
    }
    std::vector<SMTRef> DontLoopExprs;
    for (auto Path : DontLoopPaths) {
        auto Defs =
            assignmentsOnPath(Path, Program, FreeVars.at(StartIndex), false);
        auto SMT = nonmutualSMT(name("false"), Defs, FunArgs, For);
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

SMTRef mutualRecursiveForall(SMTRef Clause, std::vector<SMTRef> Args1,
                             std::vector<SMTRef> Args2, std::string Ret1,
                             std::string Ret2, std::vector<string> FunArgs1,
                             std::vector<string> FunArgs2) {
    assert(Args1.size() == Args2.size());
    assert(FunArgs1.size() == FunArgs2.size());
    assert(Args1.size() == FunArgs1.size());
    // we sort the arguments alphabetically by the corresponding function
    // argument name
    std::vector<SortedVar> Args;
    Args.push_back(SortedVar(Ret1, "Int"));
    Args.push_back(SortedVar(Ret2, "Int"));
    std::vector<std::pair<string, SMTRef>> ToSort;
    std::vector<SMTRef> ImplArgs;
    for (size_t i = 0; i < Args1.size(); i++) {
        ToSort.push_back(make_pair(FunArgs1.at(i), Args1.at(i)));
    }
    for (size_t i = 0; i < Args2.size(); i++) {
        ToSort.push_back(make_pair(FunArgs2.at(i), Args2.at(i)));
    }

    std::sort(ToSort.begin(), ToSort.end());

    for (auto Pair : ToSort) {
        ImplArgs.push_back(Pair.second);
    }
    ImplArgs.push_back(name(Ret1));
    ImplArgs.push_back(name(Ret2));
    Clause = makeBinOp(
        "=>", std::make_shared<Op>(invariantName(-1, Both), ImplArgs), Clause);
    return make_shared<Forall>(Args, Clause);
}

SMTRef nonmutualRecursiveForall(SMTRef Clause, std::vector<SMTRef> Args,
                                std::string Ret, std::vector<string> FunArgs,
                                SMTFor For) {
    assert(Args.size() == FunArgs.size());
    std::vector<SortedVar> ForallArgs;
    std::vector<SMTRef> ImplArgs;
    ForallArgs.push_back(SortedVar(Ret, "Int"));
    std::vector<std::pair<string, SMTRef>> ToSort;
    for (size_t i = 0; i < Args.size(); i++) {
        ToSort.push_back(make_pair(FunArgs.at(i), Args.at(i)));
    }
    std::sort(ToSort.begin(), ToSort.end());
    for (auto Pair : ToSort) {
        ImplArgs.push_back(Pair.second);
    }
    ImplArgs.push_back(name(Ret));
    // TODO(moritz): Pass in the name
    Clause = makeBinOp("=>", make_shared<Op>(invariantName(-1, For), ImplArgs),
                       Clause);
    return make_shared<Forall>(ForallArgs, Clause);
}

/// Wrap the clause in a forall
SMTRef assertForall(SMTRef Clause, set<string> FreeVars, int BlockIndex,
                    SMTFor For) {
    std::vector<SortedVar> Vars;
    std::vector<string> PreVars;
    for (auto &Arg : FreeVars) {
        // TODO(moritz): detect type
        Vars.push_back(SortedVar(Arg + "_old", "Int"));
        PreVars.push_back(Arg + "_old");
    }

    if (Vars.empty()) {
        return Clause;
    }

    if (For == Both) {
        auto PreInv = makeOp(invariantName(BlockIndex, For) + "_PRE", PreVars);
        Clause = makeBinOp("=>", PreInv, Clause);
    }
    return make_shared<Assert>(make_shared<Forall>(Vars, Clause));
}

/* -------------------------------------------------------------------------- */
// Functions forcing arguments to be equal

SMTRef makeFunArgsEqual(SMTRef Clause, SMTRef PreClause, set<string> Args1,
                        set<string> Args2) {
    std::vector<SMTRef> Args;
    assert(Args1.size() == Args2.size());
    for (auto ArgPair : makeZip(Args1, Args2)) {
        Args.push_back(makeBinOp("=", ArgPair.first, ArgPair.second));
    }

    auto And = make_shared<Op>("and", Args);

    return makeBinOp("=>", And, makeBinOp("and", Clause, PreClause));
}

/// Create an assertion to require that if the recursive invariant holds and the
/// arguments are equal the outputs are equal
SMTRef equalInputsEqualOutputs(set<string> FunArgs,
                               std::vector<string> FunArgs1,
                               std::vector<string> FunArgs2) {
    std::vector<SortedVar> ForallArgs;
    std::vector<string> Args;
    std::vector<string> PreInvArgs;
    Args.insert(Args.end(), FunArgs.begin(), FunArgs.end());
    PreInvArgs = Args;

    for (auto Arg : FunArgs) {
        ForallArgs.push_back(SortedVar(Arg, "Int"));
    }
    ForallArgs.push_back(SortedVar("result$1", "Int"));
    ForallArgs.push_back(SortedVar("result$2", "Int"));
    Args.push_back("result$1");
    Args.push_back("result$2");

    auto EqualResults = makeBinOp("=>", makeOp(invariantName(-1, Both), Args),
                                  makeBinOp("=", "result$1", "result$2"));
    auto PreInv = makeOp(invariantName(-1, Both) + "_PRE", PreInvArgs);

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
std::vector<DefOrCallInfo> blockAssignments(const llvm::BasicBlock *BB,
                                            const llvm::BasicBlock *PrevBB,
                                            bool IgnorePhis, bool OnlyPhis,
                                            int Program,
                                            set<string> &Constructed) {
    std::vector<DefOrCallInfo> Definitions;
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
        std::vector<SMTRef> Args = {
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

std::map<int, set<string>> freeVars(PathMap Map1, PathMap Map2,
                                    set<string> FunArgs) {
    std::map<int, set<string>> FreeVarsMap;
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
                FreeVars1.second.at(MapIt.first).insert(Var);
            }
        }

        Constructed.insert(make_pair(Index, FreeVars1.second));
    }

    for (auto Arg : FunArgs) {
        FreeVarsMap.at(-1).insert(Arg);
    }
    FreeVarsMap.insert(make_pair(-2, set<string>()));

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

    return FreeVarsMap;
}

/* -------------------------------------------------------------------------- */
// Miscellanous helper functions that don't really belong anywhere

std::pair<std::vector<string>, std::vector<string>>
functionArgs(llvm::Function &Fun1, llvm::Function &Fun2) {
    std::vector<string> Args1;
    for (auto &Arg : Fun1.args()) {
        Args1.push_back(Arg.getName());
    }
    std::vector<string> Args2;
    for (auto &Arg : Fun2.args()) {
        Args2.push_back(Arg.getName());
    }
    return std::make_pair(Args1, Args2);
}

/// Filter vars to only include the ones from Program
set<string> filterVars(int Program, set<string> Vars) {
    set<string> FilteredVars;
    string ProgramName = std::to_string(Program);
    for (auto Var : Vars) {
        auto Pos = Var.rfind("$");
        if (Var.substr(Pos + 1, ProgramName.length()) == ProgramName) {
            FilteredVars.insert(Var);
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
std::pair<std::vector<std::vector<AssignmentBlock>>, std::vector<CallInfo>>
splitAssignments(std::vector<AssignmentCallBlock> AssignmentCallBlocks) {
    std::vector<std::vector<AssignmentBlock>> AssignmentBlocks;
    std::vector<CallInfo> CallInfos;
    std::vector<struct AssignmentBlock> CurrentAssignmentsList;
    for (auto Assignments : AssignmentCallBlocks) {
        SMTRef Condition = Assignments.Condition;
        std::vector<Assignment> CurrentDefinitions;
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
    std::vector<SMTRef> Args;
    unsigned int i = 0;
    auto FunTy = CallInst->getFunctionType();
    for (auto &Arg : CallInst->arg_operands()) {

        Args.push_back(
            instrNameOrVal(Arg, FunTy->getParamType(i), Constructed));
        ++i;
    }
    return make_shared<CallInfo>(AssignedTo, "unknown function", Args);
}
