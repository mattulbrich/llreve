#include "Invariant.h"

#include "Helper.h"
#include "Opts.h"

using std::vector;
using std::make_shared;
using std::string;
using smt::makeOp;
using smt::name;
using smt::SMTRef;
using smt::SortedVar;
using smt::Forall;
using smt::FunDecl;

using std::map;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

SMTRef invariant(int StartIndex, int EndIndex, vector<string> InputArgs,
                 vector<string> EndArgs, ProgramSelection SMTFor,
                 std::string FunName, Memory Heap) {
    // This is the actual invariant we want to establish
    auto FilteredArgs = InputArgs;
    auto FilteredEndArgs = EndArgs;
    if (SMTFor == ProgramSelection::First) {
        FilteredArgs = filterVars(1, FilteredArgs);
        FilteredEndArgs = filterVars(1, FilteredEndArgs);
    }
    if (SMTFor == ProgramSelection::Second) {
        FilteredArgs = filterVars(2, FilteredArgs);
        FilteredEndArgs = filterVars(2, FilteredEndArgs);
    }
    vector<string> ResultArgs;
    switch (SMTFor) {
    case ProgramSelection::First:
        ResultArgs.push_back("result$1");
        break;
    case ProgramSelection::Second:
        ResultArgs.push_back("result$2");
        break;
    case ProgramSelection::Both:
        ResultArgs.push_back("result$1");
        ResultArgs.push_back("result$2");
        break;
    }
    if (Heap & HEAP_MASK) {
        switch (SMTFor) {
        case ProgramSelection::First:
            ResultArgs.push_back("HEAP$1_res");
            break;
        case ProgramSelection::Second:
            ResultArgs.push_back("HEAP$2_res");
            break;
        case ProgramSelection::Both:
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
        // We require the result of another call to establish our invariant
        // so
        // make sure that it satisfies the invariant of the other call and
        // then
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
            const auto PreInv = makeOp(
                invariantName(EndIndex, SMTFor, FunName, InvariantAttr::PRE),
                UsingArgsVect);
            UsingArgsVect.insert(UsingArgsVect.end(), ResultArgs.begin(),
                                 ResultArgs.end());
            UsingArgsVect = resolveHeapReferences(UsingArgsVect, "", Heap);
            Clause = makeBinOp(
                "=>", wrapHeap(makeOp(invariantName(EndIndex, SMTFor, FunName),
                                      UsingArgsVect),
                               Heap, UsingArgsVect),
                Clause);
            if (SMTFor == ProgramSelection::Both) {
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
    return wrapHeap(makeOp(invariantName(EndIndex, ProgramSelection::Both,
                                         FunName, InvariantAttr::MAIN),
                           FreeVars),
                    Heap, FreeVars);
}

/// Declare an invariant
MonoPair<SMTRef> invariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                      ProgramSelection For, std::string FunName,
                                      Memory Heap) {
    size_t NumArgs = invariantArgs(FreeVars, Heap, For, false);
    const vector<string> Args(NumArgs, "Int");
    const vector<string> PreArgs(
        NumArgs - (For == ProgramSelection::Both ? 2 : 1) -
            (Heap ? (For == ProgramSelection::Both ? 4 : 2) : 0),
        "Int");

    return makeMonoPair<SMTRef>(
        std::make_shared<class FunDecl>(invariantName(BlockIndex, For, FunName),
                                        Args, "Bool"),
        std::make_shared<class FunDecl>(
            invariantName(BlockIndex, For, FunName, InvariantAttr::PRE),
            PreArgs, "Bool"));
}

size_t invariantArgs(vector<string> freeVars, Memory memory,
                     ProgramSelection prog, bool main) {
    auto numArgs = freeVars.size();
    if (!main) {
        // we need result arguments
        // + 1 for each result
        numArgs += 1 + (prog == ProgramSelection::Both ? 1 : 0);
        if (memory) {
            // index + value at that index
            if (prog == ProgramSelection::Both) {
                numArgs += 4;
            } else {
                numArgs += 2;
            }
        }
    }
    return adaptSizeToHeap(numArgs, freeVars);
}

SMTRef singleMainInvariant(map<int, vector<string>> freeVarsMap, Memory memory,
                           ProgramSelection prog) {
    size_t maxArgs = 0;
    for (auto It : freeVarsMap) {
        size_t numArgs = invariantArgs(It.second, memory, prog, true);
        if (numArgs > maxArgs) {
            maxArgs = numArgs;
        }
    }
    maxArgs++;
    const vector<string> Args(maxArgs, "Int");
    return std::make_shared<class FunDecl>("INV_MAIN", Args, "Bool");
}

SMTRef mainInvariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                ProgramSelection For, std::string FunName) {
    auto NumArgs = FreeVars.size();
    NumArgs = adaptSizeToHeap(NumArgs, FreeVars);
    const vector<string> Args(NumArgs, "Int");

    return std::make_shared<class FunDecl>(
        invariantName(BlockIndex, For, FunName, InvariantAttr::MAIN), Args,
        "Bool");
}

/// Return the invariant name, special casing the entry block
string invariantName(int Index, ProgramSelection For, std::string FunName,
                     InvariantAttr attr, uint32_t VarArgs) {
    string Name;
    if (attr == InvariantAttr::MAIN) {
        Name = "INV_MAIN";
        if (!SingleInvariantFlag) {
            Name += "_" + std::to_string(Index);
        }
    } else {
        if (SingleInvariantFlag || Index == ENTRY_MARK) {
            Name = "INV_REC_" + FunName;
        } else {
            Name = "INV_" + std::to_string(Index);
        }
    }

    if (VarArgs > 0) {
        Name += "_" + std::to_string(VarArgs) + "varargs";
    }
    if (For == ProgramSelection::First) {
        Name += "__1";
    } else if (For == ProgramSelection::Second) {
        Name += "__2";
    }
    if (attr == InvariantAttr::PRE) {
        Name += "_PRE";
    }
    if (SingleInvariantFlag) {
        string indexString = std::to_string(abs(Index));
        if (Index < 0) {
            indexString = "(- " + indexString + ")";
        }
        Name += " " + indexString;
    }
    return Name;
}
