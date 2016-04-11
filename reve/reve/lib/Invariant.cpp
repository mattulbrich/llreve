#include "Invariant.h"

#include "Helper.h"
#include "Opts.h"

using std::vector;
using std::make_shared;
using std::unique_ptr;
using std::string;
using smt::makeOp;
using smt::stringExpr;
using smt::SharedSMTRef;
using smt::SMTRef;
using smt::SMTExpr;
using smt::SortedVar;
using smt::Forall;
using smt::FunDecl;

using std::map;

/* -------------------------------------------------------------------------- */
// Functions related to generating invariants

SMTRef invariant(int StartIndex, int EndIndex, vector<string> InputArgs,
                 vector<string> EndArgs, ProgramSelection SMTFor,
                 std::string FunName, Memory memory,
                 map<int, vector<string>> freeVarsMap) {
    // we want to end up with something like
    // (and pre (=> (nextcall newargs res) (currentcall oldargs res)))
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
    if (memory & HEAP_MASK) {
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
    // Arguments passed into the current invariant
    vector<string> EndArgsVect;
    for (const string &arg : FilteredArgs) {
        EndArgsVect.push_back(arg + "_old");
    }
    EndArgsVect.insert(EndArgsVect.end(), ResultArgs.begin(), ResultArgs.end());
    EndArgsVect = fillUpArgs(EndArgsVect, freeVarsMap, memory, SMTFor,
                             InvariantAttr::NONE);
    // The current invariant
    SMTRef Clause =
        makeOp(invariantName(StartIndex, SMTFor, FunName), EndArgsVect);

    if (EndIndex != EXIT_MARK) {
        // The result of another call is required to establish the current
        // invariant
        // so we do do that call and use the result in the current invariant
        vector<SortedVar> ForallArgs;
        for (auto ResultArg : ResultArgs) {
            ForallArgs.push_back(SortedVar(ResultArg, argSort(ResultArg)));
        }
        if (EndIndex != UNREACHABLE_MARK) {
            vector<string> usingArgsPre;
            usingArgsPre.insert(usingArgsPre.begin(), FilteredEndArgs.begin(),
                                FilteredEndArgs.end());
            vector<string> usingArgs = usingArgsPre;
            usingArgsPre = fillUpArgs(usingArgsPre, freeVarsMap, memory, SMTFor,
                                      InvariantAttr::PRE);
            SMTRef PreInv = makeOp(
                invariantName(EndIndex, SMTFor, FunName, InvariantAttr::PRE),
                usingArgsPre);
            usingArgs.insert(usingArgs.end(), ResultArgs.begin(),
                             ResultArgs.end());
            usingArgs = fillUpArgs(usingArgs, freeVarsMap, memory, SMTFor,
                                   InvariantAttr::NONE);
            Clause =
                makeBinOp("=>", makeOp(invariantName(EndIndex, SMTFor, FunName),
                                       usingArgs),
                          std::move(Clause));
            if (SMTFor == ProgramSelection::Both) {
                Clause = makeBinOp("and", std::move(PreInv), std::move(Clause));
            }
        }
        Clause = llvm::make_unique<Forall>(ForallArgs, std::move(Clause));
    }
    return Clause;
}

SMTRef mainInvariant(int EndIndex, vector<string> FreeVars, string FunName) {
    if (EndIndex == EXIT_MARK) {
        vector<string> Args = {"result$1", "result$2"};
        for (string& arg : FreeVars) {
            // No stack in output
            if (arg.compare(0,5,"STACK")) {
                Args.push_back(arg);
            }
        }
        return makeOp("OUT_INV", Args);
    }
    if (EndIndex == UNREACHABLE_MARK) {
        return stringExpr("true");
    }
    return makeOp(invariantName(EndIndex, ProgramSelection::Both, FunName,
                                InvariantAttr::MAIN),
                  FreeVars);
}

/// Declare an invariant
MonoPair<SMTRef> invariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                      ProgramSelection For, std::string FunName,
                                      Memory Heap) {
    vector<string> args;
    for (const string &arg : FreeVars) {
        if (std::regex_match(arg, HEAP_REGEX)) {
            args.push_back("(Array Int Int)");
        } else {
            args.push_back("Int");
        }
    }
    const vector<string> preArgs = args;
    // add results
    args.push_back("Int");
    if (For == ProgramSelection::Both) {
        args.push_back("Int");
    }
    if (Heap) {
        args.push_back("(Array Int Int)");
        if (For == ProgramSelection::Both) {
            args.push_back("(Array Int Int)");
        }
    }

    return makeMonoPair<SMTRef>(
        llvm::make_unique<FunDecl>(invariantName(BlockIndex, For, FunName),
                                   args, "Bool"),
        llvm::make_unique<FunDecl>(
            invariantName(BlockIndex, For, FunName, InvariantAttr::PRE),
            preArgs, "Bool"));
}

MonoPair<SMTRef>
singleInvariantDeclaration(map<int, vector<string>> freeVarsMap, Memory memory,
                           ProgramSelection prog, std::string funName) {
    size_t numArgs = maxArgs(freeVarsMap, memory, prog, InvariantAttr::NONE);
    size_t numPreArgs = maxArgs(freeVarsMap, memory, prog, InvariantAttr::PRE);
    numArgs++;
    numPreArgs++;
    const vector<string> args(numArgs, "Int");
    const vector<string> preArgs(numPreArgs, "Int");
    string name = "INV_REC_" + funName;
    if (prog != ProgramSelection::Both) {
        string index = std::to_string(programIndex(asProgram(prog)));
        name += "__" + index;
    }
    const string preName = name + "_PRE";

    return makeMonoPair<SMTRef>(
        llvm::make_unique<class FunDecl>(name, args, "Bool"),
        llvm::make_unique<class FunDecl>(preName, preArgs, "Bool"));
}

size_t invariantArgs(vector<string> freeVars, Memory memory,
                     ProgramSelection prog, InvariantAttr attr) {
    size_t numArgs = freeVars.size();
    if (attr == InvariantAttr::NONE) {
        // we need result arguments
        // + 1 for each result
        numArgs += 1 + (prog == ProgramSelection::Both ? 1 : 0);
        if (memory) {
            // index + value at that index
            if (prog == ProgramSelection::Both) {
                numArgs += 2;
            } else {
                numArgs += 1;
            }
        }
    }
    return numArgs;
}

SharedSMTRef singleMainInvariant(map<int, vector<string>> freeVarsMap,
                                 Memory memory, ProgramSelection prog) {
    size_t numArgs = maxArgs(freeVarsMap, memory, prog, InvariantAttr::MAIN);
    numArgs++;
    const vector<string> args(numArgs, "Int");
    return std::make_shared<class FunDecl>("INV_MAIN", args, "Bool");
}

size_t maxArgs(map<int, vector<string>> freeVarsMap, Memory memory,
               ProgramSelection prog, InvariantAttr attr) {
    size_t maxArgs = 0;
    for (auto It : freeVarsMap) {
        size_t numArgs = invariantArgs(It.second, memory, prog, attr);
        if (numArgs > maxArgs) {
            maxArgs = numArgs;
        }
    }
    return maxArgs;
}

SharedSMTRef mainInvariantDeclaration(int BlockIndex, vector<string> FreeVars,
                                      ProgramSelection For,
                                      std::string FunName) {
    vector<string> Args;
    for (const string &arg : FreeVars) {
        if (std::regex_match(arg, HEAP_REGEX)) {
            Args.push_back("(Array Int Int)");
        } else {
            Args.push_back("Int");
        }
    }

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
        if (!SMTGenerationOpts::getInstance().SingleInvariant) {
            Name += "_" + std::to_string(Index);
        }
    } else {
        if (SMTGenerationOpts::getInstance().SingleInvariant ||
            Index == ENTRY_MARK) {
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
    if (SMTGenerationOpts::getInstance().SingleInvariant) {
        string indexString = std::to_string(abs(Index));
        if (Index < 0) {
            indexString = "(- " + indexString + ")";
        }
        Name += " " + indexString;
    }
    return Name;
}

vector<SharedSMTRef> fillUpArgs(vector<SharedSMTRef> args,
                                map<int, vector<string>> freeVarsMap,
                                Memory mem, ProgramSelection prog,
                                InvariantAttr attr) {
    SharedSMTRef fillConstant = stringExpr("424242");
    return fillUpArgsWithFiller(fillConstant, args, freeVarsMap, mem, prog,
                                attr);
}

vector<string> fillUpArgs(vector<string> args,
                          map<int, vector<string>> freeVarsMap, Memory mem,
                          ProgramSelection prog, InvariantAttr attr) {
    return fillUpArgsWithFiller<std::string>("424242", args, freeVarsMap, mem,
                                             prog, attr);
}
