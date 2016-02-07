#include "Memory.h"

using std::vector;
using std::make_shared;

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
