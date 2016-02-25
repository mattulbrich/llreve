#include "Memory.h"
#include "Opts.h"

using std::vector;
using std::make_shared;
using std::string;
using smt::SMTRef;
using smt::SortedVar;
using smt::Forall;

std::vector<std::string> resolveHeapReferences(std::vector<std::string> args,
                                               string suffix, Memory &heap) {
    heap = 0;
    vector<string> result;
    for (auto arg : args) {
        std::smatch matchResult;
        if (std::regex_match(arg, matchResult, HEAP_REGEX) && !MuZFlag) {
            const string i = matchResult[2];
            string index = "i" + i;
            if (matchResult[1] == "STACK") {
                index += "_stack";
            }
            result.push_back(index);
            result.push_back("(select " + arg + suffix + " " + index + ")");
            heap |= HEAP_MASK;
        } else if ((arg == "HEAP$1_res" || arg == "HEAP$2_res") && !MuZFlag) {
            const string index = "i" + arg.substr(5, 6);
            result.push_back(index);
            result.push_back("(select " + arg + " " + index + ")");
            heap |= HEAP_MASK;
        } else {
            if (arg == "result$1" || arg == "result$2") {
                result.push_back(arg);
            } else {
                result.push_back(arg + suffix);
            }
        }
    }
    return result;
}

SMTRef wrapHeap(SMTRef inv, Memory heap, vector<string> freeVars) {
    if (!heap || MuZFlag) {
        return inv;
    }
    std::vector<SortedVar> args;
    for (auto var : freeVars) {
        if (std::regex_match(var, INDEX_REGEX)) {
            args.push_back(SortedVar(var, "Int"));
        }
        if (var == "STACK$1" || var == "STACK$2") {
            args.push_back(SortedVar(var, "(Array Int Int)"));
        }
    }
    return make_shared<Forall>(args, inv);
}

unsigned long adaptSizeToHeap(unsigned long size, vector<string> freeVars) {
    if (MuZFlag) {
        return size;
    }
    if (std::find(freeVars.begin(), freeVars.end(), "HEAP$1") !=
        freeVars.end()) {
        size++;
    }
    if (std::find(freeVars.begin(), freeVars.end(), "STACK$1") !=
        freeVars.end()) {
        size++;
    }
    if (std::find(freeVars.begin(), freeVars.end(), "HEAP$2") !=
        freeVars.end()) {
        size++;
    }
    if (std::find(freeVars.begin(), freeVars.end(), "STACK$2") !=
        freeVars.end()) {
        size++;
    }
    return size;
}
