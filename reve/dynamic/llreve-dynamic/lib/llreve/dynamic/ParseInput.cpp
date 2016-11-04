/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/ParseInput.h"

#include <fstream>

// Each line contains one set of input values
// The format of a single line is
// vars1|vars2|heapbackground1|heapbackground2|heap1|heap2| where vars1 and
// vars2
// are semicolon separated list of numbers in the order the functions receive
// them and heap1 and heap2 are semicolon separated lists of comma separated
// tuples representing the heap index and the heap value

using std::vector;
using std::string;

using llreve::opts::SMTGenerationOpts;

namespace llreve {
namespace dynamic {
vector<WorkItem> parseInput(string fileName) {
    vector<WorkItem> result;
    string line;
    std::ifstream fileStream(fileName.c_str());
    int i = 0;
    while (std::getline(fileStream, line)) {
        // split at '|'
        vector<string> parts = split(line, '|');
        if (parts.size() == 0) {
            return result;
        }
        assert(parts.size() == 6);
        result.push_back(
            {{getVariables(parts.at(0)), getVariables(parts.at(1))},
             {mpz_class(parts.at(2)), mpz_class(parts.at(3))},
             {getHeap(parts.at(4)), getHeap(parts.at(5))},
             true,
             i});
        ++i;
    }
    return result;
}

std::vector<mpz_class> getVariables(std::string line) {
    // split at ';'
    vector<string> parts = split(line, ';');
    vector<mpz_class> result;
    for (auto p : parts) {
        mpz_class val(p);
        result.push_back(val);
    }
    return result;
}

Heap getHeap(std::string line) {
    // split at ';'
    vector<string> parts = split(line, ';');
    Heap result;
    for (auto p : parts) {
        vector<string> pairParts = split(p, ',');
        assert(pairParts.size() == 2);
        mpz_class index(pairParts.at(0));
        mpz_class val(pairParts.at(1));
        Integer intVal;
        if (SMTGenerationOpts::getInstance().BitVect) {
            intVal = Integer(makeBoundedInt(8, val.get_si()));
        } else {
            intVal = Integer(val);
        }
        result.insert({Integer(index).asPointer(), intVal});
    }
    return result;
}
}
}
