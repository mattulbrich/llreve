#include "SerializeTraces.h"

#include "Interpreter.h"

#include <fstream>
#include <iostream>

using std::vector;
using std::string;
using std::make_shared;

using llvm::Function;

void serializeValuesInRange(MonoPair<const Function *> funs,
                            mpz_class lowerBound, mpz_class upperBound,
                            string outputDirectory) {
    assert(!(funs.first->isVarArg() || funs.second->isVarArg()));
    vector<mpz_class> argValues;
    vector<string> varNames;
    for (auto &arg : funs.first->args()) {
        // The variables are already renamed so we need to remove the suffix
        std::string varName = arg.getName();
        size_t i = varName.find_first_of('$');
        varNames.push_back(varName.substr(0, i));
    }
    int counter = 0;
    for (const auto &vals : Range(lowerBound, upperBound, varNames.size())) {
        VarMap map;
        for (size_t i = 0; i < vals.size(); ++i) {
            map.insert({varNames[i], make_shared<VarInt>(vals[i])});
        }
        Heap heap;
        MonoPair<Call> calls =
            interpretFunctionPair(funs, State(map, heap), 1000);
        calls.indexedForEach([outputDirectory, &funs, counter](Call c, int i) {
            std::ofstream ofStream;
            std::string fileName = outputDirectory + "/";
            fileName += funs.first->getName();
            fileName += "_" + std::to_string(i) + "_" + std::to_string(counter);
            ofStream.open(fileName);
            ofStream << c.toJSON() << std::endl;
        });
        counter++;
    }
}

Range::RangeIterator Range::begin() {
    vector<mpz_class> vals(n);
    for (size_t i = 0; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator Range::end() {
    vector<mpz_class> vals(n);
    vals[0] = upperBound + 1;
    for (size_t i = 1; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator &Range::RangeIterator::operator++() {
    if (vals[index] < upperBound) {
        vals[index]++;
        // If we are not at the last position advance
        if (index < vals.size() - 1) {
            index++;
        }
    } else {
        assert(index == vals.size() - 1);
        // Avoid signed warnings
        int i = static_cast<int>(index);
        while (i >= 0 && vals[index] == upperBound) {
            vals[index] = lowerBound;
            i--;
            index--;
        }
        if (i >= 0) {
            vals[index]++;
            index++;
        } else {
            // Now we are at the end, increment to make sure we reach end()
            vals[0] = upperBound + 1;
        }
    }

    return *this;
}
