#include "SerializeTraces.h"

#include "Interpreter.h"
#include "ThreadSafeQueue.h"

#include <fstream>
#include <iostream>
#include <thread>

using std::vector;
using std::string;
using std::make_shared;
using std::map;

using llvm::Function;

void serializeValuesInRange(MonoPair<const Function *> funs,
                            VarIntVal lowerBound, VarIntVal upperBound,
                            string outputDirectory) {
    assert(!(funs.first->isVarArg() || funs.second->isVarArg()));
    vector<VarIntVal> argValues;
    vector<string> varNames;
    for (auto &arg : funs.first->args()) {
        // The variables are already renamed so we need to remove the suffix
        std::string varName = arg.getName();
        size_t i = varName.find_first_of('$');
        varNames.push_back(varName.substr(0, i));
    }
    ThreadSafeQueue<WorkItem> q;
    unsigned int n = std::thread::hardware_concurrency();
    vector<std::thread> threads(n);
    for (size_t i = 0; i < n; ++i) {
        threads[i] = std::thread([&q, varNames, funs, outputDirectory]() {
            workerThread(funs, q, varNames, outputDirectory);
        });
    }
    int counter = 0;
    for (const auto &vals : Range(lowerBound, upperBound, varNames.size())) {
        q.push({vals, counter});
        counter++;
    }
    for (size_t i = 0; i < n; ++i) {
        q.push({{}, -1});
    }
    for (auto &t : threads) {
        if (t.joinable()) {
            t.join();
        } else {
            std::cout << "not joinable " << t.get_id() << "\n";
        }
    }
}

Range::RangeIterator Range::begin() {
    vector<VarIntVal> vals(n);
    std::cout << "lowerBound " << lowerBound.get_str() << ", upperBound "
              << upperBound.get_str() << "\n";
    if (lowerBound > upperBound) {
        return end();
    }
    for (size_t i = 0; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator Range::end() {
    vector<VarIntVal> vals(n);
    vals[0] = upperBound + 1;
    for (size_t i = 1; i < vals.size(); ++i) {
        vals[i] = lowerBound;
    }
    return RangeIterator(lowerBound, upperBound, vals);
}

Range::RangeIterator &Range::RangeIterator::operator++() {
    VarIntVal carry = 1;
    size_t index = 0;
    while (carry == 1 && index < vals.size()) {
        vals[index]++;
        if (vals[index] == upperBound + 1) {
            carry = 1;
            vals[index] = lowerBound;
        } else {
            carry = 0;
        }
        ++index;
    }
    if (carry == 1) {
        vals[0] = upperBound + 1;
    }
    return *this;
}

void workerThread(MonoPair<const llvm::Function *> funs,
                  ThreadSafeQueue<WorkItem> &q,
                  const std::vector<string> varNames,
                  std::string outputDirectory) {
    for (WorkItem item = q.pop(); item.counter >= 0; item = q.pop()) {
        map<string, std::shared_ptr<VarVal>> map;

        for (size_t i = 0; i < item.vals.size(); ++i) {
            map.insert({varNames[i], make_shared<VarInt>(item.vals[i])});
        }
        Heap heap;
        MonoPair<Call<const llvm::Value *>> calls =
            interpretFunctionPair(funs, map, heap, 10000);

        std::string baseName = outputDirectory + "/";
        baseName += funs.first->getName();
        baseName += "_";
        calls.indexedForEach([&funs, item, &baseName](FastCall c, int i) {
            std::ofstream ofStream;
            std::string fileName = baseName;
            fileName += std::to_string(i) + "_" + std::to_string(item.counter) +
                        ".cbor";
            ofStream.open(fileName, std::ios::out | std::ios::binary);
            unsigned char *buffer;
            cbor_item_t *root = c.toCBOR();
            size_t bufferSize;
            size_t length = cbor_serialize_alloc(root, &buffer, &bufferSize);
            ofStream.write(reinterpret_cast<char *>(buffer),
                           static_cast<long>(length));
            free(buffer);
            cbor_decref(&root);
            ofStream.close();
        });
    }
}
