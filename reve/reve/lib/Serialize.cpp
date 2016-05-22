#include "Serialize.h"

#include <fstream>
#include <iostream>

void serializeSMT(std::vector<smt::SharedSMTRef> smtExprs, bool muZ,
                  SerializeOpts opts) {
    // write to file or to stdout
    std::streambuf *buf;
    std::ofstream ofStream;

    if (!opts.OutputFileName.empty()) {
        ofStream.open(opts.OutputFileName);
        buf = ofStream.rdbuf();
    } else {
        buf = std::cout.rdbuf();
    }

    std::ostream outFile(buf);

    for (auto &smt : smtExprs) {
        if (muZ) {
            outFile << *smt->compressLets()->mergeImplications({})->toSExpr();
        } else {
            if (opts.DontInstantiate) {
                outFile << *smt->compressLets()->toSExpr();
            } else {
                outFile << *smt->compressLets()->instantiateArrays()->toSExpr();
            }
        }
        outFile << "\n";
    }

    if (!opts.OutputFileName.empty()) {
        ofStream.close();
    }
}
