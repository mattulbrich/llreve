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

    int i = 0;
    for (const auto &smt : smtExprs) {
        if (muZ) {
            outFile << *smt->compressLets()->mergeImplications({})->toSExpr();
        } else {
            smt::SharedSMTRef out = opts.Pretty ? smt->compressLets() : smt;
            if (opts.MergeImplications) {
                out = out->mergeImplications({});
            }
            if (!opts.DontInstantiate) {
                out = out->instantiateArrays();
            }
            if (opts.RenameDefineFuns) {
                out = out->renameDefineFuns("__" + std::to_string(i));
            }
            out->toSExpr()->serialize(outFile, 0, opts.Pretty);
        }
        outFile << "\n";
        ++i;
    }

    if (!opts.OutputFileName.empty()) {
        ofStream.close();
    }
}
