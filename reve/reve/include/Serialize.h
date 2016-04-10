#pragma once

#include "Opts.h"
#include "SMT.h"

void serializeSMT(std::vector<smt::SharedSMTRef> smtExprs, bool muZ,
                  SerializeOpts opts);
