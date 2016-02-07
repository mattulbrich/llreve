#pragma once

#include "SMT.h"

#include <unistd.h>
#include <regex>

using Memory = uint8_t;
const uint8_t HEAP_MASK = 0x01;
const uint8_t STACK_MASK = 0x02;

auto resolveHeapReferences(std::vector<std::string> Args, std::string Suffix,
                           Memory &Heap) -> std::vector<std::string>;
auto wrapHeap(SMTRef Inv, Memory Heap, std::vector<std::string> FreeVars)
    -> SMTRef;
auto adaptSizeToHeap(unsigned long Size, std::vector<string> FreeVars)
    -> unsigned long;

const std::regex HEAP_REGEX =
    std::regex("^(HEAP|STACK)\\$(1|2)(_old)?$", std::regex::ECMAScript);
const std::regex INDEX_REGEX =
    std::regex("^i(1|2)(_res|_old|_stack)?$", std::regex::ECMAScript);
