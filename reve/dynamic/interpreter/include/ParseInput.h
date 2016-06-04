#pragma once

#include "SerializeTraces.h"

std::vector<WorkItem> parseInput(std::string fileName);

std::vector<mpz_class> getVariables(std::string line);
Heap getHeap(std::string line);

std::vector<std::string> &split(const std::string &s, char delim,
                                std::vector<std::string> &elems);

std::vector<std::string> split(const std::string &s, char delim);
