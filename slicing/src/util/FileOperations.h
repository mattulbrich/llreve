/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include <vector>
#include <string>
#include "llvm/IR/LegacyPassManager.h"

std::shared_ptr<llvm::Module> getModuleFromSource(std::string fileName, std::string resourceDir = "", std::vector<std::string> includes = {});
void writeModuleToFile(std::string fileName, llvm::Module& module);
void writeModuleToFileDbg(std::string fileName, llvm::Module& module);
