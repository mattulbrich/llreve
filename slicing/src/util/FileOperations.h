#pragma once

#include <vector>
#include <string>
#include "llvm/IR/LegacyPassManager.h"

std::shared_ptr<llvm::Module> getModuleFromSource(std::string fileName, std::string resourceDir = "", std::vector<std::string> includes = {});
void writeModuleToFile(std::string fileName, llvm::Module& module);
