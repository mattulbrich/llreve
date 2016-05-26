#pragma once

#include <vector>
#include <string>
#include "llvm/IR/LegacyPassManager.h"

std::shared_ptr<llvm::Module> getModuleFromFile(std::string fileName, std::string resourceDir = "", std::vector<std::string> includes = {});
