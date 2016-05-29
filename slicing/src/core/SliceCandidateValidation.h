#include "llvm/IR/Module.h"

enum class ValidationResult {valid, invalid, unknown};

class CounterExample;

extern bool CriterionPresent;

class SliceCandidateValidation {
public:
	static ValidationResult validate(llvm::Module* program, llvm::Module* candidate, CounterExample* counterExample = nullptr);
};
