#include "llvm/IR/Module.h"

enum ValidationResult {valide, invalide, unknown};

class CounterExample;

class SliceCandidateValidation {
public:
	static ValidationResult validate(llvm::Module* program, llvm::Module* candidate, CounterExample* counterExample = nullptr);
};
