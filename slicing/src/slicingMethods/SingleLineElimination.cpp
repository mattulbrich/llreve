#include "SingleLineElimination.h"

#include "core/SlicingPass.h"
#include "core/SliceCandidateValidation.h"

#include "core/Util.h"
#include "util/misc.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <set>

using namespace std;
using namespace llvm;

ModulePtr SingleLineElimination::computeSlice(CriterionPtr criterion) {
	ModulePtr program = getProgram();
	ModulePtr slice = CloneModule(&*program);
	set<Instruction*> criterionInstructions = criterion->getInstructions(*slice);

	bool changed = true;

	while (changed) {
		changed = false;

		for (Function& function:*slice) {
			if (!Util::isSpecialFunction(function)) {
				for(Instruction& instruction : Util::getInstructions(function)) {
					Type* type = instruction.getType();
					const bool isCriterion = criterionInstructions.find(&instruction) != criterionInstructions.end();
					if (!isCriterion && !isa<PHINode>(instruction) && type->isIntegerTy() && type->getIntegerBitWidth() > 1) {
						ValueToValueMapTy valueMap;
						ModulePtr impactAbstraction = CloneModule(&*slice, valueMap);

						Instruction* instToReplace = cast<Instruction>(&*valueMap[&instruction]);
						SlicingPass::toBeSliced(*instToReplace);

						llvm::legacy::PassManager PM;
						PM.add(new SlicingPass());
						PM.run(*impactAbstraction);

						ValidationResult result = SliceCandidateValidation::validate(&*slice, &*impactAbstraction, criterion);
						if (result == ValidationResult::valid) {
							SlicingPass::toBeSliced(instruction);
							slice = impactAbstraction;
							changed = true;
						}
					}
				}
			}
		}
	}



	return slice;
}
