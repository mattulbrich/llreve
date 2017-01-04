/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SyntacticSlicing.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include "core/DependencyGraphPasses.h"
#include "core/SlicingPass.h"
#include "core/SyntacticSlicePass.h"
#include "core/Util.h"
#include "core/SliceCandidateValidation.h"

using namespace std;
using namespace llvm;

shared_ptr<Module> SyntacticSlicing::computeSlice(CriterionPtr criterion) {
	ModulePtr program = getProgram();
	ModulePtr sliceCandidate = CloneModule(&*program);

	llvm::legacy::PassManager PM;
	PM.add(new llvm::PostDominatorTree());
	PM.add(new CDGPass());
	PM.add(new DDGPass());
	PM.add(new PDGPass());
	PM.add(new SyntacticSlicePass(criterion));
	PM.add(new SlicingPass());
	PM.run(*sliceCandidate);

	return sliceCandidate;
}
