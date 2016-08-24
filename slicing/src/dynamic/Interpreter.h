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

#include "llvm/ADT/APInt.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

#include <initializer_list>
#include <list>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class TraceEntry;
class DynType;
class DynInteger;
class DynArray;
class DynPointer;

class DataSlot {
	
	public:
	
	DataSlot(llvm::Value const& creatingValue, DynType* pContent = nullptr) :
		pContent(pContent), pLastModifyingValue(&creatingValue) {}
	
	llvm::raw_ostream& print(llvm::raw_ostream& out) const;
	
	DynType*  getContent(void) const;
	DataSlot& setContent(DynType& content, llvm::Value const& modifyingValue);
	
	llvm::Value const* getLastModifyingValue(void) const;
	
	private:
	
	// The content won't be deleted in the destructor as these values are also
	// stored in the execution trace
	DynType* pContent;
	
	llvm::Value const* pLastModifyingValue;
};

class Interpreter {
	
	public:
	
	typedef std::vector<int64_t> InputType;
	
	llvm::Function const& func;
	
	std::unordered_set<llvm::Instruction const*> recentDataDependencies;
	
	Interpreter(
		llvm::Function const& func,
		InputType      const& input,
		bool           const  branchDependencies = true);
	~Interpreter(void);
	
	// Return value indicates whether the interpretation has termated before
	// 'maxStepCount' has been reached
	bool execute(
		unsigned long const maxStepCount = static_cast<unsigned long>(-1));
	
	// Return value indicates whether the execution has changed the state
	bool executeNextInstruction(void);
	
	// Provide the instructions that caused the current state and that will be
	// executed in this state
	llvm::Instruction const* getRecentInstruction(void) const;
	llvm::Instruction const* getNextInstruction  (void) const;
	
	DynType const* getReturnValue(void) const;
	
	DynType const& operator[](llvm::Value const& value) const;
	
	private:
	
	bool const _computeBranchDep;
	
	static unsigned int getValueBitWidth(llvm::Value const& value);
	
	llvm::BasicBlock::const_iterator _instIt;
	DataSlot                         _retValueSlot;
	
	llvm::BasicBlock  const* _pLastBB; // Current BB is stored via '_pNextInst'
	llvm::Instruction const* _pRecentInst;
	llvm::Instruction const* _pNextInst;
	
	std::unordered_map<llvm::Value const*, DataSlot*> _mappedState;
	std::unordered_set<DataSlot*>                     _state;
	std::list<TraceEntry const*>                      _trace;
	std::unordered_map<llvm::Value const*, DynArray*> _arrays;
	
	llvm::APInt resolveInt           (llvm::Value const* pVal);
	DataSlot*   resolvePointer       (llvm::Value const& value);
	DataSlot&   resolvePointerNotNull(llvm::Value const& value);
	
	bool tryResolveInt    (llvm::Value const& value, llvm::APInt& result);
	bool tryResolvePointer(llvm::Value const& value, DataSlot*&   result);
	
	void            moveToNextInstruction(void);
	DataSlot const& updateState(llvm::Instruction const& inst, DynType& value);
	void            addDependency(llvm::Value const& dependency);
	
	DataSlot const& updateState(
		llvm::Instruction const& inst,
		llvm::APInt       const& value);
	DataSlot const& updateState(
		llvm::Instruction const& inst,
		bool              const  value);
	DataSlot const& updateState(
		llvm::Instruction const& inst,
		DataSlot*         const  pPointedSlot);
	
	// There is special function for every instruction type
	DataSlot const* executeAllocaInst       (llvm::AllocaInst        const& inst);
	DataSlot const* executeBinaryOperator   (llvm::BinaryOperator    const& inst);
	DataSlot const* executeBranchInst       (llvm::BranchInst        const& inst);
	DataSlot const* executeCallInst         (llvm::CallInst          const& inst);
	DataSlot const* executeGetElementPtrInst(llvm::GetElementPtrInst const& inst);
	DataSlot const* executeICmpInst         (llvm::ICmpInst          const& inst);
	DataSlot const* executeLoadInst         (llvm::LoadInst          const& inst);
	DataSlot const* executePHINode          (llvm::PHINode           const& inst);
	DataSlot const* executeReturnInst       (llvm::ReturnInst        const& inst);
	DataSlot const* executeStoreInst        (llvm::StoreInst         const& inst);
};

class TraceEntry {
	
	public:
	
	// Not every instruction writes to a data slot, e.g. branch instructions
	llvm::Instruction const&       inst;
	DataSlot          const* const pSlot;
	DynType           const* const pContent;
	
	TraceEntry(llvm::Instruction const& inst, DataSlot const* const pSlot);
	
	~TraceEntry(void);
};

class DynType {
	
	public:
	
	llvm::Type::TypeID const  id;
	llvm::Value        const& parentValue;
	DataSlot*          const  pSlot;
	
	virtual ~DynType(void);
	
	DynArray   const& asArray  (void) const;
	DynInteger const& asInteger(void) const;
	DynPointer const& asPointer(void) const;
	
	DynArray&   asArray  (void);
	DynInteger& asInteger(void);
	DynPointer& asPointer(void);
	
	bool isArray  (void) const;
	bool isInteger(void) const;
	bool isPointer(void) const;
	bool isVoid   (void) const;
	
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const;
	
	protected:
	
	DynType(
		llvm::Type::TypeID const  id,
		llvm::Value        const& creatingValue,
		bool               const  createNewSlot,
		DataSlot*          const  pExistingSlot);
};

class DynInteger : public DynType {
	
	public:
	
	llvm::APInt const& value;
	
	DynInteger(
			llvm::Value const& creatingValue,
			DataSlot*   const  pSlot = nullptr) :
		DynType(llvm::Type::IntegerTyID, creatingValue, !pSlot, pSlot),
		value  (*new llvm::APInt()),
		undef  (true) {}
	
	DynInteger(
			llvm::Value const& creatingValue,
			llvm::APInt const& value,
			DataSlot*   const  pSlot = nullptr) :
		DynType(llvm::Type::IntegerTyID, creatingValue, !pSlot, pSlot),
		value  (*new llvm::APInt(value)),
		undef  (false) {}
	
	DynInteger(
			llvm::Value const& creatingValue,
			bool        const  value,
			DataSlot*   const  pSlot = nullptr) :
		DynType(llvm::Type::IntegerTyID, creatingValue, !pSlot, pSlot),
		value  (*new llvm::APInt(1, value ? 1 : 0)),
		undef  (false) {}
	
	virtual ~DynInteger(void);
	
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	bool isUndef(void) const;
	
	private:
	
	bool const undef;
};

class DynArray : public DynType {
	
	public:
	
	unsigned int const size;
	
	DynArray(
		llvm::ArrayType         const& type,
		llvm::Value             const& creatingValue,
		std::unordered_set<DataSlot*>& slotSet);
	virtual ~DynArray(void);
	
	DynType& getElement(unsigned int const index) const;
	void     setElement(unsigned int const index, DynType& element);
	
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	private:
	
	DynType** _array;
};

class DynPointer : public DynType {
	
	public:
	
	DataSlot* const pPointedSlot;
	
	DynPointer(
			llvm::Value const& creatingValue,
			DataSlot*   const  pPointedSlot = nullptr,
			DataSlot*   const  pSlot        = nullptr) :
		DynType     (llvm::Type::PointerTyID, creatingValue, !pSlot, pSlot),
		pPointedSlot(pPointedSlot) {}
	
	virtual ~DynPointer(void) {}
	
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	bool     isNull           (void) const;
	DynType* tryGetSlotContent(void) const;
	DynType& getSlotContent   (void) const;
};
