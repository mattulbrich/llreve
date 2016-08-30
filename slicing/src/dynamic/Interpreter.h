#pragma once

#include "Heap.h"

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
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class TraceEntry;
class DynType;
class DynInteger;
class DynPointer;

class Interpreter {
	
	public:
	
	typedef std::vector<int64_t> InputType;
	
	llvm::Function const& func;
	
	std::unordered_set<llvm::Instruction const*> recentDataDependencies;
	
	Interpreter(
		llvm::Function     const& func,
		InputType          const& input,
		Heap&                     heap,
		bool               const  branchDependencies = true,
		llvm::raw_ostream* const  pOut               = nullptr);
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
	
	Heap&                            _heap;
	Heap::OwnerType const            _ownerId;
	bool            const            _tracePrinting;
	std::string     const            _printPrefix;
	llvm::raw_ostream&               _out;
	llvm::BasicBlock::const_iterator _instIt;
	
	llvm::BasicBlock  const* _pLastBB; // Current BB is stored via '_pNextInst'
	llvm::Instruction const* _pRecentInst;
	llvm::Instruction const* _pNextInst;
	DynType           const* _pRetValue;
	
	std::unordered_map<llvm::Value const*, DynType const*> _state;
	std::list<TraceEntry const*>                           _trace;
	
	Interpreter(
		llvm::Function     const& func,
		InputType          const& input,
		Heap&                     heap,
		bool               const  branchDependencies,
		llvm::raw_ostream* const  pOut,
		std::string        const  printPrefix);
	
	DynType const&    cloneValue    (llvm::Value const& value);
	llvm::APInt       resolveInt    (llvm::Value const& value);
	Heap::AddressType resolvePointer(llvm::Value const& value);
	
	bool tryResolveInt    (llvm::Value const& value, llvm::APInt&       result);
	bool tryResolvePointer(llvm::Value const& value, Heap::AddressType& result);
	
	void moveToNextInstruction(void);
	void addDependency(llvm::Value const& dependency);
	
	Heap::AddressType computeByteSize            (llvm::Type const& type);
	Heap::AddressType computeArrayElementByteSize(llvm::Type const& type);
	
	TraceEntry const& updateState(
		llvm::Instruction const&       inst,
		DynType           const* const pValue = nullptr);
	TraceEntry const& updateState(
		llvm::Instruction const& inst,
		Heap::AddressType const  address,
		Heap::AddressType const  length);
	
	// There is special function for every instruction type
	TraceEntry const& executeAllocaInst       (llvm::AllocaInst        const& inst);
	TraceEntry const& executeBinaryOperator   (llvm::BinaryOperator    const& inst);
	TraceEntry const& executeBranchInst       (llvm::BranchInst        const& inst);
	TraceEntry const& executeCallInst         (llvm::CallInst          const& inst);
	TraceEntry const& executeCastInst         (llvm::CastInst          const& inst);
	TraceEntry const& executeGetElementPtrInst(llvm::GetElementPtrInst const& inst);
	TraceEntry const& executeICmpInst         (llvm::ICmpInst          const& inst);
	TraceEntry const& executeLoadInst         (llvm::LoadInst          const& inst);
	TraceEntry const& executePHINode          (llvm::PHINode           const& inst);
	TraceEntry const& executeReturnInst       (llvm::ReturnInst        const& inst);
	TraceEntry const& executeStoreInst        (llvm::StoreInst         const& inst);
};

class TraceEntry {
	
	public:
	
	llvm::Instruction const&       inst;
	DynType           const* const pValue;
	
	std::map<Heap::AddressType, Heap::ElementType> heapValues;
	
	TraceEntry(
		llvm::Instruction const& inst,
		DynType const*    const  pValue,
		Heap              const& heap,
		Heap::AddressType const  address = 0,
		Heap::AddressType const  length  = 0);
	
	~TraceEntry(void);
};

class DynType {
	
	public:
	
	llvm::Type::TypeID const id;
	
	virtual ~DynType(void);
	
	DynInteger const& asInteger(void) const;
	DynPointer const& asPointer(void) const;
	
	DynInteger& asInteger(void);
	DynPointer& asPointer(void);
	
	bool isInteger(void) const;
	bool isPointer(void) const;
	bool isVoid   (void) const;
	
	virtual DynType&           clone(void)                   const = 0;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const = 0;
	
	protected:
	
	DynType(llvm::Type::TypeID const id) : id(id) {}
};

class DynInteger : public DynType {
	
	public:
	
	llvm::APInt const value;
	
	DynInteger(void) :
		DynType(llvm::Type::IntegerTyID), value() {}
	
	DynInteger(llvm::APInt const& value) :
		DynType(llvm::Type::IntegerTyID), value(value) {}
	
	DynInteger(bool const value) :
		DynType(llvm::Type::IntegerTyID), value(1, value ? 1 : 0) {}
	
	virtual ~DynInteger(void) {}
	
	virtual DynType&           clone(void)                   const override;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
};

class DynPointer : public DynType {
	
	public:
	
	Heap::AddressType const heapLocation;
	
	DynPointer(
			Heap::AddressType const heapLocation) :
		DynType     (llvm::Type::PointerTyID),
		heapLocation(heapLocation) {}
	
	virtual ~DynPointer(void) {}
	
	virtual DynType&           clone(void)                   const override;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	bool isNull(void) const;
};
