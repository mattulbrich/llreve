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

class DynType;
class DynInteger;
class DynArray;
class DynPointer;

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
	
	// There is special function for every instruction type
	DynType* executeAllocaInst       (llvm::AllocaInst        const& inst);
	DynType* executeBinaryOperator   (llvm::BinaryOperator    const& inst);
	DynType* executeBranchInst       (llvm::BranchInst        const& inst);
	DynType* executeCallInst         (llvm::CallInst          const& inst);
	DynType* executeGetElementPtrInst(llvm::GetElementPtrInst const& inst);
	DynType* executeICmpInst         (llvm::ICmpInst          const& inst);
	DynType* executeLoadInst         (llvm::LoadInst          const& inst);
	DynType* executePHINode          (llvm::PHINode           const& inst);
	DynType* executeReturnInst       (llvm::ReturnInst        const& inst);
	DynType* executeStoreInst        (llvm::StoreInst         const& inst);
	
	private:
	
	bool const _computeBranchDep;
	
	static unsigned int getValueBitWidth(llvm::Value const& value);
	static bool         isArrayValue    (llvm::Value const& value);
	static bool         isIntValue      (llvm::Value const& value);
	static bool         isVoidValue     (llvm::Value const& value);
	static bool         isPointerValue  (llvm::Value const& value);
	
	llvm::BasicBlock::const_iterator _instIt;
	
	llvm::BasicBlock  const* _pLastBB; // Current BB is stored via '_pNextInst'
	llvm::Instruction const* _pRecentInst;
	llvm::Instruction const* _pNextInst;
	DynType           const* _pRetValue;
	
	std::unordered_map<llvm::Value const*, DynType const*>         _state;
	std::list<std::pair<llvm::Instruction const*, DynType const*>> _trace;
	std::unordered_map<llvm::Value const*, DynArray*>              _arrays;
	
	DynType&          cloneValue    (llvm::Value const& value);
	llvm::APInt       resolveInt    (llvm::Value const* pVal);
	DynPointer const& resolvePointer(llvm::Value const* pVal);
	
	void moveToNextInstruction(void);
};

class DynType {
	
	public:
	
	static DynType& voidValue;
	
	llvm::Type::TypeID const id;
	DynType*           const pParent;
	
	virtual ~DynType(void);
	
	DynArray   const& asArray  (void) const;
	DynInteger const& asInteger(void) const;
	DynPointer const& asPointer(void) const;
	
	DynArray&   asArray  (void);
	DynInteger& asInteger(void);
	DynPointer& asPointer(void);
	
	bool isSpecial(void) const;
	bool isArray  (void) const;
	bool isInteger(void) const;
	bool isPointer(void) const;
	bool isVoid   (void) const;
	
	virtual DynType* clone(DynType* const pParent = nullptr) const;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const;
	
	protected:
	
	DynType(llvm::Type::TypeID const id, DynType* const pParent) :
		id(id), pParent(pParent) {}
};

class DynInteger : public DynType {
	
	public:
	
	static DynInteger& undefValue;
	
	llvm::APInt const& value;
	
	DynInteger(llvm::APInt const& value, DynType* const pParent = nullptr) :
		DynType(llvm::Type::IntegerTyID, pParent),
		value  (*new llvm::APInt(value)) {}
	DynInteger(bool const value, DynType* const pParent = nullptr) :
		DynType(llvm::Type::IntegerTyID, pParent),
		value  (*new llvm::APInt(1, value ? 1 : 0)) {}
	virtual ~DynInteger(void);
	
	virtual DynType* clone(DynType* const pParent = nullptr) const override;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	bool isUndef(void) const;
};

class DynArray : public DynType {
	
	public:
	
	unsigned int const size;
	
	DynArray(llvm::ArrayType const& type, DynType* const pParent = nullptr);
	virtual ~DynArray(void);
	
	DynType& getElement(unsigned int const index) const;
	void     setElement(unsigned int const index,  DynType& element);
	void     setElement(DynType const& oldElement, DynType& newElement);
	
	virtual DynType* clone(DynType* const pParent = nullptr) const override;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	private:
	
	DynType**                                        _array;
	std::unordered_map<DynType const*, unsigned int> _elementToIndexMap;
};

class DynPointer : public DynType {
	
	public:
	
	static DynPointer& nullPtr;
	
	DynType& element;
	
	DynPointer(
			DynType&       element,
			DynType* const pParent = nullptr) :
		DynType(llvm::Type::PointerTyID, pParent), element(element) {}
	virtual ~DynPointer(void) {}
	
	virtual DynType* clone(DynType* const pParent = nullptr) const override;
	virtual llvm::raw_ostream& print(llvm::raw_ostream& out) const override;
	
	bool isNull(void) const;
};
