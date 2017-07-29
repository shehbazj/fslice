//#define DEBUG_TYPE "FSlice"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#include <iostream>
#include <sstream>
#include <algorithm>
#include <map>
#include <vector>
#include <list>
#include <string>
#include <stack>
#include <queue>
#include "sym.h"
//#include "taintProcessor.cpp"

#include <boost/algorithm/string/classification.hpp> // Include boost::for is_any_of
#include <boost/algorithm/string/split.hpp> // Include for boost::split

//#define DEBUG

using namespace llvm;

#ifdef DEBUG
#  define D(x) x
#else
#  define D(x)
#endif

#ifdef DEBUG_ENUMERATE
#  define DE(x) x
#else
#  define DE(x)
#endif

#ifdef DEBUG_TAINT
#  define DT(x) x
#else
#  define DT(x)
#endif

struct loopType {
	
};

enum operandType {
	CONSTANT,
	INPUT_DEPENDENT,
	UNKNOWN,
};

// Introduces generic dynamic program slic recording into code.
class loopSymx : public ModulePass {
	public:
		loopSymx(void);
		virtual bool runOnModule(Module &M) override;
		static char ID;

		std::map<const char *,Value *> StrValues;
		std::map<BasicBlock *, BasicBlock *> loopBackBBs;

		// map of loop entry block and list of basic blocks containing loopback path
		// from entry to loop block
		std::map<BasicBlock *, std::list<BasicBlock *> *> loopEntryBlock_loopPath_map;
		std::list< std::list <BasicBlock *> *> loopLessPathList;
		std::map<BasicBlock *, std::map<Value *, enum operandType > *> basicBlock_operandType_map;

	private:
		void printBBStack(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB);
		void storeLoopEntryBlockAndLoopPath(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB);
		bool hasLoop(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack);
		void getLooplessPaths(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack);
		void taintVariables(void);
		bool getLoopType(void);			
		void extractIteratorOperation(void);
		void analyseBranches(void);
		void markInput(Value *V, BasicBlock *BB);
		void addLoopPath(std::stack <BasicBlock *>);
	
		void runOnLoad(LoadInst *LI);
		void runOnStore(StoreInst *SI);
		void runOnBranch(BranchInst *BI);
		bool runOnCall(CallInst *CI);
		void runOnReturn(ReturnInst *RI);
		void runOnUnary(UnaryInstruction *I);
		void runOnCast(CastInst *I);
		void runOnBinary(BinaryOperator *I);
		void runOnICmp(ICmpInst *I);
		void runOnAlloca(AllocaInst *I);
		void runOnGetElementPtr(GetElementPtrInst *I);
		void displayLoopPathMap();
		void displayLoopLessPathList();
		void displayBBTaintMap();
		void displayStack(std::stack <BasicBlock *> *bbStack);
		void addLoopPath(std::stack <BasicBlock *> *bbStack);

		enum operandType getOperandType(Value *V, BasicBlock *BB);
		void setOperandType(Value *V, BasicBlock *BB , enum operandType opType);

		template <typename T>
			bool isLoopBack(T *currentBB, std::stack <T *> *bbStack);
		template <typename T>
			bool isLoopBack(T *currentBB, std::stack <T *> *bbStack, T *loopBackBB);

		// Creates a function returning void on some arbitrary number of argument
		// types.
		template <typename... ParamTypes>
			Function *CreateFunc(Type *RetTy, std::string name, std::string suffix,
					ParamTypes... Params) {
				std::vector<Type *> FuncParamTypes = {Params...};
				auto FuncType = llvm::FunctionType::get(RetTy, FuncParamTypes, false);
				return dyn_cast<Function>(M->getOrInsertFunction(name + suffix, FuncType));
			}


		Value *CreateString(const char *str) {
			auto &Val = StrValues[str];
			if (Val) return Val;

			auto GStr = new GlobalVariable(
					*M,
					ArrayType::get(IntegerType::get(*C, 8), strlen(str) + 1),
					true,
					GlobalValue::PrivateLinkage,
					ConstantDataArray::getString(*C, str, true));

			auto Zero = ConstantInt::get(IntPtrTy, 0, false);
			std::vector<Value *> Indices = {Zero, Zero};
			Val = ConstantExpr::getGetElementPtr(GStr, Indices);
			return Val;
		}

		Function *F;
		Module *M;
		LLVMContext *C;

		Type *IntPtrTy;
};

loopSymx::loopSymx(void): ModulePass(ID){}

/* for each instruction, mark the resultant operator based on operands.
 * maintain the type of each operand for each basic block separately.
 * type of operators - CONSTANT, INPUT_DEPENDENT, UNKNOWN.
 *
 * An operand type is constant if it is assigned a constant value or
 * a result of operations on constant values.
 *
 * An operand type is input dependent if they are assigned an input value
 * or a result of operations on input values. If operand is treated as
 * constant in one path and input dependent in another path, we mark the
 * operand as constant. 
 *
 * Finally, there are operands or input results that are dependent on
 * environment variables. these are classified as UNKNOWN operators. 
 * unknown operators > input dependent values > constant values.
 * */

enum operandType loopSymx:: getOperandType(Value *V, BasicBlock *BB)
{
	/*
	if(basicBlock_operandType_map.find(BB) != basicBlock_operandType_map.end()){
		basicBlock_operandType_map[BB] = new std::map<Value *, enum operandType >;	
	} 
	*/
	if( basicBlock_operandType_map[BB] == nullptr){
		basicBlock_operandType_map[BB] = new std::map<Value *, enum operandType >;
	} 
	if(basicBlock_operandType_map[BB]->find(V)  == basicBlock_operandType_map[BB]->end()){
		enum operandType opType = UNKNOWN; 
		if(dyn_cast<ConstantInt>(V)){
			opType = CONSTANT;
		}
		basicBlock_operandType_map[BB]->insert(std::pair<Value *, enum operandType > (V, opType));
		std::cerr << __func__ << "(): " << opType << std::endl;
		return opType;
	} else {
		std::cerr << __func__ << "(): " << basicBlock_operandType_map[BB]->find(V)->second << std::endl;
		return basicBlock_operandType_map[BB]->find(V)->second;
	}
}

void loopSymx:: setOperandType(Value *V, BasicBlock *BB , enum operandType opType)
{
	if(basicBlock_operandType_map[BB] == nullptr){
		basicBlock_operandType_map[BB] = new std::map<Value *, enum operandType >;		
	}
	if(basicBlock_operandType_map[BB]->find(V) == basicBlock_operandType_map[BB]->end()){
		basicBlock_operandType_map[BB]->insert (std::pair <Value *, enum operandType>(V, opType));
	}else{
		auto op = basicBlock_operandType_map[BB]->find(V)->second;
		if(opType > op){
			basicBlock_operandType_map[BB]->insert (std::pair <Value *, enum operandType>(V, opType));
		}
	}
}

void loopSymx:: markInput(Value *V, BasicBlock *BB)
{
	if(basicBlock_operandType_map[BB] == nullptr){
		basicBlock_operandType_map[BB] = new std::map<Value *, enum operandType >;		
	}
	//std::cerr << "MARKED INPUT ARGUMENT AS INPUT_DEPENDENT " << BB->getName().data() << V->getName().data() << std::endl;
		// || basicBlock_operandType_map[BB]->find(V)->second != UNKNOWN) { 
	basicBlock_operandType_map[BB]->insert (std::pair <Value *, enum operandType>(V, INPUT_DEPENDENT));
}

void loopSymx:: runOnLoad(LoadInst *LI)
{
	std::cerr << LI->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
	auto P = LI->getPointerOperand();
	enum operandType opType = getOperandType(P, LI->getParent());
	
	setOperandType(LI, LI->getParent() , opType);
}

void loopSymx:: runOnStore(StoreInst *SI)
{				
	auto V = SI->getValueOperand();
	auto P = SI->getPointerOperand();
	
	std::cerr << SI->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
//	std::cerr << __func__ << "():" << std::endl;
	enum operandType opType = getOperandType(V, SI->getParent());
//	std::cerr << " operand Type of " << V->getName().data() << " = " << opType << std::endl;
	setOperandType(P, SI->getParent() , opType);
}

bool loopSymx:: runOnCall(CallInst *CI)
{
	return false;	
}

void loopSymx:: runOnBranch(BranchInst *BI)
{
	std::cerr << BI->getParent()->getName().data() << " " << __func__ << "()" << std::endl;
	if(BI->isConditional()){ 
                auto cond = BI->getCondition();
		enum operandType opType = getOperandType(cond, BI->getParent());
		switch (opType){
			case 0:
				std::cerr << "BRANCH IS FIL " << std::endl;
				break;
			case 1:
				std::cerr << "BRANCH IS IDL " << std::endl;
				break;
			case 2:
				std::cerr << "BRANCH IS UNKNOWN " << std::endl;
				break;
		};
	}
}

void loopSymx:: runOnReturn(ReturnInst *RI)
{

}

void loopSymx:: runOnUnary(UnaryInstruction *I)
{

}

void loopSymx:: runOnCast(CastInst *I)
{
	std::cerr << I->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
	auto operand = I->getOperand(0);
	enum operandType opType = getOperandType(operand, I->getParent());
	setOperandType(I, I->getParent() , opType);
}

void loopSymx:: runOnBinary(BinaryOperator *I)
{

}

// if value being compared to is a constant, the first value also becomes
// a constant.

void loopSymx:: runOnICmp(ICmpInst *I)
{
 	auto op1 = I->getOperand(0);
        auto op2 = I->getOperand(1);
	
	std::cerr << I->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
	enum operandType op1Type = getOperandType(op1, I->getParent());
	enum operandType op2Type = getOperandType(op2, I->getParent());
	if(op1Type == UNKNOWN && op2Type == CONSTANT){
		std::cerr << __func__ << "():Setting Value " << op1-> getName().data() << " as  CONSTANT " << std::endl;
		setOperandType(op1, I->getParent() , op2Type);
		setOperandType(I, I->getParent(), op2Type);
	}else if(op1Type == INPUT_DEPENDENT){
		setOperandType(I, I->getParent(), INPUT_DEPENDENT);
	}else {
		std::cerr << "NO BRANCH TYPE AVAILABLE FOR " << op1Type << " CMP " << op2Type << std::endl;
		assert(0);
	}
}

void loopSymx:: runOnAlloca(AllocaInst *I)
{
//	for (auto &A : F->args()){
//		if(A == I->get()){
//			setOperandType(I , I->getParent() , INPUT_DEPENDENT);
//		}
//	}
}

/* mark resultant array index computed as INPUT_DEPENDENT if either the
 * array or the index used is dependent on the INPUT_DEPENDENT
 * */

void loopSymx:: runOnGetElementPtr(GetElementPtrInst *I)
{
	auto ptrOperand = I->getPointerOperand();
	enum operandType opType = getOperandType(ptrOperand, I->getParent());
	std::cerr << I->getParent()->getName().data() << __func__ << "():" << std::endl;
	for(auto op = I->idx_begin(); op!= I->idx_end() ; op++){
		opType = (getOperandType( op ->get(), I->getParent())  == INPUT_DEPENDENT) ? 
				INPUT_DEPENDENT : opType;
	}
	setOperandType(I, I->getParent(), opType);
}

/* enumerate different paths by their basic blocks. Mark the function paramters 
 * as input variables. for each basic block, mark the variables as input 
 * dependent or constant. 
 * */

void loopSymx:: taintVariables(void)
{
	// mark input argument values
	// mark constant values
	// mark unknown values
	
	for (auto &A : F->args()){
		markInput( &A, &(F->getEntryBlock()));
 	}

	// iterate through each path in loopLessPathList

	for(auto &path : loopLessPathList){
		std::cerr << "=== LOOP ===" << std::endl;
		for(auto &BB : *path){ // get each basic block in each path
			std::cerr << "PROCESSING BB " << BB->getName().data() << std::endl;
			for (auto &I : *BB){
				if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
                	        	runOnLoad(LI);
                		} else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
	                	        runOnStore(SI);
        	        	} else if (BranchInst *BI = dyn_cast<BranchInst>(&I)) {
        	        	        runOnBranch(BI);
        	        	} else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
        	        	        runOnCall(CI);
				} else if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
        	        	        runOnReturn(RI);
        	        	} else if (CastInst *CI = dyn_cast<CastInst>(&I)) {
        	        	        runOnCast(CI);
        	        	} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(&I)) {
        	        	        runOnBinary(BI);
        	        	} else if (ICmpInst *IC = dyn_cast<ICmpInst>(&I)) {
        	        	        runOnICmp(IC);
        	        	} else if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
					runOnAlloca(AI);
        	        	} else if (GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(&I)) {
        	        	        runOnGetElementPtr(GI);
        	        	}else{  
        	        	        std::cerr << __func__ << "(): Could not match instruction " << std::endl;
        	        	        assert(0);
        	        	}
			}
		}
		displayBBTaintMap();
	}
}

// check loop block. classify as IDL or FIL
// loop block has a branch condition. check if 
// branch condition operators are constant operators 
// or input dependent

bool loopSymx:: getLoopType(void){
	for(auto &it : loopEntryBlock_loopPath_map){
		BasicBlock *loopBackBlock = it.first;
		// go through each instruction.
		// get cmp instruction. get operands
		// check if operand is a constant
		
		for(auto &inst : *loopBackBlock){
			if (ICmpInst *I = dyn_cast<ICmpInst>(&inst)) {
				auto op1 = I->getOperand(0);
				if (dyn_cast<ConstantInt>(op1)){
					return true;	
				}
				auto op2 = I->getOperand(1);
				if (dyn_cast<ConstantInt>(op2)){
					return true;
				}
			}
		}
	}
	return false;
}

void loopSymx:: extractIteratorOperation(void){

}

void loopSymx:: analyseBranches(void){

}

void loopSymx:: displayStack(std::stack <BasicBlock *> *bbStack)
{
	std::stack <BasicBlock *> *tmpStack = new std::stack <BasicBlock *>;
	while(!bbStack->empty()){
		std::cerr << bbStack->top()->getName().data() << " --> ";
		tmpStack->push(bbStack->top());
		bbStack->pop();
	}
	std::cerr << std::endl;
	while(!tmpStack->empty()){
		bbStack->push(tmpStack->top());
		tmpStack->pop();
	}
}

void loopSymx:: addLoopPath(std::stack <BasicBlock *> *bbStack)
{
	//std::stack <BasicBlock *> *tmpStack = new std::stack <BasicBlock *>;
	//loopLessPathList.insert(new std::list <BasicBlock *>);
	std::stack <BasicBlock *> *tmpStack = new std::stack <BasicBlock *>;
	std::list <BasicBlock *> *newList = new std::list <BasicBlock *>;

	while(!bbStack->empty()){
		tmpStack->push(bbStack->top());
		std::list <BasicBlock *>::iterator it = newList->begin();
		newList->insert(it,bbStack->top());
		//std::cerr << "stack top = " << bbStack->top()->getName().data() << std::endl;
		bbStack->pop();
	}
	while(!tmpStack->empty()){
		bbStack->push(tmpStack->top());
		tmpStack->pop();
	}
	std::list< std::list <BasicBlock *> *>::iterator it = loopLessPathList.end();
	it--;
	loopLessPathList.insert(it,newList);
}

void loopSymx:: displayLoopPathMap()
{
	for(auto &it : loopEntryBlock_loopPath_map){
		std::cerr << it.first->getName().data() << std::endl;
		if(it.second == nullptr){
			std::cerr << "NULLPTR Detected "<< std::endl;
		}else{
			for(auto it2 : *(it.second)){
				std::cerr << it2->getName().data() << " ";
			}
			std::cerr<< std::endl;
		}
	}
}

void loopSymx:: displayBBTaintMap()
{
	for(auto &it : basicBlock_operandType_map){
		//std::cerr << "BasicBlock = " << it.first->getName().data() << std::endl;
		for(auto &it2 : *(it.second)){
			std::cerr << it2.first->getName().data() << " -- " << it2.second << std::endl;
		}
	}
}

void loopSymx:: displayLoopLessPathList()
{
	for(auto &it : loopLessPathList){
		for(auto &it2 : *(it)){
			std::cerr << it2->getName().data() << " --> ";
		}
		std::cerr << " --> " << std::endl;
	}
}

template <typename T>
bool loopSymx :: isLoopBack(T *currentBB, std::stack <T *> *bbStack){
	std::stack <T *> temp;
	bool bbIsLoopBack = false;
	if(bbStack->empty()){
		return false;
	}
	// removing top element since its currentBB
	else{
		if(bbStack == NULL){
			D(std::cerr << "Stack is null " << std::endl;)
			return false;
		}
		if(bbStack -> top() == NULL){
			D(std::cerr << "Stack top is null " << std::endl;)
			return false;
		}
		auto elem = bbStack->top();
		temp.push(elem);
		bbStack->pop();
		// checking if current BB is already in the stack
		while(!bbStack->empty()){
			auto top = bbStack->top();
			if(top == currentBB){
				bbIsLoopBack = true;
				D(std::cerr << "Loop Back Found at block " << currentBB << std::endl;)
			}
			temp.push(top);
			bbStack->pop();	
		}
		while(!temp.empty()){
			auto top = temp.top();
			bbStack->push(top);
			temp.pop();
		}
	}
	return bbIsLoopBack;
}

template <typename T>
bool loopSymx :: isLoopBack(T *currentBB, std::stack <T *> *bbStack, T *loopBackBB)
{
	std::stack <T *> temp;
	bool bbIsLoopBack = false;
	if(bbStack->empty()){
		return false;
	}
	// removing top element since its currentBB
	else{
		if(bbStack == NULL){
			D(std::cerr << "Stack is null " << std::endl;)
			return false;
		}
		if(bbStack -> top() == NULL){
			D(std::cerr << "Stack top is null " << std::endl;)
			return false;
		}
		auto elem = bbStack->top();
		temp.push(elem);
		bbStack->pop();
		// checking if current BB is already in the stack
		while(!bbStack->empty() && bbStack->top() != loopBackBB){
			auto top = bbStack->top();
			if(top == currentBB){
				bbIsLoopBack = true;
				D(std::cerr << "Loop Back Found at block " << currentBB << std::endl;)
			}
			temp.push(top);
			bbStack->pop();	
		}
		while(!temp.empty()){
			auto top = temp.top();
			bbStack->push(top);
			temp.pop();
		}
	}
	return bbIsLoopBack;
}

void loopSymx:: storeLoopEntryBlockAndLoopPath(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB)
{
	std::stack <BasicBlock *> tmpStack;
	std::list <BasicBlock *> *tmpList = new std::list<BasicBlock *>;
	while(!bbStack->empty()){
		auto bb = bbStack -> top();
		tmpStack.push(bb);
		bbStack->pop();
	}
	while(!tmpStack.empty()){
		auto bb = tmpStack.top();
		//std::cerr << bb->getName().data() << " -> " ;
		tmpList->push_back(bb);
		tmpStack.pop();
		bbStack->push(bb);
	}
	tmpList->push_back(currentBB);
	loopEntryBlock_loopPath_map[currentBB] = tmpList;	
	//std::cerr << currentBB ->getName().data() << std::endl;
}

void loopSymx:: printBBStack(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB)
{
	std::stack <BasicBlock *> tmpStack;
	while(!bbStack->empty()){
		auto bb = bbStack -> top();
		tmpStack.push(bb);
		bbStack->pop();
	}
	while(!tmpStack.empty()){
		auto bb = tmpStack.top();
		std::cerr << bb->getName().data() << " -> " ;
		tmpStack.pop();
		bbStack->push(bb);
	}
	std::cerr << currentBB ->getName().data() << std::endl;
}

/* stores all paths inside the function without any loops being repeated more than once into 
 * loopLessPathList 
 * */

void loopSymx::getLooplessPaths(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack)
{
	int numSuccessors = currentBB->getTerminator()->getNumSuccessors();
	if(numSuccessors == 0){
		// end of loop, enumerate path
		bbStack->push(currentBB);
		addLoopPath(bbStack);
		//displayStack(bbStack);	
		bbStack->pop();
		return;
	}
	if(!isLoopBack(currentBB, bbStack)){
		// not loopBack, go to successor block
		bbStack->push(currentBB);
		for(auto succ = 0 ;  succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			getLooplessPaths(BB, bbStack);
		}
		bbStack->pop();
	}else{
		std::cerr << "detected " << currentBB->getName().data() << " as loopback BB" << std::endl;
		// check which successor block is the loopback block
		for(auto succ =0 ; succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			if(!isLoopBack(BB, bbStack, currentBB)){
			// check for an alternative path with respect to current
			// loopback block.
				bbStack->push(currentBB);
				getLooplessPaths(BB, bbStack);
				bbStack->pop();
				return;
			}
		}
	}
}

// returns true even if 1 loop exists

bool loopSymx::hasLoop(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack)
{
	int numSuccessors = currentBB->getTerminator()->getNumSuccessors();
	bool loopExists = false;
	if(!isLoopBack(currentBB, bbStack)){
		bbStack->push(currentBB);
		for(auto succ = 0 ;  succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			loopExists =  hasLoop(BB, bbStack)? true : loopExists;
		}
		bbStack->pop();
	}else{
		std::cerr << "detected " << currentBB->getName().data() << " as loopback BB" << std::endl;
		// check which successor block is the loopback block
		for(auto succ =0 ; succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			if(isLoopBack(BB, bbStack)){
				loopBackBBs[currentBB] = BB;
				storeLoopEntryBlockAndLoopPath(bbStack, currentBB);
				printBBStack(bbStack, currentBB);
				loopExists = true;
			}
		}
	}
	return loopExists;
}

bool loopSymx::runOnModule(Module &M_) {
	M = &M_;
	for(auto &F_ : M->functions()){
		F = &F_;
		std::stack <BasicBlock *> *bbStack = new std::stack <BasicBlock *>;
		if(!F->isDeclaration()){
			//std::cerr << __func__ << "():FUNCTION():" << F->getName().data() << std::endl;
			getLooplessPaths(&F->getEntryBlock(), bbStack);
			displayLoopLessPathList();
			taintVariables();

		//	if(hasLoop(&(F->getEntryBlock()), bbStack)){
				// data flow pass to mark input dependent, constant, and unknown variable types.
				/*
					// std::cerr << F->getName().data() << " has a loop " << std::endl;
					// check loop condition. classify as IDL or FIL
					getLoopType();			
					// XXX flag loops that have iterator operations in BBs other than loop entry block.
					// get iterator operation within the loop structure.
					// predecessor of the loop block inside the loop will have this value.
					extractIteratorOperation();
					// mark different branches as - input dependent (data flow dependency)
					// concrete
					// control flow dependent
					analyseBranches();
				*/
			
				//displayLoopPathMap();
				//displayBBTaintMap();
		//	}else{
		//		std::cerr << "For function " << F->getName().data() << " loop not detected " << std::endl;
		//	}
		}else{
			if(F->hasName()){
				std::cerr << "Function " << F->getName().data() << " is declaration " << std::endl;
			}
		}	
	}
        return true;
}

char loopSymx::ID = '\0';

static RegisterPass<loopSymx> X(
    "loopSymx",
    "loopSymx",
    false,  // Only looks at CFG.
    false);  // Analysis Pass.
