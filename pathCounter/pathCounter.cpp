#define DEBUG_TYPE "FSlice"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <iostream>
#include <map>
#include <vector>
#include <list>
#include <string>
#include <stack>
//#include "taintProcessor.cpp"


//#define DEBUG

using namespace llvm;

#ifdef DEBUG
#  define D(x) x
#else
#  define D(x)
#endif

// Set of llvm values that represent a logical variable.
struct VSet {
  VSet *rep;
  int index;
};

// Information about an instruction.
struct IInfo {
  BasicBlock *B;
  Instruction *I;
};

// Introduces generic dynamic program slic recording into code.
class pathCounter : public ModulePass {
 public:
  pathCounter(void);

  virtual bool runOnModule(Module &M) override;

  static char ID;
  static unsigned int taintVal;

 private:
  void collectInstructions(void);
  void initVSets(void);
  void combineVSets(void);
  static void combineVSet(VSet *VSet1, VSet *VSet2);
  static VSet *getVSet(VSet *VSet);
  void labelVSets(void);
  void allocaVSetArray(void);

  void runOnFunction();
  void runOnFunctionEnd();
  void runOnArgs(void);
  void printFunctionName(const char *s);
  void pushToCallStack(const char *s);
  void printCallTrace();
  void printString(Instruction *I, const char *s);

  void runOnLoad(BasicBlock *B, LoadInst *LI);
  void runOnStore(BasicBlock *B, StoreInst *SI);
  void runOnCall(BasicBlock *B, CallInst *CI);
  void runOnReturn(BasicBlock *B, ReturnInst *RI);
  void runOnUnary(BasicBlock *B, UnaryInstruction *I);
  void runOnBinary(BasicBlock *B, BinaryOperator *I);
	void runOnICmp(BasicBlock *B, ICmpInst *I);
  void traceFunctionCallGraph();
  void generateConvergenceFactor();
  void getFunctionBFWithoutCalls();
  void getModuleLevelBF();
	std::map <uint64_t, uint64_t> taintMap;
	bool markedProcessed();
	bool processedFunctionCaller();
	void analyseFunctionCalls();
  void runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI);
  int getFunctionBF(std::stack <const char*> *FStack);
	void generateTaintInfo();
	void processBlock(BasicBlock *BB);
	std::vector<const char *> processedBlocks;
  int getBFOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack);
	void processDFS(BasicBlock *B, std::stack <const char *> *BBStack);
	void processBasicBlock(BasicBlock *BB);
	//void generateTestCases();
  //BasicBlock *getBB(const char *name);
	int getCF(BasicBlock *BB);
	int getBasicBlockBF(BasicBlock *BB, std::stack <const char *> *bbStack, std::stack <const char *> *FStack);

	void displayCFMap();
	void displayBFMap();
	void displayFunctionBFMap();
	void printStack(std::stack <const char *> *bbStack);
	int  getConvergence(BasicBlock *BB);
	int  getMaxConvergence(TerminatorInst *I);

	void runOnBB(BasicBlock *BB);
	void trackLoad(Value *I);
	void displayMap();
	void generatePaths(std::stack <const char *> *);
	template <typename T>
	bool isLoopBack(T *currentBB, std::stack <T *> *bbStack);
	bool isLoopBackBB(const char *currentBB);
	bool inStack(const char *element, std::stack<const char *> *bbStack);
	const char * getAlternatePath(const char *currentBB, std::stack <const char *> *bbStack);
	BasicBlock * getAlternatePath(BasicBlock *ForLoopBlock, std::stack <const char *> *bbStack);
	bool isTerminalFunction();
	void getTerminalFunctions();

	void printFunCallFromBB(const char *bbName);
  void track(Value *V);
  int marked(Value *V);

  Value *getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	std::map<BasicBlock *, int> *CFMap = new std::map <BasicBlock *, int>;
	std::map<BasicBlock *, int> *BFMap = new std::map <BasicBlock *, int>;
	std::map<const char *, int> functionBFMap;
  std::vector <Value *> trackTaint;
	// map of functions and pointer to map of (BB,ConvergenceFactor)
	// for each BB in that function.
	std::map <const char *, void *> functionConvergenceFactorMap;

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
  const DataLayout *DL;

  Type *IntPtrTy;
  Type *VoidTy;
  Type *VoidPtrTy;
  Instruction *AfterAlloca;// first instruction in a function.
			   // this instruction is always entry

  std::map<Argument *, VSet *> ArgToVSet;
  std::vector<IInfo> IIs;
  std::vector<VSet> VSets;
  std::map<Value *,VSet *> VtoVSet;
  std::vector<Value *> IdxToVar;
  std::map<const char *,Value *> StrValues;
  std::map<const char *, std::list <const char *> >  BBSuccessorMap;
  std::list<const char *> processedFunctionNames;
  int numVSets;
};

pathCounter::pathCounter(void)
    : ModulePass(ID),
      F(nullptr),
      M(nullptr),
      C(nullptr),
      DL(nullptr),
      IntPtrTy(nullptr),
      VoidTy(nullptr),
      VoidPtrTy(nullptr),
      AfterAlloca(nullptr),
      numVSets(0) {}

void pathCounter :: displayMap()
{
	for(auto bbIt = BBSuccessorMap.begin() ; bbIt != BBSuccessorMap.end() ; bbIt++){
		std::cerr << bbIt->first << " -> ";
		for(auto listIter = bbIt->second.begin() ; listIter !=bbIt->second.end() ; listIter++){
			std::cerr << *listIter << " ," ;
		}
		std::cerr << std::endl;
	}	
}

void pathCounter :: printFunCallFromBB(const char *bbName)
{
	bool bracketPrinted = false;
	for(auto &BB : *F){
		if(!strcmp(BB.getName().data(),bbName)){
			for(auto &I : BB){
				if(CallInst *CI = dyn_cast<CallInst>(&I)) {
					if(!bracketPrinted){
						std::cerr << "(";
						bracketPrinted = true;
					} 
					std::cerr << CI->getCalledFunction()->getName().data() << " " ;
					// self recursion
					if(!strcmp(CI->getCalledFunction()->getName().data(),bbName)){
						std::cerr << "*" ;
					}
				}
			}
			if(bracketPrinted){
				std::cerr << ")";
			}
			return;	
		}
	}
}

void pathCounter ::printStack(std::stack <const char *> *bbS)
{
//	std::cerr << F->getName().data() << "():"; 
	std::stack <const char *> temp;
	if(bbS->empty()){
		std::cerr << "STACK IS ALREADY EMPTY" << std::endl;
		return;
	}
	while(!bbS->empty()){
		const char * name = bbS->top();
		temp.push(name);
		bbS->pop();
	}
	while(!temp.empty()){
		auto bbName = temp.top();
		temp.pop();
		std::cerr << bbName << "  ->  ";
		printFunCallFromBB(bbName);
		bbS->push(bbName);
	}
	std::cerr << std::endl;
} 

int pathCounter :: getCF(BasicBlock *BB)
{
	int ret = -1;
	for (auto it = CFMap->begin() ; it != CFMap->end() ; it++)
	{
		if(!strcmp(it->first->getName().data() , BB->getName().data())){
			return it->second;
		}
	}
	return ret;
}

int pathCounter :: getMaxConvergence(TerminatorInst *I)
{
	int max = 0;
	for( unsigned i = 0 ; i < I->getNumSuccessors() ; i++)
	{
		// need a check for successors being part of a loop construct, in which case
		// we loop once and look for alternate path

		int conv = getCF(I->getSuccessor(i)); 
		if(conv == -1){					// BB's CF not calculated already
			conv = getConvergence(I->getSuccessor(i)); // then calculate convergence
			CFMap->insert (std::pair<BasicBlock *, int >  (I->getSuccessor(i),conv));
		}
		if (conv > max){
			max = conv;
		}		
	}
	return max;
}

int pathCounter :: getConvergence(BasicBlock *BB)
{
	int numPred=0;
	for (pred_iterator it = pred_begin(BB) ; it != pred_end(BB) ; it++){
		numPred++;
	}
	if (numPred  > 1){ 	// termination of a branch instruction two paths meet here
		return 1 + getMaxConvergence(BB->getTerminator());
	}else {			// entry Basic Block or sequential block
		return getMaxConvergence(BB->getTerminator());
	}
}

int pathCounter :: getBFOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack)
{
	int functionBF = 1;
	if(FStack == NULL)
		return functionBF;
	for (auto &I : *BB){
		if( CallInst *CI = dyn_cast<CallInst > (&I)) {
			if(CI->getCalledFunction() == NULL){
				std::cerr << "called function is null " << std::endl;
				printStack(FStack);
				continue;
			}
			if(!CI->getCalledFunction()->hasName()){
				printStack(FStack);
				std::cerr << "found basic Block " << BB->getName().data() << " with a call instruction with no name " << std::endl;
				continue;	
			}
			auto calledFunction = CI->getCalledFunction()->getName().data();
			D(std::cerr << __func__ << "(): BB " << BB->getName().data() << " calls " << calledFunction << std::endl;)
			if(M->getFunction(calledFunction)->isDeclaration()){
				continue;
			}
    			FStack->push(calledFunction);
			functionBF *= getFunctionBF(FStack);
			FStack->pop();
		}
	}
	return functionBF;
}

int pathCounter :: getBasicBlockBF(BasicBlock *BB, std::stack <const char *> *bbStack, std::stack <const char *> *FStack = NULL)
{
	if(BB == NULL){
		assert(0);
	}
	D(printStack(FStack);)
	auto TerminatorInst = BB->getTerminator();
	int numSucc = TerminatorInst->getNumSuccessors();
	int calledFunctionBF = 1;
	D(std::cerr << __func__ << "(): " << BB->getName().data() << std::endl;)
	if(isLoopBack(BB->getName().data(),bbStack)){
		D(std::cerr << __func__ << "(): " << BB->getName().data() << " is loopback"  << std::endl;)
		auto alternateBB = getAlternatePath(BB, bbStack);
		calledFunctionBF = getBFOfFunctionCalls(alternateBB, FStack);
		bbStack	->push(alternateBB->getName().data());
		auto currentBB_BF = calledFunctionBF * getBasicBlockBF(alternateBB, bbStack, FStack);
		bbStack->pop();	
		return currentBB_BF;
	}else{
		if (numSucc == 0){
			BFMap->insert(std::pair<BasicBlock *, int> (BB, 1));
			calledFunctionBF = getBFOfFunctionCalls(BB, FStack);
			D(std::cerr << __func__ << "(): " << "reached terminator block " << BB->getName().data() << std::endl;)
			D(printStack(bbStack);)
			return calledFunctionBF;
		}else{
			calledFunctionBF = getBFOfFunctionCalls(BB, FStack);	
			auto TerminatorInst = BB->getTerminator();
			int currentBB_BF = 0;
			for(int i = 0 ; i < numSucc ; i++){
				auto nextBB = TerminatorInst->getSuccessor(i);
				//calledFunctionBF = getBFOfFunctionCalls(nextBB, FStack);
				bbStack->push(nextBB->getName().data());
				D(std::cerr << __func__ << "(): calling BB_BF of " << nextBB->getName().data()  << std::endl;)
				//printStack(bbStack);
				currentBB_BF += (calledFunctionBF * getBasicBlockBF(nextBB, bbStack, FStack));
				bbStack->pop();
			}
			BFMap->insert( std::pair<BasicBlock *, int> (BB, currentBB_BF) );
			return currentBB_BF;
		}
	}
}

void pathCounter:: displayCFMap()
{
	for(auto it = CFMap->begin() ; it != CFMap->end() ; it++)
	{
		std::cerr << it->first->getName().data() << " -> " << it->second << std::endl;
	}	
}

void pathCounter:: displayBFMap()
{
	for(auto it = BFMap->begin() ; it != BFMap->end() ; it++)
	{
		//if(!strcmp(it->first->getName().data(),"entry")){
			std::cerr << it->first->getName().data() << " -> " << it->second << std::endl;
			if(!strcmp(it->first->getName().data(),"entry"))
				functionBFMap.insert(std::pair<const char *, int> ( F->getName().data(), it->second));	
		//}
	}
}

void pathCounter :: displayFunctionBFMap()
{
	for(auto it = functionBFMap.begin() ; it != functionBFMap.end() ; it++)
	{
		std::cerr << it->first << "():" << it->second << std::endl;
	}
}


/* Convergence factor of a basic block is the number of if.end conditions that
 * follow a block. The more degree of convergence, the more number of path combinations 
 * are possible
 * */

void pathCounter :: generateConvergenceFactor()
{
	auto StartBB = F->begin();
	CFMap = new std::map <BasicBlock *, int>;
	assert(StartBB->getName().data() != NULL);
	int SBconv = getConvergence(StartBB);
	CFMap->insert (std::pair<BasicBlock *, int >  (StartBB,SBconv));
	displayCFMap();
	delete CFMap;
	return;
}

template <typename T>
bool pathCounter :: isLoopBack(T *currentBB, std::stack <T *> *bbStack){
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

// currentBB ends with a star
bool pathCounter:: isLoopBackBB(const char *currentBB){
	std::string s(currentBB);
	if (s.find("*") != std::string::npos){
		return true;
	}
	return false;
}

bool pathCounter:: inStack(const char *element, std::stack<const char *> *bbStack){
	std::stack <const char *> temp;
	bool elementExists = false;
	// scan through all stack elements,
	while(!bbStack->empty()){
		auto top = bbStack->top();
		if(top == element){
			elementExists = true;
		}
		temp.push(top);
		bbStack->pop();		
	}
	// restore stack
	while(!temp.empty()){
		auto top = temp.top();
		bbStack->push(top);
		temp.pop();
	}
	return elementExists;

}

// scan through stack for LoopBlockName. Record path that was stored in the stack 
// i.e. the basic block that was selected in LoopBlockName. return alternate path.

BasicBlock * pathCounter:: getAlternatePath( BasicBlock *LoopBlock, std::stack <const char *> *bbStack)
{
	std::stack <const char *> temp;
	const char *prev;
	const char *LoopBlockName = LoopBlock->getName().data();

	D(std::cerr << __func__ << "(): LoopbackBlock = " << LoopBlockName << std::endl;)

	if(bbStack->empty()){
		D(std::cerr << "STACK empty, returning" << std::endl;)
		return NULL;
	}
	// remove first loopback block from stack.
	auto top = bbStack->top();
	temp.push(top);
	bbStack->pop();
	
	// search for the second loopback block.
	while(!bbStack->empty()){
		auto top = bbStack->top();
		if(top == LoopBlockName){
			D(std::cerr << "top is " << top << std::endl;)
			break;	
		}else{
			prev = top;	// prev contains element traversed after LoopBlock
			D(std::cerr << "top is " << top << " assigning prev " << prev << std::endl;)
			temp.push(top);
			bbStack->pop();
		}
	}
	//std::cerr << "restoring stack " << std::endl;
	while(!temp.empty()){
		auto top = temp.top();
		bbStack->push(top);
		temp.pop();
	}		
	D(std::cerr << __func__ << "(): previous traversed block = " << prev << std::endl;)
	auto TermInst = LoopBlock->getTerminator();
	BasicBlock *prevBB;
	for(unsigned i = 0; i < TermInst->getNumSuccessors() ; i++){
		if(TermInst->getSuccessor(i)->getName().data() != prev){
			D(std::cerr << __func__ << "(): returning alternate path " << TermInst->getSuccessor(i) << std::endl;)
			return TermInst->getSuccessor(i);
		}else{
			prevBB = TermInst->getSuccessor(i);
		}
	}
	
	D(std::cerr << LoopBlock->getName().data() << "returning previous path " << prevBB->getName().data() << std::endl;)
	return prevBB;
}

const char * pathCounter:: getAlternatePath(const char *currentBB, std::stack <const char *> *bbStack)
{
	std::string s(currentBB);	
	auto loopBBStr = s.substr(0, s.find("*"));
	auto loopBB = loopBBStr.data();
	auto bbIt = BBSuccessorMap.begin();
	for(; bbIt != BBSuccessorMap.end() ; bbIt++){
		if(!strcmp(bbIt->first, loopBB)){
			break;
		}
	}
	auto childrenList = bbIt->second;
	for(auto children = childrenList.begin(); children!= childrenList.end(); children++)
	{
		if(!inStack(*children, bbStack)){
			return *children;	
		}
	}
	std::cerr << "Could not find alternate route to loop, cannot find termination path" << std::endl;
	assert(0);
}

void pathCounter :: generatePaths(std::stack <const char *> *bbStack)
{
	if (bbStack->empty()){
		std::cerr << "Stack Is empty" << std::endl;
		return;
	}else{
		auto currentBB = bbStack->top();
		bool matchFound = false;
		//find BB Successor
		auto bbIt = BBSuccessorMap.begin();
		for(; bbIt != BBSuccessorMap.end() ; bbIt++){
			if(!strcmp(bbIt->first, currentBB)){
				matchFound = true;
				break;
			}
		}
		if(!matchFound){
			//std::cerr << "FOUND BB with no Children " << currentBB << std::endl;
			// if found a loop back BB, push alternate path BB
			if(isLoopBackBB(currentBB)){
				//std::cerr << "CurrentBB detected as LoopBack BB " << currentBB << std::endl;
				auto alternateBB = getAlternatePath(currentBB,bbStack);
				//std::cerr << "Alternate BB for the LoopBack BB " << alternateBB << std::endl;
				if(alternateBB != NULL){
					bbStack->push(alternateBB);
					//printStack(bbStack);
					generatePaths(bbStack);
					bbStack->pop();
				}else{
					printStack(bbStack);
				}
			}else{
				printStack(bbStack);
			}
		}else{
			//std::cerr << "CHILDREN EXIST for " << currentBB  << std::endl;
			for (auto children = bbIt->second.begin(); children != bbIt->second.end() ; children++){
				if(isLoopBack(*children,bbStack)){
					// if loop is detected, mark the loop back BB
					std::string s(*children);
					auto loopBB = s + '*';
					bbStack->push(loopBB.data());
					//std::cerr << "LOOP BACK DETECTED, ADDING LOOP BACK BB" << loopBB.data() << std::endl;
					//printStack(bbStack);
				}else{
					//std::cerr << "PUSHING CHILD TO STACK" << *children << std::endl;
					bbStack->push(*children);
					//printStack(bbStack);
				}	
				generatePaths(bbStack);
				bbStack->pop();
			}
		}
	}
}

void pathCounter:: traceFunctionCallGraph()
{
	std::string funName(F->getName().data());
	BBSuccessorMap.clear();
	for(auto &BB : *F){
		std::string bbName(BB.getName().data());
		//std::cerr << F->getName().data() << "()"<< BB.getName().data() << ":";
		auto TermInst = BB.getTerminator();
		auto numSuccessors = TermInst->getNumSuccessors();
		if(numSuccessors == 0){
	//		std::cerr << BB.getName().data() << " has no successors " << std::endl;
			;
		}else{	
			for(unsigned i = 0 ; i < numSuccessors ; i++){
				//std::cerr << TermInst->getSuccessor(i)->getName().data() << ",";
				BBSuccessorMap[BB.getName().data()].push_back(TermInst->getSuccessor(i)->getName().data());
			}
			//std::cerr << std::endl;
		}
	}
	//displayMap();
  	std::stack<const char *> bbStack;
	bbStack.push("entry");
	generatePaths(&bbStack);
}

/* create branching factor for each function, without taking function
 * calls into consideration
 * */

void pathCounter :: getFunctionBFWithoutCalls()
{
	auto StartBB = F->begin();
	BFMap = new std::map <BasicBlock *, int>;
	std::stack <const char *> bbStack;
	assert(StartBB->getName().data() != NULL);
	bbStack.push(StartBB->getName().data());
	int StartBBcount = getBasicBlockBF(StartBB, &bbStack);
	BFMap->insert (std::pair<BasicBlock *, int >  (StartBB,StartBBcount));
	//displayBFMap();
	delete BFMap;
	return;
}

int pathCounter :: getFunctionBF(std::stack <const char*> *FStack)
{
	// get current Function Context.
	D(std::cerr << __func__ << "()" << std::endl;)
	D(printStack(FStack);)
	assert(!FStack->empty());
	auto FunName = FStack->top();
	//FStack->pop();

	D(std::cerr << "Processing BF for Function " << FunName << "()" << std::endl;)
	if(isLoopBack(FunName,FStack)){
		std::cerr << __func__ << "(): " << FunName << " is loopback"  << std::endl;
		return 0;
	}
	std::stack <const char *> localStack;

	localStack.push("entry");
	// compute and return BF here
	return getBasicBlockBF(M->getFunction(FunName)->begin(), &localStack, FStack);
}

/* 
 * getModuleLevelBF() maintans two stacks - function level and bb level.
 * go through each called function recursively and continue till we reach
 * one of the following conditions:
 * 
 * a) end of main
 * b) recursive call to a function.
 * 
 * if loops occur within a function, resolve them using the same heuristics
 * as used before.
 *
 * */

void pathCounter:: getModuleLevelBF()
{
	// get main function.
	for(auto &F_ : M->functions())
	{
		F = &F_;
		if(!strcmp(F->getName().data(),"main")){
			break;
		}
	}
	// do BF calculation recursively starting from main
	std::stack <const char *> functionStack;
	functionStack.push(F->getName().data());
	//std::stack <const char *> globalBBStack;
	//TODO use globalBBStack to maintain state of global basic blocks
	int totalBF = getFunctionBF(&functionStack);
	std::cerr << "Total BF " << totalBF << std::endl;
}

bool pathCounter::runOnModule(Module &M_) {
        M = &M_;
        C = &(M->getContext());
        DL = M->getDataLayout();
        IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
        VoidTy = Type::getVoidTy(*C);
        VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));

	// get different function call paths possible.

	//for(auto &F_ : M->functions())
	//{
	//	F = &F_;
	//	if(!F->isDeclaration()){
	//		std::cerr << F->getName().data() << std::endl;
	//		getFunctionBFWithoutCalls();
	//	}
	//}
	getModuleLevelBF();

	//displayBFMap();	

	generateTaintInfo();
	//generateTestCases();
	//displayFunctionBFMap();
	// get different basic block sequence of calls possible.
        return true;
}

void pathCounter:: processBlock(BasicBlock *BB)
{
//	std::cerr << BB->getName().data() << std::endl;
	for(auto &I : *BB){
		if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
      			  runOnLoad(BB,LI);
		} else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
    			  runOnStore(BB, SI);
    		} /*else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(&I)) {
      			runOnIntrinsic(BB, MI);
    		} else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
      			runOnCall(BB, CI);
    		} else if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
      			runOnReturn(BB, RI);
    		} */else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(&I)) {
      			runOnUnary(BB, UI);
    		} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(&I)) {
      			runOnBinary(BB, BI);
    		} else if (ICmpInst *IC = dyn_cast<ICmpInst>(&I)) {
      			runOnICmp(BB, IC);	
    		} 
	}
}

//void pathCounter:: generateTestCases()
//{
////	for(auto &F_ : M->functions())
////	{
////		F = &F_;
////  		for (auto &B : *F) {
////			processBasicBlock(&B);
////		}
////	}
//}

void pathCounter :: processDFS(BasicBlock *B, std::stack<const char *> *BBStack)
{
//	if(std::find (processedBlocks.begin(), processedBlocks.end(), B->getName().data()) == processedBlocks.end()){
//		//processBlock(B);
//		//std::cerr << B->getName().data() << std::endl;
//		processedBlocks.push_back(B->getName().data());
//	}else{
//		return;
//	}
	if(B->getTerminator()->getNumSuccessors() == 0){
		BBStack->push(B->getName().data());
		printStack(BBStack);
		BBStack->pop();
		return ;
	}else {
		if(isLoopBack(B->getName().data(), BBStack)){
			B = getAlternatePath(B, BBStack);
			processDFS(B, BBStack);
		}else{
			for(unsigned int i = 0 ; i < B->getTerminator()->getNumSuccessors() ; i++){
				BBStack->push(B->getName().data());
				processDFS(B->getTerminator()->getSuccessor(i), BBStack);
				BBStack->pop();
			}
		}
	}
}

void pathCounter:: generateTaintInfo()
{
	for(auto &F_ : M->functions())
	{
		F = &F_;
		std::stack <const char *> BBStack;
  		auto B = F->begin(); 
		if(!F->isDeclaration()){
			std::cerr << "checking the dfs algo" << std::endl;
			runOnFunction();
			processDFS(B, &BBStack);
			runOnFunctionEnd();
		}
	}
}

void pathCounter::runOnBB(BasicBlock *BB) {
	for (auto &I: *BB)	{
		if (dyn_cast<LoadInst>(&I)!=nullptr) {
			std::cout << "calling trackLoad " << std::endl;
      trackLoad(&I);
    } 	
 }
}


// Instrument every instruction in a function.
void pathCounter::runOnFunction() {
  numVSets = 0;
  collectInstructions();
  initVSets();
  combineVSets();
  labelVSets();
  allocaVSetArray();
  runOnArgs();
}

void pathCounter::runOnFunctionEnd() {
  ArgToVSet.clear();
  IIs.clear();      
  VSets.clear();
  VtoVSet.clear();
  IdxToVar.clear();
}

// Collect a list of all instructions. We'll be adding all sorts of new
// instructions in so having a list makes it easy to operate on just the
// originals.
void pathCounter::collectInstructions(void) {
  for (auto &B : *F) {
    for (auto &I : B) {
	//		std::cerr << F->getName().data() << "():"<< B.getName().data() ; std::cerr << " " << &I << std::endl;
      IIs.push_back({&B, &I});
    }
  }
}

// Group the values (instructions, arguments) into sets where each set
// represents a logical variable in the original program.
void pathCounter::initVSets(void) {
  VSets.resize(IIs.size() + F->arg_size());

  for (auto &VSet : VSets) {
    VSet.rep = &VSet;
    VSet.index = -1;
  }

  auto i = 0UL;
  for (auto &A : F->args()) {
    auto VSet = &(VSets[i++]);
    VtoVSet[&A] = VSet;
    ArgToVSet[&A] = VSet;
  }
  for (auto &II : IIs) {
    auto VSet = &(VSets[i++]);
    VtoVSet[II.I] = VSet;
  }
}

// Combine value sets.
// go through each of the Instructions. Check the incoming 
// nodes of each of the instructions. If the incoming vertex is
// not from a constant, combine the incoming value with the Vset corresponding
// to the Instruction that you just read.
void pathCounter::combineVSets(void) {
  for (auto &II : IIs) {
    auto I = II.I;
    auto VSet = VtoVSet[I];
    if (PHINode *PHI = dyn_cast<PHINode>(I)) {
      auto nV = PHI->getNumIncomingValues();
      for (auto iV = 0U; iV < nV; ++iV) {
        auto V = PHI->getIncomingValue(iV);
        if (!isa<Constant>(V)) {
          auto incomingVSet = VtoVSet[V];
          combineVSet(VSet, incomingVSet);
        }
      }
    }
  }
}

// Combine two value sets. This implements disjoint set union.
// Build a chain/tree. Point Vset to the Vset which has lower value.
// parent --> child.
void pathCounter::combineVSet(VSet *VSet1, VSet *VSet2) {
  VSet1 = getVSet(VSet1);
  VSet2 = getVSet(VSet2);
  if (VSet1 < VSet2) {
    VSet2->rep = VSet1;
  } else if (VSet1 > VSet2){
    VSet1->rep = VSet2;
  }
}

// Get the representative of this VSet. Implements union-find path compression.
VSet *pathCounter::getVSet(VSet *VSet) {
  while (VSet->rep != VSet) {
    VSet = (VSet->rep = VSet->rep->rep);
  }
  return VSet;
}

// Assign array indices to each VSet. This labels all variables from 0 to N-1.
void pathCounter::labelVSets(void) {
  for (auto &rVSet : VSets) {
    auto pVSet = getVSet(&rVSet);
    if (-1 == pVSet->index) {
      pVSet->index = numVSets++;
    }
  }
}

// Allocate an array to hold the slice taints for each variable in this
// function.
// ilist insert inserts a new element at the beginning of the list
// keep moving child pointers point to 1 root parent.
void pathCounter::allocaVSetArray(void) {
  auto &B = F->getEntryBlock();
  auto &IList = B.getInstList();
  auto &FirstI = *IList.begin();
  for (auto i = 0; i < numVSets; ++i) {
    auto TaintVar = new AllocaInst(IntPtrTy);
    IList.insert(FirstI, TaintVar);
    IList.insert(FirstI, new StoreInst(ConstantInt::get(IntPtrTy, 0, false),
                                       TaintVar));
    IdxToVar.push_back(TaintVar);
  }
  AfterAlloca = &FirstI;
}

void pathCounter::track(Value *V){
	if( std::find(trackTaint.begin(), trackTaint.end(), V) == trackTaint.end()){
		std::cerr << __func__ << "():added a taint tracker " << V << std::endl; 
		trackTaint.push_back(V);
	}
}

int pathCounter::marked(Value *V){
	for (auto taint : trackTaint){
			if( taint == V){
			  std::cerr << "Value Marked" << std::endl;
			  return true;
		  }	
	}
	std::cerr << "Value NOT Marked" << std::endl;
	return false;
//	if( std::find(trackTaint.begin(), trackTaint.end(), V) == trackTaint.end()){
//		std::cerr << "Value NOT Marked" << std::endl;
//		return false;
//	}else{
//		std::cerr << "Value Marked" << std::endl;
//		return true;
//	}
}

// Instrument the arguments.
void pathCounter::runOnArgs(void) {
  if (!AfterAlloca) return;
  auto &IList = AfterAlloca->getParent()->getInstList();
  auto LoadFunc = CreateFunc(IntPtrTy, "__fslice_load_arg", "", IntPtrTy);
  for (auto &A : F->args()) {
    if (auto TA = getTaint(&A)) {
      auto T = CallInst::Create(
          LoadFunc, {ConstantInt::get(IntPtrTy, A.getArgNo(), false)});
      IList.insert(AfterAlloca, T);
      IList.insert(AfterAlloca, new StoreInst(T, TA));
    }
  }
}

//// Insert function to print Function Name.
//void pathCounter::printFunctionName(const char * s){
//	if(!AfterAlloca) return;
//	if(!s) return;
//	auto &IList = AfterAlloca->getParent()->getInstList();
//  	auto FunName = CreateString(s);
//	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", FunName->getType());
//	auto PR = CallInst::Create(PrintFunc, {FunName});
//	IList.insert(AfterAlloca, PR); 	
//}
//
//// Insert function to print Function Name.
//void pathCounter::pushToCallStack(const char *s){
//	if(!AfterAlloca) return;
//	auto &IList = AfterAlloca->getParent()->getInstList();
//  	auto FunName = CreateString(s);
//	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_push_to_call_stack","", FunName->getType());
//	auto PR = CallInst::Create(PrintFunc, {FunName});
//	IList.insert(AfterAlloca,PR); 	
//}
//
//// Print call Trace for a function.
//void pathCounter::printCallTrace() {
//	if(!AfterAlloca) return;
//	auto &IList = AfterAlloca->getParent()->getInstList();
//	//auto Arglist = CreateString(bt.c_str());
//	//auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", Arglist->getType());
//	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_call_trace","");
//	auto PR = CallInst::Create(PrintFunc);
//	IList.insert(AfterAlloca, PR); 	
//}
//
//// Insert function to print a string before I.
//void pathCounter::printString(Instruction *I, const char * s){
//	return;
//	if(!AfterAlloca) return;
//	if(!s) return;
//	auto &IList = AfterAlloca->getParent()->getInstList();
//  	auto FunName = CreateString(s);
//	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", FunName->getType());
//	auto PR = CallInst::Create(PrintFunc, {FunName});
//	IList.insert(I, PR); 	
//}

// Returns the size of a loaded/stored object.
//static uint64_t LoadStoreSize(const DataLayout *DL, Value *P) {
//  PointerType *PT = dyn_cast<PointerType>(P->getType());
//  return DL->getTypeStoreSize(PT->getElementType());
//}

void pathCounter ::trackLoad(Value *I) {
	std::cerr << __func__ << " check for P " << std::endl;
	auto P = ((LoadInst *)I)->getPointerOperand();
	if(marked(P)){
		std::cerr << "Load Instruction contains tracked variable " << std::endl;
	}else if(marked(I)){
		std::cerr << "Load Instruction is tainted " << std::endl;
		track(P);
  } else {
		std::cerr << "Not Tainted " << I << " " << P << std::endl;
	}
}

// Instrument a single instruction.
void pathCounter::runOnLoad(BasicBlock *B, LoadInst *LI) {
    auto P = (uint64_t)LI->getPointerOperand();
//    auto S = LoadStoreSize(DL, P);
	if(taintMap.find(P) == taintMap.end()){
		taintMap[P] = taintVal;
		taintVal ++;
	} 
    std::cerr << B->getName().data() << " Load " << taintMap[P] << /*" SIZE " << std::to_string(S) <<*/ std::endl;
}

// Get a value that contains the tainted data for a local variable, or zero if
// the variable isn't tainted.
Value *pathCounter::LoadTaint(Instruction *I, Value *V) {
  auto &IList = I->getParent()->getInstList();
  Instruction *RV = nullptr;
  if (auto TV = getTaint(V)) {
    RV = new LoadInst(TV);
  } else {
    if (IntegerType *IT = dyn_cast<IntegerType>(V->getType())) {
      Instruction *CV = nullptr;
      if (IT->isIntegerTy(IntPtrTy->getPrimitiveSizeInBits())) {
        CV = CastInst::CreateBitOrPointerCast(V, IntPtrTy);
      } else {
        CV = CastInst::Create(Instruction::ZExt, V, IntPtrTy);
      }
      IList.insert(I, CV);
      auto ValueFunc = CreateFunc(IntPtrTy, "__fslice_value", "",
                                  IntPtrTy);
      RV = CallInst::Create(ValueFunc, {CV});
    } else {
      return ConstantInt::get(IntPtrTy, 0, false);
    }
  }
  IList.insert(I, RV);
  return RV;
}

// Instrument a single instruction.
void pathCounter::runOnStore(BasicBlock *B, StoreInst *SI) {
	
    auto P = (uint64_t)SI->getPointerOperand();
//    auto S = LoadStoreSize(DL, P);
    auto V = SI->getValueOperand();
	if(taintMap.find(P) == taintMap.end()){
		taintMap[P] = taintVal++;
	}
    		std::cerr << B->getName().data() << " Store " << taintMap[P] << /*" SIZE " << std::to_string(S) << */" VALUE " << V << std::endl;
}

void pathCounter::runOnCall(BasicBlock *B, CallInst *CI) {
  auto &IList = B->getInstList();
  auto StoreFunc = CreateFunc(VoidTy, "__fslice_store_arg", "",
                              IntPtrTy, IntPtrTy);
  auto i = 0UL;
  for (auto &A : CI->arg_operands()) {
    std::vector<Value *> args = {ConstantInt::get(IntPtrTy, i++, false),
                                 LoadTaint(CI, A.get())};
    IList.insert(CI, CallInst::Create(StoreFunc, args));
  }

	if (!strcmp(  CI->getCalledFunction()->getName().data(), "_mark")){
		auto arg = CI->getArgOperand(0);
		track(arg);
	} else{
    std::cerr << "Intercepted call to " << CI->getName().data() << std::endl;
  }

  if (CI->user_empty()) return;

	  Instruction* st;
  if (auto RT = getTaint(CI)) {
    auto LoadFunc = CreateFunc(IntPtrTy, "__fslice_load_ret", "");
    auto TR = CallInst::Create(LoadFunc);
	st = new StoreInst(TR, RT);
    IList.insertAfter(CI, st);
    IList.insertAfter(CI, TR);
  }
}

void pathCounter::runOnReturn(BasicBlock *B, ReturnInst *RI) {
  if (auto RV = RI->getReturnValue()) {
    auto &IList = B->getInstList();
    auto StoreFunc = CreateFunc(VoidTy, "__fslice_store_ret", "",
                                IntPtrTy);
    IList.insert(RI, CallInst::Create(StoreFunc, {LoadTaint(RI, RV)}));
  }

  // remove function name from call stack on return
  auto &IList = B->getInstList();
  auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_pop_from_call_stack","");
  auto PR = CallInst::Create(PrintFunc);
  IList.insert(RI, PR);
}


void pathCounter::runOnUnary(BasicBlock *B, UnaryInstruction *I) {
	//auto Op = CreateString(I->getOpcodeName());	
	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
	}
	std::cerr  << B->getName().data() << " Unary Operand " << I->getOpcodeName() << " " << taintMap[(uint64_t)I->getOperand(0)] << std::endl;
}

void pathCounter::runOnBinary(BasicBlock *B, BinaryOperator *I) {
	//auto Op = CreateString(I->getOpcodeName());	
	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
	}
	if(taintMap.find((uint64_t)I->getOperand(1)) == taintMap.end()){
		taintMap[(uint64_t)I->getOperand(1)] = taintVal++;
	}
	std::cerr  << B->getName().data()<< "Binary Operand " << I->getOpcodeName() << " Op1 = " << taintMap[(uint64_t)I->getOperand(0)] << " Op2 = " << taintMap[(uint64_t)I->getOperand(1)] << std::endl;
}

void pathCounter::runOnICmp(BasicBlock *B, ICmpInst *I) {
	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
	}
	if(taintMap.find((uint64_t)I->getOperand(1)) == taintMap.end()){
		taintMap[(uint64_t)I->getOperand(1)] = taintVal++;
	}
	auto Pred = I->getUnsignedPredicate();
	std::cerr  << B->getName().data()<< "Predicate " << Pred << "LO = " << taintMap[(uint64_t)I->getOperand(0)] << " RO = " << taintMap[(uint64_t)I-> getOperand(1)] << std::endl;
}

void pathCounter::runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI) {
  const char *FName = nullptr;
  auto CastOp = Instruction::PtrToInt;
  if (isa<MemSetInst>(MI)) {
    CastOp = Instruction::ZExt;
    FName = "__fslice_memset";
  } else if (isa<MemCpyInst>(MI)) {
    FName = "__fslice_memcpy";
  } else if (isa<MemMoveInst>(MI)) {
    FName = "__fslice_memmove";
  } else {
    return;
  }

  auto &IList = B->getInstList();
  auto MemF = CreateFunc(VoidPtrTy, FName, "", IntPtrTy, IntPtrTy, IntPtrTy);
  auto MDest = CastInst::CreatePointerCast(MI->getRawDest(), IntPtrTy);
  IList.insert(MI, MDest);

  auto Src = CastInst::Create(CastOp, MI->getArgOperand(1), IntPtrTy);
  IList.insert(MI, Src);

  std::vector<Value *> args = {MDest, Src, MI->getLength()};
  IList.insert(MI, CallInst::Create(MemF, args));

  MI->eraseFromParent();
}

Value *pathCounter::getTaint(Value *V) {
  if (V->getType()->isFPOrFPVectorTy()) return nullptr;
  if (VtoVSet.count(V)) {
    auto index = VtoVSet[V]->index;
    if (-1 == index) return nullptr;
    return IdxToVar[index];
  } else {
    auto it = std::find(IdxToVar.begin(), IdxToVar.end(), V);
    if (it == IdxToVar.end()) return nullptr;
    return *it;
  }
}

char pathCounter::ID = '\0';
unsigned int pathCounter ::taintVal= 0;

static RegisterPass<pathCounter> X(
    "pathCounter",
    "pathCounter",
    false,  // Only looks at CFG.
    false);  // Analysis Pass.
