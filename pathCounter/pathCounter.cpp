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
  void printGbbMap(std::map <std::string, unsigned> *GbbMap);
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
  void getFunctionPPWithoutCalls();
  void getModuleLevelPP( std::map <std::string, unsigned> *GbbMap);
	std::map <uint64_t, uint64_t> taintMap;
	bool markedProcessed();
	bool processedFunctionCaller();
	void analyseFunctionCalls();
  void runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI);
  int getFunctionPP(std::stack <const char*> *FStack, std::map<std::string, unsigned> *GbbMap);
	void generateTaintInfo();
	void processBlock(BasicBlock *BB);
	std::vector<const char *> processedBlocks;
  int getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map<std::string, unsigned> *GbbMap);
	void processDFS(BasicBlock *B, std::stack <const char *> *BBStack);
	void processBasicBlock(BasicBlock *BB);
	//void generateTestCases();
  //BasicBlock *getBB(const char *name);
	int getCF(BasicBlock *BB);
	int getBasicBlockPP(BasicBlock *BB, std::stack <const char *> *bbStack, std::map< const char *, int > *bbMap , std::stack <const char *> *FStack, std::map < std::string, unsigned > *GbbMap);

	void printCFMap();
	void printPaths();
	void printFunctionPPMap();
	void printStack(std::stack <const char *> *bbStack);
	int  getConvergence(BasicBlock *BB);
	int  getMaxConvergence(TerminatorInst *I);

	void runOnBB(BasicBlock *BB);
	void trackLoad(Value *I);
	void printMap();
	template <typename T>
	bool isLoopBack(T *currentBB, std::stack <T *> *bbStack);
	bool isLoopBackBB(const char *currentBB);
	bool inStack(const char *element, std::stack<const char *> *bbStack);
	const char * getAlternatePath(const char *currentBB, std::stack <const char *> *bbStack);
	BasicBlock * getAlternatePath(BasicBlock *ForLoopBlock, std::stack <const char *> *bbStack);
	bool isTerminalFunction();
	void getTerminalFunctions();
	void processBBInstructions();
	void evaluatePath(std::map<std::string, unsigned > *GbbMap);

	void printFunCallFromBB(const char *bbName);
  void track(Value *V);
  int marked(Value *V);

  Value *getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	std::map<BasicBlock *, int> *CFMap = new std::map <BasicBlock *, int>;
	std::map<BasicBlock *, int> *PPMap = new std::map <BasicBlock *, int>;
	std::map<const char *, int> functionPPMap;
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

  BasicBlock *LocalBB;
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

void pathCounter :: printMap()
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

/* getPPofFunctionCalls - generates Path Potential of the functions that are called from a
 * basic block BB.
 * */

int pathCounter :: getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map <std::string, unsigned > *GbbMap)
{
	int functionPP = 1;
	if(FStack == NULL)
		return functionPP;
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
				// we do not have the function definition, we just have the function declaration.
				std::cerr << FStack->top() << "() BLACK BOX " << calledFunction << std::endl;
				continue;
			}
			// XXX why is this going into infinite loop?
			if(!strcmp(calledFunction , "quotearg_buffer_restyled")){
				continue;
			}
			if(functionPPMap.find(calledFunction) == functionPPMap.end()){
	    			FStack->push(calledFunction);
				auto calledFunctionPP = getFunctionPP(FStack, GbbMap);
				functionPP *= calledFunctionPP;
				std::cerr << __func__ << "():" << calledFunction << calledFunctionPP << std::endl;
				functionPPMap[calledFunction] = calledFunctionPP;
				FStack->pop();
			}else{
				functionPP *= functionPPMap[calledFunction];
				D(std::cerr << __func__ << "():" << FStack->top() << functionPP << " after processing " << calledFunction << std::endl;)
			}
		}
	}
	return functionPP;
}

/* getBasicBlockPP calculates the Path Potential for each Basic Block.
 * */

int pathCounter :: getBasicBlockPP(BasicBlock *BB, std::stack <const char *> *bbStack, std::map <const char *, int> *bbMap ,std::stack <const char *> *FStack, std::map<std::string, unsigned> *GbbMap)
{
	if(BB == NULL){
		assert(0);
	}
	D(printStack(FStack);)
	auto TerminatorInst = BB->getTerminator();
	int numSucc = TerminatorInst->getNumSuccessors();
	int calledFunctionPP = 1;
	D(std::cerr << __func__ << "(): " << BB->getName().data() << std::endl;)
	auto bbName = BB->getName().data();
	if(bbMap->find(bbName) != bbMap->end()){
		std::cerr <<  FStack->top() << "():Found BB in map " << bbName << std::endl; 
		return (*bbMap)[bbName];
	}
	// **collision stuff
	if(isLoopBack(bbName,bbStack)){
		std::cerr << __func__ << "(): " << FStack->top() << " " << bbName << " is loopback"  << std::endl;
		auto alternateBB = getAlternatePath(BB, bbStack);
		calledFunctionPP = getPPOfFunctionCalls(alternateBB, FStack, GbbMap);
		auto alternateBBName = alternateBB->getName().data();
		int alternateBB_PP;
		if(bbMap->find(alternateBBName) != bbMap->end()){
			alternateBB_PP = (*bbMap)[alternateBBName];
		}else{
			bbStack	->push(alternateBBName);
			alternateBB_PP = getBasicBlockPP(alternateBB, bbStack, bbMap, FStack, GbbMap);
			bbMap->insert(std::pair<const char *, int>(alternateBBName, alternateBB_PP)); 
			std::string funNameBB(FStack->top());
			funNameBB += alternateBBName;
			GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),alternateBB_PP));
			bbStack->pop();
		}
		auto currentBB_PP = calledFunctionPP * alternateBB_PP;
		if(bbMap->find(bbName) != bbMap->end()){
			std::cerr << "**** LOOP Collision ****" << FStack->top() << "():" << bbName << std::endl;
		}else{
			bbMap->insert(std::pair<const char *, int>(bbName, currentBB_PP));	
			std::string funNameBB(FStack->top());
			funNameBB.append(bbName);
			GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
		}
		return currentBB_PP;
	}else{
		if (numSucc == 0){
			PPMap->insert(std::pair<BasicBlock *, int> (BB, 1));
			auto currentBB_PP = getPPOfFunctionCalls(BB, FStack, GbbMap);
			D(std::cerr << __func__ << "(): " << "reached terminator block " << BB->getName().data() << std::endl;)
			D(printStack(bbStack);)
			if(bbMap->find(bbName) != bbMap->end()){
				std::cerr << "**** SUCC 0 Collision ****" << FStack->top() << "():" << bbName << std::endl;
			}else{
				bbMap->insert(std::pair<const char *, int>(bbName, currentBB_PP));
				std::string funNameBB(FStack->top());
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
			}
			return currentBB_PP;
		}else{
			calledFunctionPP = getPPOfFunctionCalls(BB, FStack, GbbMap);	
			auto TerminatorInst = BB->getTerminator();
			int currentBB_PP = 0;
			for(int i = 0 ; i < numSucc ; i++){
				auto nextBB = TerminatorInst->getSuccessor(i);
				//calledFunctionPP = getPPOfFunctionCalls(nextBB, FStack);
				auto nextBBName = nextBB->getName().data();
				int nextBB_PP;
				if(bbMap->find(nextBBName) != bbMap->end()){
					nextBB_PP = (*bbMap)[nextBBName];
				}else{
					bbStack->push(nextBBName);
					D(std::cerr << __func__ << "(): calling BB_PP of " << nextBBName  << std::endl;)
					//printStack(bbStack);
					nextBB_PP = getBasicBlockPP(nextBB, bbStack, bbMap, FStack, GbbMap);
					bbMap->insert(std::pair<const char *, int>(nextBBName, nextBB_PP));
					std::string funNameBB(FStack->top());
					funNameBB.append(nextBBName);
					GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),nextBB_PP));
					bbStack->pop();
				}
				currentBB_PP += (calledFunctionPP * nextBB_PP);
			}
			PPMap->insert( std::pair<BasicBlock *, int> (BB, currentBB_PP) );
			if(bbMap->find(bbName) != bbMap->end()){
				std::cerr << "**** SUM UP children Collision ****" << FStack->top() << "():" << bbName << std::endl;
				std::cerr << "PREV VALUE = " << (*bbMap)[bbName] << " new value " << currentBB_PP << std::endl;
				(*bbMap)[bbName] = currentBB_PP;
				std::string funNameBB(FStack->top());
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
			}else{
				bbMap->insert(std::pair<const char *, int>(bbName, currentBB_PP));
				std::string funNameBB(FStack->top());
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
			}
			return currentBB_PP;
		}
	}
}

void pathCounter:: printCFMap()
{
	for(auto it = CFMap->begin() ; it != CFMap->end() ; it++)
	{
		std::cerr << it->first->getName().data() << " -> " << it->second << std::endl;
	}	
}

void pathCounter:: printPaths()
{
	for(auto it = PPMap->begin() ; it != PPMap->end() ; it++)
	{
		D(std::cerr << it->first->getName().data() << " -> " << it->second << std::endl;)
	}
}

void pathCounter :: printFunctionPPMap()
{
	for(auto it = functionPPMap.begin() ; it != functionPPMap.end() ; it++)
	{
		std::cerr << it->first << "():" << it->second << std::endl;
	}
}

void pathCounter :: printGbbMap(std::map <std::string, unsigned > *GbbMap)
{
	for(auto it = GbbMap->begin() ; it != GbbMap->end() ; it++)
	{
		std::cerr << it->first << "():" << it->second << std::endl;
	}
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


int pathCounter :: getFunctionPP(std::stack <const char*> *FStack, std::map <std::string, unsigned> *GbbMap)
{
	// get current Function Context.
	D(printStack(FStack);)
	assert(!FStack->empty());
	auto FunName = FStack->top();
	std::cerr << FunName << "()" << std::endl;
	//FStack->pop();

	D(std::cerr << "Processing PP for Function " << FunName << "()" << std::endl;)
	if(isLoopBack(FunName,FStack)){
		std::cerr << __func__ << "(): " << FunName << " is loopback"  << std::endl;
		FStack->pop();
		std::cerr << "PP: " << FunName << " = " << 0 << std::endl;
		functionPPMap[FunName]=0;
		return 0;
	}
	// compute and return PP here
	int funPP;
	if(functionPPMap.find(FunName) == functionPPMap.end()){
		std::stack <const char *> localStack;
		std::map <const char *, int> bbMap;
		localStack.push("entry");
		funPP = getBasicBlockPP(M->getFunction(FunName)->begin(), &localStack, &bbMap , FStack, GbbMap);
		std::cerr << "PP: " << FunName << " = " << funPP << std::endl;
		functionPPMap[FunName] = funPP;
	}else {
		funPP = functionPPMap[FunName];
		std::cerr << "PP: ALREADY PROCESSED, REUSING " << FunName  << funPP << std::endl;
	}
	return funPP;
}

/* 
 * getModuleLevelPP() maintans two stacks - function level and bb level.
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

void pathCounter:: getModuleLevelPP( std::map < std::string, unsigned> *GbbMap)
{
	bool nomain = true;
	// get main function.
	for(auto &F_ : M->functions())
	{
		F = &F_;
		if(!strcmp(F->getName().data(),"main")){
			nomain = false;
			break;
		}
	}
	if(nomain){
		std::cerr << "Please add main() or mark start function" << std::endl;
		return;
	}
	// do PP calculation recursively starting from main
	std::stack <const char *> functionStack;
	functionStack.push(F->getName().data());
	//std::stack <const char *> globalBBStack;
	int totalPP = getFunctionPP(&functionStack, GbbMap);
	std::cerr << "Total PP " << totalPP << std::endl;
}

void pathCounter::processBBInstructions()
{
	if(LocalBB->hasName())
		std::cerr << "BB()" <<  LocalBB->getName().data() << std::endl;
//	for(&I : LocalBB){
//			
//	}
;
}

void pathCounter::evaluatePath(std::map< std::string, unsigned> *GbbMap)
{
	auto &BB = M->getFunction("main")->getEntryBlock();
	auto TermInst = BB.getTerminator();
	std::list <std::string> traversedBB;
	LocalBB = &BB;
	while(TermInst -> getNumSuccessors() != 0 )
	{
		processBBInstructions();
		if(TermInst->getNumSuccessors() == 0){	// reached end of path
			std::cerr << "Terminating at " << LocalBB->getName().data() << std::endl;
			break;
		}else if(TermInst->getNumSuccessors() == 1){
			LocalBB = TermInst->getSuccessor(0);
			std::cerr << "Next Block " << LocalBB->getName().data() << std::endl;
			if(!LocalBB->hasName())
				continue;
			TermInst = TermInst->getSuccessor(0)->getTerminator();
			std::string str("main");
			str+= LocalBB->getName().data();
			traversedBB.push_back(str);
			std::cerr << "New BB " << LocalBB->getName().data() << std::endl;
		}else{
			unsigned max = 0;
			std::cerr << "checking for " << BB.getName().data() << "successors " << std::endl;
			for(unsigned i = 0 ; i < TermInst->getNumSuccessors() ; i++){
				std::string nextBBName("main");
				nextBBName+= std::string(TermInst->getSuccessor(i)->getName());
				if(GbbMap->find(nextBBName) == GbbMap->end()){
					std::cerr<< "Basic Block PP not found " << nextBBName << std::endl;	
					exit(0);
				}
				if((*GbbMap)[nextBBName] > max && (std::find(traversedBB.begin(), traversedBB.end(), nextBBName) == traversedBB.end())){
					std::cerr << "found " << nextBBName << " with weight " << (*GbbMap)[nextBBName] << std::endl;
					max = (*GbbMap)[nextBBName];
					LocalBB = TermInst->getSuccessor(i);
					TermInst = TermInst->getSuccessor(i)->getTerminator();
				//	if(!LocalBB->hasName())
				//		continue;
				}
			}
			traversedBB.push_back(LocalBB->getName().data());
			processBBInstructions();		
		}
	}
	//processBBInstructions(); // for the terminal Basic Block
}

bool pathCounter::runOnModule(Module &M_) {
	std::map< std::string, unsigned> GbbMap;
	// initialization stuff
        M = &M_;
        C = &(M->getContext());
        DL = M->getDataLayout();
        IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
        VoidTy = Type::getVoidTy(*C);
        VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));

	// get different function call paths possible.
	getModuleLevelPP(&GbbMap);
	std::cerr << "evaluate path" << std::endl;
	evaluatePath(&GbbMap);
	//printFunctionPPMap();
	//std::cerr << "gBMap " << std::endl;
	//std::cerr << "GBBMap Size = " << GbbMap.size() << std::endl;
	//printGbbMap(&GbbMap);
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

/*print all paths in DFS order*/

void pathCounter :: processDFS(BasicBlock *B, std::stack<const char *> *BBStack)
{
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

/*instruments code to call runtime functions  */

void pathCounter:: generateTaintInfo()
{
	for(auto &F_ : M->functions())
	{
		F = &F_;
		std::stack <const char *> BBStack;
  		// XXX uncomment before removing commit below.
  		// auto B = F->begin(); 
		if(!F->isDeclaration()){
			std::cerr << "checking the dfs algo" << std::endl;
			runOnFunction();
			//XXX prints all function path calls. processDFS(B, &BBStack);
			runOnFunctionEnd();
		}
	}
}

void pathCounter::runOnBB(BasicBlock *BB) {
	for (auto &I: *BB)	{
		if (dyn_cast<LoadInst>(&I)!=nullptr) {
			std::cerr << "calling trackLoad " << std::endl;
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

/* cleanup data structures */

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
