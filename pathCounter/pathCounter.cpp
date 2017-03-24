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

struct Taint {
  uint64_t id:32;
  uint64_t offset:31;	// S.J. number of bytes following the address that 
			// have the same taint value as start address.
  bool is_obj:1;	// S.J. Is true for objects allocated on heap
} __attribute__((packed));



// Expands into __fslice_load1 (addr) { return Load (addr, 1) };
//          and __fslice_store1 (addr, Taint taint) { return Store (addr, 1, taint) };
// basically, size can only be 1,2,4,8,16,32 or 64.   

// Set of llvm values that represent a logical variable.
struct VSet {
  VSet *rep;
  int index = 0;
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
  void runOnArgs(void);
  void printFunctionName(const char *s);
  void printGbbMap(std::map <std::string, unsigned> *GbbMap);
  void pushToCallStack(const char *s);
  void printCallTrace();
  void printString(Instruction *I, const char *s);

uint64_t  LoadStoreSize(const DataLayout *DL, Value *P);
  void runOnLoad(BasicBlock *B, LoadInst *LI);
  void runOnStore(StoreInst *SI);
  void runOnCall(BasicBlock *B, CallInst *CI);
  void runOnReturn(BasicBlock *B, ReturnInst *RI);
  void runOnUnary(BasicBlock *B, UnaryInstruction *I);
  void runOnBinary(BasicBlock *B, BinaryOperator *I);
	void runOnICmp(BasicBlock *B, ICmpInst *I);
  void getFunctionPPWithoutCalls();
	void cleanup();
	void instrumentModule(Module *M);


	void Store(uint64_t addr, uint64_t size, Taint t);
	
  void getModuleLevelPP( std::map <std::string, unsigned> *GbbMap);
	//std::map <uint64_t, uint64_t> taintMap;
	bool markedProcessed();
	bool processedFunctionCaller();
	void analyseFunctionCalls();
  void runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI);
	void runOnInstructions(void);
  int getFunctionPP(std::stack <const char*> *FStack, std::map<std::string, unsigned> *GbbMap);
	//void processBlock(BasicBlock *BB);
	std::vector<const char *> processedBlocks;
  int getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map<std::string, unsigned> *GbbMap);
	void processDFS(BasicBlock *B, std::stack <const char *> *BBStack);
	void processBasicBlock(BasicBlock *BB);
  //BasicBlock *getBB(const char *name);
	int getCF(BasicBlock *BB);
	int getBasicBlockPP(BasicBlock *BB, std::stack <const char *> *bbStack, std::map< const char *, int > *bbMap , std::stack <const char *> *FStack, std::map < std::string, unsigned > *GbbMap);

	void printCFMap();
	void printPaths();
	void printFunctionPPMap();
	void printStack(std::stack <const char *> *bbStack);
	int  getConvergence(BasicBlock *BB);
	int  getMaxConvergence(TerminatorInst *I);

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
	void processBBInstructions(std::map <std::string, unsigned> *GbbMap, std::list <std::string > *traversedBB, std::string funName);
	void evaluatePath(std::map<std::string, unsigned > *GbbMap, std::string funName, std::list <std::string> *traversedList);

	void __fslice_store (uint64_t size, Value  *addr , Value *taint);
	void printFunCallFromBB(const char *bbName);
  void track(Value *V);
  int marked(Value *V);

  uint64_t getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	std::map<BasicBlock *, int> *CFMap = new std::map <BasicBlock *, int>;
	std::map<BasicBlock *, int> *PPMap = new std::map <BasicBlock *, int>;
	std::map<const char *, int> functionPPMap;
  	std::vector <Value *> trackTaint;
	// map of functions and pointer to map of (BB,ConvergenceFactor)
	// for each BB in that function.
	std::map <const char *, void *> functionConvergenceFactorMap;
	void taintInstructions();

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
  std::vector<IInfo> IIs;
  std::vector<VSet> VSets;
  std::map<Value *,VSet *> VtoVSet;
  std::map<Value *, uint64_t> ValueTaintMap;
  std::map<uint64_t, uint64_t> ConstantTaintMap;
  std::vector<Value *> IdxToVar;
//  std::vector<uint64_t  IdxToVar;
  std::map<const char *,Value *> StrValues;
  std::map<const char *, std::list <const char *> >  BBSuccessorMap;
  std::list<const char *> processedFunctionNames;
  std::map <Value *, uint64_t> InstructionTaints;


void assignTaint(Value *Dest, Value *Src);
uint64_t assignTaint(Value *Val);

// creates a map of function and map of instruction and taints

  std::map<Function *, std::map<Value *, uint64_t> *> FTMapMap;
  std::map <Value *, uint64_t > * TMap;
// Map of all constant values being referred.
  std::map <uint64_t, uint64_t> * CMap; 
  int numVSets;
  uint64_t taintNo;
};

void pathCounter:: __fslice_store (uint64_t size, Value * addr , Value* taint) { 
					
	return;
}


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
      numVSets(0),
      taintNo(1) {}

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
				// XXX resolve BLACK BOX functions.
				D(std::cerr << FStack->top() << "() BLACK BOX " << calledFunction << std::endl;)
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

void pathCounter::processBBInstructions(std::map <std::string, unsigned> *GbbMap, std::list <std::string > *traversedList, std::string parentFunName)
{
//	if(LocalBB->hasName())
//		std::cerr << parentFunName << "BB()" <<  LocalBB->getName().data() << std::endl;
//	for(auto &I : *LocalBB){
//		if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//			runOnLoad(LocalBB, LI);
//		}/* else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//    			  runOnStore(BB, SI);
//    		} else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(&I)) {
//      			runOnIntrinsic(BB, MI);
//    		} else*/ 
//		if (CallInst *CI = dyn_cast<CallInst>(&I)) {
//			if(CI->getCalledFunction() != NULL && CI->getCalledFunction()->hasName()){
//				auto function = CI->getCalledFunction();
//				auto funName = function->getName().data();
//				if(!strcmp(funName, "_mark")){
//					std::cerr << "Found Mark Function " << std::endl;
//					auto arg = CI->getArgOperand(0);
//					track(arg);
//				}
//				std::cerr << LocalBB->getName().data() << " calls function()" << funName << std::endl;
//				// skip declared functions
//				if(function->isDeclaration()){
//					std::cerr << funName << "() is declaration " << std::endl; 
//					continue;
//				}
//				std::cerr << "EVALUATE PATH" << funName << std::endl;
//				evaluatePath(GbbMap, funName, traversedList);
//			}else{
//				std::cerr << "Name not found for BB " << LocalBB->getName().data() << std::endl;
//			}
//    		}/* else if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
//      			runOnReturn(BB, RI);
//    		} else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(&I)) {
//      			runOnUnary(BB, UI);
//    		} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(&I)) {
//      			runOnBinary(BB, BI);
//    		} else if (ICmpInst *IC = dyn_cast<ICmpInst>(&I)) {
//      			runOnICmp(BB, IC);	
//    		} */
//	}
}

void pathCounter::evaluatePath(std::map< std::string, unsigned> *GbbMap, std::string funName, std::list<std::string> *traversedBB)
{
	auto &BB = M->getFunction(funName.c_str())->getEntryBlock();
	auto TermInst = BB.getTerminator();
	LocalBB = &BB;
	while(TermInst -> getNumSuccessors() != 0 )
	{
		processBBInstructions(GbbMap, traversedBB, funName);
		if(TermInst->getNumSuccessors() == 0){	// reached end of path
			std::cerr << "Terminating at " << LocalBB->getName().data() << std::endl;
			break;
		}else if(TermInst->getNumSuccessors() == 1){
			LocalBB = TermInst->getSuccessor(0);
			if(!LocalBB->hasName())
				continue;
			TermInst = TermInst->getSuccessor(0)->getTerminator();
			std::string str(funName);
			str+= LocalBB->getName().data();
			traversedBB->push_back(str);
		}else{
			unsigned max = 0;
			for(unsigned i = 0 ; i < TermInst->getNumSuccessors() ; i++){
				std::string nextBBName(funName);
				nextBBName+= std::string(TermInst->getSuccessor(i)->getName().data());
				if(GbbMap->find(nextBBName) == GbbMap->end()){
					std::cerr<< "Basic Block PP not found " << nextBBName << std::endl;	
					exit(0);
				}
				if((*GbbMap)[nextBBName] > max && (std::find(traversedBB->begin(), traversedBB->end(), nextBBName) == traversedBB->end())){
					std::cerr << "found " << nextBBName << " with weight " << (*GbbMap)[nextBBName] << std::endl;
					max = (*GbbMap)[nextBBName];
					LocalBB = TermInst->getSuccessor(i);
				//	if(!LocalBB->hasName())
				//		continue;
				}
			}
			if(max == 0){
				break;	
			}
			TermInst = LocalBB->getTerminator();
			std::string bbName(funName);
			bbName.append(LocalBB->getName().data());
			traversedBB->push_back(bbName);
		//	processBBInstructions(GbbMap);		
		}
	}
	processBBInstructions(GbbMap, traversedBB, funName); // for the terminal Basic Block
}

void pathCounter::runOnFunction()
{
	numVSets = 0;
	taintInstructions();
	runOnArgs();
	runOnInstructions();
//	auto count=0;
//	for(auto &ValTaintPair : (*TMap)){
//		std::cerr << count++ << "-->" << ValTaintPair.second << std::endl;
//	}
}

uint64_t pathCounter::assignTaint(Value *V)
{
	uint64_t integer;
	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)){
		if(CI->getBitWidth() <=32){
			integer = CI->getSExtValue();
			if(CMap->find(integer) == CMap->end()){
				//std::cerr << __func__ << "():Assigning int constant " << integer << " taint value " << taintNo << std::endl;
				std::cerr << "t" << taintNo << "=V(" << integer << ")" << std::endl;
				(*CMap)[integer] = taintNo++;
			}
			//std::cerr << __func__ << "():returning int constant " << integer << " taint value " << (*CMap)[integer] << std::endl;
			return (*CMap)[integer];
		}else{
			std::cerr << __func__ << "():Found Integer Type value with non 32 bit size" << std::endl;
		}
	}
	if(TMap->find(V) == TMap->end()){
		std::cerr << __func__ << "():Assigning new taint value " << taintNo << std::endl;
		(*TMap)[V]=taintNo++;
	}
	return (*TMap)[V];	
}

void pathCounter::assignTaint(Value *Dest, Value *Src)
{
	auto srcTaint = getTaint(Src);

	if(srcTaint == 0){
		assignTaint(Src);
	}
	//std::cerr << __func__ << "():assigning taint of source " << srcTaint << std::endl;
	(*TMap)[Dest] = srcTaint;
}

void pathCounter::taintInstructions()
{
	TMap = new std::map<Value *, uint64_t>;
	if(TMap == nullptr)
		std::cerr << __func__ << "null value allocated" << std::endl;

//	FTMapMap.insert(std::pair<Function *, std::map<Value *, uint64_t > *>(F, TMap));
	FTMapMap[F] = TMap;

	for (auto &B : *F) {
		for (auto &I : B) {
			(*TMap)[&I] =taintNo++;
		}
	}
	//std::cerr << __func__ << "(): completed Assigning taints to all instructions
	//		in function " << F->getName().data() << " total Taint Count " << taintNo-1 << std::endl;
}

void pathCounter::runOnArgs(void) {
	for (auto &A : F->args()){
		uint64_t TA = getTaint(&A);
		if (TA == 0) {
			(*TMap)[&A] = taintNo++; 
		}
	}
}

void pathCounter:: runOnInstructions(void)
{
	for (auto &B : *F) {
		for (auto &I : B) {
		/*if (LoadInst *LI = dyn_cast<LoadInst>(II.I)) {
			runOnLoad(LI); 
		} else */if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
			runOnStore(SI);
		} /*else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(II.I)) {
			runOnIntrinsic(II.B, MI);
		} else if (CallInst *CI = dyn_cast<CallInst>(II.I)) {
			runOnCall(II.B, CI);
		} else if (ReturnInst *RI = dyn_cast<ReturnInst>(II.I)) {
			runOnReturn(II.B, RI);
		} else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(II.I)) {
			runOnUnary(II.B, UI);
		} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(II.I)) {
			runOnBinary(II.B, BI);
		} else if (ICmpInst *IC = dyn_cast<ICmpInst>(II.I)) {
			runOnICmp(II.B, IC);
		}*/
		}
	}
}

void pathCounter:: cleanup()
{ 
	IIs.clear();
	VSets.clear();
	VtoVSet.clear();
	IdxToVar.clear();
}

void pathCounter::instrumentModule(Module *M_)
{
	// initialization stuff
        M = M_;
        C = &(M->getContext());
        DL = M->getDataLayout();
        IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
        VoidTy = Type::getVoidTy(*C);
        VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));

	for (auto &F_ : M->functions()) {
		F = &F_;
		//if (F->isDeclaration()) {
		//	if (F->getName() == "memset") {
		//		F->setName("__fslice_memset");
		//	} else if (F->getName() == "memcpy") {
		//		F->setName("__fslice_memcpy");
		//	} else if (F->getName() == "memmove") {
		//		F->setName("__fslice_memmove");
		//	} else if (F->getName() == "strcpy") {
		//		F->setName("__fslice_strcpy");
		//	} else if (F->getName() == "bzero") {
		//		F->setName("__fslice_bzero");
		//	} else if (F->getName() == "malloc") {
		//		F->setName("__fslice_malloc");
		//	} else if (F->getName() == "calloc") {
		//		F->setName("__fslice_calloc");
		//	} else if (F->getName() == "mark") {
		//		F->setName("__fslice_mark");
		//	} else if (F->getName() == "strlen") {
		//		F->setName("__fslice_strlen");
		//		//      printFunctionName(F->getName().data());
		//	}
		//} else {
		if (!F->isDeclaration()) 
			runOnFunction();
		//}
	}
}

bool pathCounter::runOnModule(Module &M_) {
	CMap = new std::map<uint64_t , uint64_t>;
	std::map< std::string, unsigned> GbbMap;
	// instrument the code for tainting
	instrumentModule(&M_);
	
//	// get different possible paths from each basic block.
//	getModuleLevelPP(&GbbMap);
//
//	// get path constraints for each path.
//	std::cerr << "EVALUATE PATH" << std::endl;
//	std::list <std::string> traversedBB;
//	evaluatePath(&GbbMap, std::string("main"), &traversedBB);
//
//	// process path constraints and get input values
//
//	// cleanup
        return true;
}

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

void pathCounter:: Store(uint64_t addr, uint64_t size, Taint t) {
//  for (auto i = 0U; i < size; ++i) {
//    auto &et = gShadow[addr + i];
//    if (et.is_obj) {
//      std::cerr << "t" << et.id << "[" << et.offset << "]=t" << t.id
//                << "[" << (t.offset + i) << "] # Store::is_obj equals true."
//                << std::endl;
//    } else {
//      	  et = {t.id, t.offset + i , false}; // should be `taint.offset + i`?
//    }
//  }
}

// Returns the size of a loaded/stored object.
uint64_t pathCounter:: LoadStoreSize(const DataLayout *DL, Value *P) {
	PointerType *PT = dyn_cast<PointerType>(P->getType());
	return DL->getTypeStoreSize(PT->getElementType());
}

/* VtoVSet only contains original instructions and orginal arguments,
 * It does not containt instructions and arguments that were added to the 
 * Code base during the tainting. So, we check first the VtoVSet if the
 * AllocaInst instruction (V) is one of the VtoVSet instructions. If yes,
 * We return IdxToVar instruction. If not, it is one of the tainted
 * allocainst instructions, which we find from IdxToVar */

/* IdxToVar most probably does not contain any other operands other than
 * the Instructions and arguments of the program, already covered in
 * VtoVSet. So the "else" part in getTaint may be unnecessary.*/

/* If we do not find a taint value in VtoVSet, it is most probably an 
 * integer constant.*/

uint64_t pathCounter::getTaint(Value *V) {
  if (V->getType()->isFPOrFPVectorTy()) return 0;
	if(TMap->find(V) == TMap->end()){
		return 0;
	}else{
		return (*TMap)[V];
	}
}

// Get a value that contains the tainted data for a local variable, or zero if
// the variable isn't tainted.

Value *pathCounter::LoadTaint(Instruction *I, Value *V) {
//  auto &IList = I->getParent()->getInstList();
//  Instruction *RV = nullptr;
//  if (auto TV = getTaint(V)) {
//    RV = new LoadInst(TV);
//  } else {
//    if (IntegerType *IT = dyn_cast<IntegerType>(V->getType())) {
//      Instruction *CV = nullptr;
//      if (IT->isIntegerTy(IntPtrTy->getPrimitiveSizeInBits())) {
//        CV = CastInst::CreateBitOrPointerCast(V, IntPtrTy);
//      } else {
//        CV = CastInst::Create(Instruction::ZExt, V, IntPtrTy);
//      }
//      IList.insert(I, CV);
//      auto ValueFunc = CreateFunc(IntPtrTy, "__fslice_value", "",
//                                  IntPtrTy);
//      RV = CallInst::Create(ValueFunc, {CV});
//    } else {
//      return ConstantInt::get(IntPtrTy, 0, false);
//    }
//  }
//  IList.insert(I, RV);
//  return RV;
	return nullptr;
}

// Instrument a single instruction.
void pathCounter::runOnStore(StoreInst *SI) {
	// store taint of Value, to taint of PointerAddress
	// get Taint of Value, get taint of Pointer Address
	// store Value of Pointer address, taint of Value
	//std::cerr << __func__ << "():" << std::endl;

	auto V = SI->getValueOperand();
	auto P = SI->getPointerOperand();
	assignTaint(P, V);
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


//void pathCounter::runOnUnary(BasicBlock *B, UnaryInstruction *I) {
//	//auto Op = CreateString(I->getOpcodeName());	
//	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
//		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
//	}
//	std::cerr  << B->getName().data() << " Unary Operand " << I->getOpcodeName() << " " << taintMap[(uint64_t)I->getOperand(0)] << std::endl;
//}
//
//void pathCounter::runOnBinary(BasicBlock *B, BinaryOperator *I) {
//	//auto Op = CreateString(I->getOpcodeName());	
//	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
//		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
//	}
//	if(taintMap.find((uint64_t)I->getOperand(1)) == taintMap.end()){
//		taintMap[(uint64_t)I->getOperand(1)] = taintVal++;
//	}
//	std::cerr  << B->getName().data()<< "Binary Operand " << I->getOpcodeName() << " Op1 = " << taintMap[(uint64_t)I->getOperand(0)] << " Op2 = " << taintMap[(uint64_t)I->getOperand(1)] << std::endl;
//}
//
//void pathCounter::runOnICmp(BasicBlock *B, ICmpInst *I) {
//	if(taintMap.find((uint64_t)I->getOperand(0)) == taintMap.end()){
//		taintMap[(uint64_t)I->getOperand(0)] = taintVal++;
//	}
//	if(taintMap.find((uint64_t)I->getOperand(1)) == taintMap.end()){
//		taintMap[(uint64_t)I->getOperand(1)] = taintVal++;
//	}
//	auto Pred = I->getUnsignedPredicate();
//	std::cerr  << B->getName().data()<< "Predicate " << Pred << "LO = " << taintMap[(uint64_t)I->getOperand(0)] << " RO = " << taintMap[(uint64_t)I-> getOperand(1)] << std::endl;
//}
//
//void pathCounter::runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI) {
//  const char *FName = nullptr;
//  auto CastOp = Instruction::PtrToInt;
//  if (isa<MemSetInst>(MI)) {
//    CastOp = Instruction::ZExt;
//    FName = "__fslice_memset";
//  } else if (isa<MemCpyInst>(MI)) {
//    FName = "__fslice_memcpy";
//  } else if (isa<MemMoveInst>(MI)) {
//    FName = "__fslice_memmove";
//  } else {
//    return;
//  }
//
//  auto &IList = B->getInstList();
//  auto MemF = CreateFunc(VoidPtrTy, FName, "", IntPtrTy, IntPtrTy, IntPtrTy);
//  auto MDest = CastInst::CreatePointerCast(MI->getRawDest(), IntPtrTy);
//  IList.insert(MI, MDest);
//
//  auto Src = CastInst::Create(CastOp, MI->getArgOperand(1), IntPtrTy);
//  IList.insert(MI, Src);
//
//  std::vector<Value *> args = {MDest, Src, MI->getLength()};
//  IList.insert(MI, CallInst::Create(MemF, args));
//
//  MI->eraseFromParent();
//}
//
char pathCounter::ID = '\0';
unsigned int pathCounter ::taintVal= 0;

static RegisterPass<pathCounter> X(
    "pathCounter",
    "pathCounter",
    false,  // Only looks at CFG.
    false);  // Analysis Pass.
