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
#include <algorithm>
#include <map>
#include <vector>
#include <list>
#include <string>
#include <stack>
#include "sym.h"
#include <queue>
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

std::map<int , const char *> Predicate {
  // Opcode        
{   0, "FCMP_FALSE"}, 
{   1, "FCMP_OEQ"  }, 
{   2, "FCMP_OGT"  }, 
{   3, "FCMP_OGE"  }, 
{   4, "FCMP_OLT"  }, 
{   5, "FCMP_OLE"  }, 
{   6, "FCMP_ONE"  }, 
{   7, "FCMP_ORD"  }, 
{   8, "FCMP_UNO"  }, 
{   9, "FCMP_UEQ"  }, 
{  10, "FCMP_UGT"  }, 
{  11, "FCMP_UGE"  }, 
{  12, "FCMP_ULT"  }, 
{  13, "FCMP_ULE"  }, 
{  14, "FCMP_UNE"  }, 
{  15, "FCMP_TRUE" }, 
{  32, "ICMP_EQ"  } , 
{  33, "ICMP_NE"  } , 
{  34, "ICMP_UGT" } , 
{  35, "ICMP_UGE" } , 
{  36, "ICMP_ULT" } , 
{  37, "ICMP_ULE" } , 
{  38, "ICMP_SGT" } , 
{  39, "ICMP_SGE" } , 
{  40, "ICMP_SLT" } , 
{  41, "ICMP_SLE" } , 
};

// Priority Queue Scheduler
class pathPotentialTuple
{
public: 
	pathPotentialTuple(std::string s, uint64_t pp):path(s), pathPotential(pp){}
        std::string path;
        uint64_t pathPotential;
};

class Compare
{
        public:
        bool operator() (pathPotentialTuple p1, pathPotentialTuple p2){
                if(p1.pathPotential < p2.pathPotential)
                  return true;
                return false;
        }
};

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
  void runOnLoad(LoadInst *LI);
  void runOnStore(StoreInst *SI);
  void runOnBranch(BranchInst *BI);
  void runOnCall(CallInst *CI);
  void markVariable(CallInst *CI);
  void runOnReturn(ReturnInst *RI);
  void runOnUnary(UnaryInstruction *I);
  void runOnCast(CastInst *I);
  void addMarkerTaint();
  bool hasFunctionCall(BasicBlock *BB);
  void runOnBinary(BinaryOperator *I);
	void runOnICmp(ICmpInst *I);
  void getFunctionPPWithoutCalls();
	void cleanup();
	void taintBasicBlocks(Module *M);


	void Store(uint64_t addr, uint64_t size, Taint t);
	
  void getModuleLevelPP( std::map <std::string, unsigned> *GbbMap);
	//std::map <uint64_t, uint64_t> taintMap;
	bool markedProcessed();
	bool processedFunctionCaller();
	void analyseFunctionCalls();
// 	void runOnIntrinsic(MemIntrinsic *MI);
	void runOnInstructions(BasicBlock *B);
  int getFunctionPP(std::stack <const char*> *FStack, std::map<std::string, unsigned> *GbbMap);
	//void processBlock(BasicBlock *BB);
	std::vector<const char *> processedBlocks;
  int getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map<std::string, unsigned> *GbbMap);
	void processDFS(BasicBlock *B, std::stack <BasicBlock *> *BBStack);
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
	const char * isLoopBack(BasicBlock * currentBB);
	bool isLoopBackBB(const char *currentBB);
	bool inStack(const char *element, std::stack<const char *> *bbStack);
	const char * getAlternatePath(const char *currentBB, std::stack <const char *> *bbStack);
	BasicBlock * getAlternatePath(BasicBlock *ForLoopBlock, std::stack <const char *> *bbStack);
	BasicBlock * getAlternatePath(BasicBlock *ForLoopBlock, std::stack <BasicBlock *> *bbStack);
	BasicBlock*  getAlternateBB(BasicBlock *parentBB, const char *loopBackBBName);
	bool isTerminalFunction();
	void getTerminalFunctions();
	void processBBInstructions(std::map <std::string, unsigned> *GbbMap, std::list <std::string > *traversedBB, std::string funName);
	void evaluatePath(std::map<std::string, unsigned > *GbbMap, std::string funName, std::list <std::string> *traversedList);
	void enumeratePaths(std::map<std::string, unsigned > *GbbMap, BasicBlock *BB);

	void __fslice_store (uint64_t size, Value  *addr , Value *taint);
	void printFunCallFromBB(const char *bbName);
	uint64_t queryPP(BasicBlock *BB, std::map<std::string, unsigned> *GbbMap);
  void track(Value *V);
  int marked(Value *V);

  uint64_t getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	// stores loopBack Basic Block and its successor basic block that creates
	// the loop
	std::map<BasicBlock *, BasicBlock *> loopBackBBs;

	std::map<BasicBlock *, int> *CFMap = new std::map <BasicBlock *, int>;
	std::map<BasicBlock *, int> *PPMap = new std::map <BasicBlock *, int>;
	std::map<const char *, int> functionPPMap;
  	std::vector <Value *> trackTaint;
	// map of functions and pointer to map of (BB,ConvergenceFactor)
	// for each BB in that function.
	std::map <const char *, void *> functionConvergenceFactorMap;
	void taintInstructions();

	void calculateLoopFactor(Module *M);
	void detectLoop(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack);

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
  BasicBlock *BBLocal;
  Module *M;
  LLVMContext *C;
  const DataLayout *DL;

  Type *IntPtrTy;
  Type *VoidTy;
  Type *VoidPtrTy;
  Instruction *AfterAlloca;// first instruction in a function.
			   // this instruction is always entry

  BasicBlock *LocalBB;
  BasicBlock *entryBB;
  std::vector<IInfo> IIs;
  std::vector<VSet> VSets;
  std::map<Value *,VSet *> VtoVSet;
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
// marks <value, symbolic type> [0,1,2 for INT, STR, VAR_ARRAY]
  std::map<Value *, uint64_t> markerTypeMap;
// created for every function. stores "value" of each operator
// and operand and corresponding taint number
  std::map <Value *, uint64_t > * TMap;
// Map of all constant values being referred.
  std::map <uint64_t, uint64_t> * CMap; 
  int numVSets;
  uint64_t taintNo;
// Scheduler
	std::priority_queue<pathPotentialTuple, std::vector<pathPotentialTuple>, Compare> Scheduler;
	bool isSolvable();
	bool isSolvable(BasicBlock *);
	void updatePathContext(BasicBlock *currentBB);
	BasicBlock* getNextMaxBB(BasicBlock *currentBB, std::map<std::string, unsigned > *GbbMap);
	void  getModel();
	BasicBlock* loadContext();
	void saveContext (BasicBlock *currentBB, std::map<std::string, unsigned > *GbbMap);
	std::string pathContext;
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
			funNameBB += ":";
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
			funNameBB += ":";
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
				funNameBB += ":";
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
					funNameBB += ":";
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
				funNameBB += ":";
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
			}else{
				bbMap->insert(std::pair<const char *, int>(bbName, currentBB_PP));
				std::string funNameBB(FStack->top());
				funNameBB += ":";
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
		std::cerr << it->first << " " << it->second << std::endl;
	}
}

const char* pathCounter :: isLoopBack(BasicBlock *BB)	// finds loopback in pathCounter
{
	auto BBName = BB->getName().data();
	std::string s(pathContext);
        std::string funDelimiter(":");
        std::string bbDelimiter("-");
        std::string bb;
        while(std::count(s.begin(), s.end(), '-')>1){
                std::cerr << "s = " << s << std::endl;
                auto bbIndex = s.find(bbDelimiter);
                auto funIndex = (s.find(funDelimiter) == std::string::npos) ? s.length() : s.find(funDelimiter);
                std::cerr << "funIndex = " <<funIndex << " bbIndex = " << bbIndex << std::endl;
                bb = s.substr(bbIndex + 1, funIndex - bbIndex -1);
                if(!bb.compare(BBName)){
			s = s.substr(funIndex + 1, s.length());
                        bbIndex = s.find(bbDelimiter);
                        funIndex = s.find(funDelimiter);
			auto nextBB = s.substr(bbIndex + 1, funIndex - bbIndex - 1); 
                	return nextBB.c_str();
                }else{  
                        std::cerr << "bb=" << bb << " BBName" << BBName << std::endl;
                }
                if(s.find(funDelimiter) != std::string::npos){
                        s= s.substr(funIndex+1, s.length());
                }else{  
                        s.clear();
                }
        }
	return nullptr;
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

BasicBlock * pathCounter:: getAlternatePath( BasicBlock *LoopBlock, std::stack <BasicBlock *> *bbStack)
{
	std::stack <BasicBlock *> temp;
	BasicBlock *prev;
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
		if(!strcmp(top->getName().data(),LoopBlockName)){
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
		if(strcmp(TermInst->getSuccessor(i)->getName().data(),prev->getName().data()) != 0){	// not equal
			D(std::cerr << __func__ << "(): returning alternate path " << TermInst->getSuccessor(i) << std::endl;)
			return TermInst->getSuccessor(i);
		}else{
			prevBB = TermInst->getSuccessor(i);
		}
	}
	
	D(std::cerr << LoopBlock->getName().data() << "returning previous path " << prevBB->getName().data() << std::endl;)
	return prevBB;
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

/**
 *  go through all basic blocks in function in depth first order and assign all operands 
 *  appropriate taints when loop is detected, send all loop related basic blocks to loop 
 *  detector logic where iterators will be identified, iterator incrementor will be 
 *  determined additional constraints will be added.
 * **/
void pathCounter::runOnFunction()
{
	taintInstructions();
	runOnArgs();

	std::cerr << F->getName().data() << std::endl;
	BBLocal = &(F->getEntryBlock());
	std::stack <BasicBlock *> BBStack; 
	assert(BBLocal != nullptr);
	BBStack.push(BBLocal);
	processDFS(BBLocal, &BBStack);
	BBStack.pop();

}

uint64_t pathCounter::assignTaint(Value *V)
{
	uint64_t integer;
	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)){
		if(CI->getBitWidth() <=64){
			integer = CI->getZExtValue();
			if(CMap->find(integer) == CMap->end()){
				//std::cerr << __func__ << "():Assigning int constant " << integer << " taint value " << taintNo << std::endl;
				std::cerr << "t" << taintNo << "=V(" << integer << ")" << std::endl;
				(*CMap)[integer] = taintNo++;
			}
			D(std::cerr << "integer value " << integer << " has taint " << (*CMap)[integer];)
			//std::cerr << __func__ << "():returning int constant " << integer << " taint value " << (*CMap)[integer] << std::endl;
			return (*CMap)[integer];
		}else{
			std::cerr << __func__ << "():Found Integer Type value with non 64 bit size" << std::endl;
		}
	}
	if(TMap->find(V) == TMap->end()){
		D(std::cerr << __func__ << "():Assigning new taint value " << taintNo << std::endl;)
		(*TMap)[V]=taintNo++;
	}	
	return (*TMap)[V];	
}

void pathCounter::assignTaint(Value *Dest, Value *Src)
{
	auto srcTaint = getTaint(Src);
	if(srcTaint == 0){
		srcTaint = assignTaint(Src);
	}
	D(std::cerr << __func__ << "():assigning taint of source " << srcTaint << std::endl;)
	std::cerr << "t" << (*TMap)[Dest] << "=t" << srcTaint << std::endl;
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

void pathCounter:: runOnInstructions(BasicBlock *B)
{
	for (auto I = B->begin(); I != B->end() ; I++) {
		if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
			runOnLoad(LI); 
		} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
			runOnStore(SI);
		} else if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
			runOnBranch(BI);
		} /*else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I)) {
			runOnIntrinsic(MI);
		}*/ else if (CallInst *CI = dyn_cast<CallInst>(I)) {
			runOnCall(CI);
		} else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
			runOnReturn(RI);
		} else if (CastInst *CI = dyn_cast<CastInst>(I)) {
			runOnCast(CI);
		} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(I)) {
			runOnBinary(BI);
		}
		else if (ICmpInst *IC = dyn_cast<ICmpInst>(I)) {
			runOnICmp(IC);
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

void pathCounter::taintBasicBlocks(Module *M_)
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
		if (!F->isDeclaration()) 
			runOnFunction();
	}
}

// detect loop entry blocks in a program. add the pair
// <entry_block: successor_loop_block> to loopBackBBs

void pathCounter::detectLoop(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack)
{
	int numSuccessors = currentBB->getTerminator()->getNumSuccessors();
	if(!isLoopBack(currentBB, bbStack)){
		bbStack->push(currentBB);
		for(auto succ = 0 ;  succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			detectLoop(BB, bbStack);			
		}
		bbStack->pop();	
	}else{
		std::cerr << "detected " << currentBB->getName().data() << " as loopback BB" << std::endl;
		// check which successor block is the loopback block
		for(auto succ =0 ; succ < numSuccessors ; succ++){
			auto BB = currentBB->getTerminator()->getSuccessor(succ);
			if(isLoopBack(BB, bbStack)){
				std::cerr << currentBB->getName().data() << "->" << BB->getName().data() << std::endl;
				loopBackBBs[currentBB] = BB;
				return;
			}
		}
		assert(0);
	}
}

// scan through loop entry bb. get comparator taints.
// go recursively through all bbs from the child bb of
// loop entry bb that leads to a loop. explore path till
// you reach the loop entry bb.
//
//void pathCounter::getLoopDependentTaints()
//{
//	// contains entire functions loopBlock Taints
//	std::vector<uint64_t> loopTaints ;
//
//	for(auto &loopBackBBPair : loopBackBBs)	{
//		// first, get the loop back bb, get comparator instruction
//		// get taint of iterator.
//			
//		auto loopBackBB = loopBackBBPair.first;
//		auto childBB = loopBackBBPair.second;
//							
//		int iteratorTaint = getIteratorTaint(loopBackBB);
//		// call recursive block processing instruction that will
//		// go through each successor block until loopback block
//		// is reached again.
//
//		getloopVariables(childBB, loopTaints);
//	}
//	
//	// for each bb, check if any operation involves loop 
//	// iterator variable. keep track of these taint values
//	
//}
//
//void pathCounter::scanLoopDependentBranch()
//{
//}
//
//void pathCounter::calculateLoopFactor(Module *M)
//{
//	// detect loops. detect loop condition.
//	for (auto &F_ : M->functions()) {
//		F = &F_;
//		if (!F->isDeclaration()) {
//			entryBB = &(F->getEntryBlock());
//			auto currentBB = entryBB;
//			std::stack <BasicBlock *> bbStack;
//			detectLoop(currentBB, &bbStack);
//			// find all dependent taints on loop.
//			auto loopDependentTaints = getLoopDependentTaints();
//			// determine if there are any branch conditions
//			// that depend on loop.
//			/*
//			auto loopFactor = scanLoopDependentBranch();
//			// keep track of loopFactor for loop
//			//addBBLoopFactor();
//			*/
//		}
//	}
//}

// lists all paths/ subpaths as strings.

bool pathCounter::hasFunctionCall(BasicBlock *BB)
{
	for(auto &I : *BB){
		if(dyn_cast<CallInst>(&I))
			return true;
	}
	return false;
}

uint64_t pathCounter :: queryPP(BasicBlock *BB, std::map<std::string, unsigned> *GbbMap)
{
	auto currentBBName = BB->getName().data();
	auto functionName = BB->getParent()->getName().data();
	std::string s(functionName);
	s += ":";
	s += currentBBName;
//	std::cerr << "returning path potential of " << s.c_str() << (*GbbMap)[s] << std::endl;
	assert(GbbMap->find(s) != GbbMap->end());
	return (*GbbMap)[s];
}

bool pathCounter::isSolvable()
{
	assert(!pathContext.empty());
	std::cerr << __func__ << "():"<< pathContext << std::endl;
	return true;
}

bool pathCounter::isSolvable(BasicBlock *nextBB)
{
	std::string oldPathContext(pathContext);
	pathContext += "-";
	pathContext += nextBB->getParent()->getName().data();
	pathContext += ":";
	pathContext += nextBB->getName().data();
	bool result = isSolvable();
	pathContext.clear();
	pathContext = oldPathContext;
	return result;
}

void pathCounter :: updatePathContext(BasicBlock *currentBB){
	pathContext += ":";
	pathContext += currentBB->getParent()->getName().data();
	pathContext += "-";
	pathContext += currentBB->getName().data();
}

// saves current pathContext + currentBB.getName() to scheduler
void pathCounter:: saveContext (BasicBlock *currentBB, std::map<std::string, unsigned > *GbbMap){
	std::cerr << __func__ << "():current BB is " << currentBB->getName().data() << std::endl;
	auto currentBBPP = queryPP(currentBB, GbbMap);
	auto pathToSave = pathContext + "-";
	pathToSave += currentBB->getParent()->getName().data();
	pathToSave += ":";
	pathToSave += currentBB->getName().data();
	D(std::cerr << __func__ << "():saved path " << pathToSave << " path Potential " << currentBBPP << std::endl;)
	pathPotentialTuple p(pathToSave,currentBBPP);
	Scheduler.push(	p);
}

// return child BB with minimum PP
BasicBlock* pathCounter:: getAlternateBB(BasicBlock *parentBB, const char *loopBackBlock){
	for(unsigned i = 0 ; i < parentBB->getTerminator()->getNumSuccessors(); i++){
		if(strcmp(loopBackBlock,parentBB->getTerminator()->getSuccessor(i)->getName().data())){
			return parentBB->getTerminator()->getSuccessor(i);
		}
	}
	assert(0);
}

// choose between saved contexts and child basic blocks
// DO: add to path context before returning a basic block, if new basic block is detected

BasicBlock* pathCounter::getNextMaxBB(BasicBlock *currentBB, std::map<std::string, unsigned > *GbbMap)
{
	BasicBlock *maxChildBB = currentBB->getTerminator()->getSuccessor(0);
	uint64_t maxChildBBPP = queryPP(maxChildBB, GbbMap);
	unsigned numSuccessors = currentBB->getTerminator()-> getNumSuccessors();
	uint64_t schedulerMaxPP = 0;
	if(!Scheduler.empty()){
		schedulerMaxPP = Scheduler.top().pathPotential;
		D(std::cout << __func__ << "():picked up scheduler element " << Scheduler.top().path << std::endl;)
	}else{
		D(std::cerr << __func__ << "():scheduler is empty " << std::endl;)
	}

	const char* alternateBBName = isLoopBack(currentBB);
	if(alternateBBName != nullptr){
		std::cerr << __func__ << "(): LOOP DETECTED " << std::endl;
		std::cerr << __func__ << "(): return block with less PP " << std::endl;
		auto alternateBB = getAlternateBB(currentBB, alternateBBName);
		std::cerr << __func__ << "(): block returned " << alternateBB->getName().data() << std::endl;
		updatePathContext(alternateBB);
		return alternateBB;
	}

	// choose max child, save state of other children
	for(unsigned i=1; i < numSuccessors ; i++){
		BasicBlock* nextChildBB = currentBB->getTerminator()->getSuccessor(i);
		uint64_t nextChildBBPP = queryPP(nextChildBB, GbbMap);
		if(nextChildBBPP > maxChildBBPP ){ // save less PP context
			D(std::cerr << __func__ << "():saving max child " << maxChildBB->getName().data() << std::endl;)
			if(isSolvable(maxChildBB)){
				saveContext(maxChildBB, GbbMap);
			}
			maxChildBB = nextChildBB;
			maxChildBBPP = nextChildBBPP;
		}else{
			D(std::cerr << __func__ << "():saving next child " << nextChildBB->getName().data() << std::endl;)
			if(isSolvable(nextChildBB)){
				saveContext(nextChildBB, GbbMap);
			}
		}
	}
	D(std::cerr << __func__ << "():child having max path potential " << maxChildBB->getName().data() << std::endl;)
	D(std::cerr << __func__ << "(): path Context " <<pathContext << std::endl;)
	D(std::cerr << __func__ << "(): max Child " << maxChildBB->getName().data() << std::endl; )
	// if max child is greater than scheduler max, or scheduler is empty,
	// continue. else save max child, load scheduler top

	if(maxChildBBPP < schedulerMaxPP){
		assert(schedulerMaxPP > 0);
		D(std::cerr << __func__ << "():picked scheduler top context " << Scheduler.top().path << std::endl;)
		D(std::cerr << __func__ << "():saved current Context " << pathContext << std::endl;)
		if(isSolvable(maxChildBB)){
			saveContext(maxChildBB, GbbMap);
		}
		std::cerr << __func__ << "():loaded new context " << std::endl;
		maxChildBB = loadContext();
		std::cerr << __func__ << "context path " << pathContext << std::endl;
	}else{
		D(std::cerr << __func__ << "():no update from scheduler " << currentBB->getName().data() << std::endl;)
		updatePathContext(maxChildBB);
	}
	D(std::cerr << __func__ << "(): path Context " << pathContext << std::endl;)
	D(std::cerr << __func__ << "(): max Child " << maxChildBB->getName().data() << std::endl;)
	return maxChildBB;
}

void pathCounter :: getModel()
{
	std::cerr << ">>>:::GETMODEL:::<<<" << std::endl;
	isSolvable();
}

BasicBlock* pathCounter :: loadContext()
{
	unsigned prevSize = Scheduler.size();
	D(std::cerr << __func__ << "(): Scheduler Size " << Scheduler.size() << std::endl; )
	if(Scheduler.empty()){
		D(std::cerr << __func__ << "(): Scheduler is empty, returning " << std::endl;)
		return nullptr;
	}else{
		auto nextContext = Scheduler.top();
		Scheduler.pop();
		pathContext = nextContext.path;
		// context saved as f1:bb1-f1:bb2-f2:bb1
	
		std::string bbDelimiter = "-";
	        std::string funDelimiter = ":";
	        int lastIndex;
	        std::string lastBB(pathContext);
	        while(lastBB.find(bbDelimiter)!=std::string::npos){
	                lastIndex = lastBB.find(bbDelimiter);
	                lastBB = lastBB.substr(lastIndex+1, lastBB.length());
	        }
	        lastIndex = lastBB.find(funDelimiter);
	        std::string lastFunName = lastBB.substr(0, lastIndex);
	        lastBB = lastBB.substr(lastIndex+1, lastBB.length());
		
		D(std::cerr << __func__ << "():loading path " << pathContext << std::endl;
		std::cerr<< __func__ << "():last Basic Block received " << lastBB << std::endl;
		std::cerr << __func__ << "():last function name " << lastFunName << std::endl;)

		assert(Scheduler.size() == prevSize - 1);	// should have removed 1 element

		F = M->getFunction(lastFunName);
		for(auto &BB : *F){
			if(!strcmp(BB.getName().data(), lastBB.c_str())){
				return &BB;
			}
		}
	}
	assert(0);	// should get last basic Block from function.
	return nullptr;
}

/* List out all paths in path potential first manner.
 * A context is a tuple with string path and a path potential.
 * We save stuff on a Scheduler only if it isSolvable()
 * */

void pathCounter::enumeratePaths(std::map<std::string, unsigned > *GbbMap, BasicBlock *currentBB)
{
	unsigned numSuccessors = currentBB->getTerminator()-> getNumSuccessors();
	if(!hasFunctionCall(currentBB)){
		if(numSuccessors == 0){
			D(std::cerr <<__func__ << "():reached terminal path " << pathContext << std::endl;)
			getModel(); // reach terminal block GENERATE TESTCASE
			currentBB = loadContext();
			if(currentBB == nullptr){
				std::cerr << "TESTING COMPLETE" << std::endl;
				return;
			}else{		// Scheduler has unexplored paths in Queue
				D(std::cerr << __func__ << "():new context loaded " << pathContext << std::endl;
				std::cerr << __func__ << "():new currentBB = " << currentBB->getName().data() << std::endl;)
				enumeratePaths(GbbMap, currentBB);
			}
		}else if(numSuccessors == 1){
			currentBB = currentBB->getTerminator()->getSuccessor(0);
			updatePathContext(currentBB);
			D(std::cerr << __func__ << "():only 1 child, extend only 1 path" << std::endl;)
			if(isSolvable()) // move to child basic block
				enumeratePaths(GbbMap, currentBB);
		}else{	// choose max among child Basic Blocks or saved contexts
			D(std::cerr << __func__ << "():num successors > 1, current path " << pathContext << std::endl;)
			currentBB = getNextMaxBB(currentBB,GbbMap);
			D(std::cerr << __func__ << "():path Context " << pathContext << std::endl;
			std::cerr << __func__ << "():currentBB " << currentBB->getName().data() << std::endl;)
			if(isSolvable())
				enumeratePaths(GbbMap, currentBB);
		}
	}
}

bool pathCounter::runOnModule(Module &M_) {
	CMap = new std::map<uint64_t , uint64_t>;
	std::map< std::string, unsigned> GbbMap;
	// instrument the code for tainting
	taintBasicBlocks(&M_);
	
	// get different possible paths from each basic block.
	getModuleLevelPP(&GbbMap);
//	printGbbMap(&GbbMap);

	auto mainF = M->getFunction("main");
	assert(mainF !=nullptr);
	BBLocal = &(mainF->getEntryBlock());
	pathContext += "main-entry";
	std::cerr<< "START ENUMERATION" << std::endl;
	enumeratePaths(&GbbMap, BBLocal);
		
//	// process path constraints and get input values

//	// cleanup
        return true;
}

/*print all paths in DFS order*/

void pathCounter :: processDFS(BasicBlock *B, std::stack<BasicBlock *> *BBStack)
{
	if(B->getTerminator()->getNumSuccessors() == 0){
		//BBStack->push(B);
		//printStack(BBStack);
		std::cerr << "PROCESSING BB " << B->getName().data() << std::endl;
		runOnInstructions(B);
		//BBStack->pop();
		return ;
	}else {
		if(isLoopBack(B, BBStack)){
			return;
		}else{
			std::cerr << "PROCESSING BB " << B->getName().data() << std::endl;
			runOnInstructions(B);
			for(unsigned int i = 0 ; i < B->getTerminator()->getNumSuccessors() ; i++){
				BBStack->push(B->getTerminator()->getSuccessor(i));
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
	if(TMap->find(V) != TMap->end()){
		return (*TMap)[V];
	}
	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)){
		if(CI->getBitWidth() <=64){
			auto integer = CI->getZExtValue();
			if(CMap->find(integer) != CMap->end()){
				return (*CMap)[integer];
			}
		}
	}		
	return 0;
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

	auto V = SI->getValueOperand();
	auto P = SI->getPointerOperand();
	assignTaint(P, V);
}

void pathCounter::markVariable(CallInst *CI){
	enum symType markerType = UNDEFINED;	// see sym.h
	if(ConstantInt *I = dyn_cast<ConstantInt>(CI->getArgOperand(0))){
		if (I->getBitWidth() <= 64) {
			markerType = (enum symType)I->getZExtValue();
		}else{
			std::cerr << "ERROR: Value GT 64 bit detected" << std::endl;
		}
	}
	auto markedValue = CI->getArgOperand(1);
	uint64_t markedTaintValue;	

	if(TMap->find(markedValue) != TMap->end()){
		markedTaintValue = (*TMap)[markedValue];
	}else{
		markedTaintValue = taintNo++;
		(*TMap)[markedValue] = markedTaintValue;
	}
	markerTypeMap[markedValue] = markerType;

	switch(markerType){
		case INT:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(INT)" << std::endl;
			break;
		case CONSTANT_STR:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(CONSTANT_STR)" << std::endl;
			break;
		case VARIABLE_STR:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(VARIABLE_STR)" << std::endl;
			break;
		case CONSTANT_INT_ARRAY:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(CONSTANT_INT_ARRAY)" << std::endl;
			break;
		case CONSTANT_STRING_ARRAY:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(CONSTANT_STRING_ARRAY)" << std::endl;
			break;
		case VARIABLE_INT_ARRAY:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(VARIABLE_INT_ARRAY)" << std::endl;
			break;
		case VARIABLE_STRING_ARRAY:
			std::cerr << "t" << (*TMap)[markedValue] << "=" << "MARK(VARIABLE_STRING_ARRAY)" << std::endl;
			break;
		default:
			std::cerr << "ERROR! Unknown Mark TYPE!" << std::endl;
			assert(0);	
	}
}

void pathCounter::runOnCall(CallInst *CI) {
	if(CI !=nullptr && CI->getCalledFunction() != nullptr && (CI->getCalledFunction()->hasName())){
		if(!strcmp(CI->getCalledFunction()->getName().data(), "_mark")){
			markVariable(CI);
		}else{
			// assign all arguments taint values
			auto numArgs = CI->getNumArgOperands();
			for(unsigned i = 0 ; i < numArgs ; i++){
				auto argi = CI->getArgOperand(i);
				auto taint_argi = getTaint(argi);
				if(taint_argi == 0){
					taint_argi = assignTaint(argi);
				}
				std::cerr << CI->getCalledFunction()->getName().data() << ".arg" << i << "=t" << taint_argi  << std::endl;
			}
			// assign return value taints
			auto retTaint = getTaint(CI);
			assert(retTaint);
			std::cerr << CI->getCalledFunction()->getName().data() << ".ret=t" << retTaint << std::endl;
		}
	}
}

void pathCounter::runOnBranch(BranchInst *BI) {
	int numSuccessors = BI->getNumSuccessors();
	if(BI->isConditional()){
		auto cond = BI->getCondition();
		auto condTaint = getTaint(cond);
		if(condTaint == 0){
			condTaint = assignTaint(cond);
		}
		std::cerr << "BRANCH_COND " << " " << "t" << condTaint << " ( " ;
		for(auto i = 0; i < numSuccessors ; i++){
			auto bbName = BI->getSuccessor(i)->getName().data();
			std::cerr << bbName << " ";
		}
		std::cerr << ")" << std::endl;
	}else{
		std::cerr << "BRANCH_UNCOND " << " " ;
		for(auto i = 0 ; i < numSuccessors ; i++)
			std::cerr << BI->getSuccessor(i) -> getName().data() << " ";
		std::cerr << std::endl;
	}
}

void pathCounter::runOnLoad(LoadInst *LI) {
	// eg. %0 = load *x
	// get taint of pointer, get taint of LI instruction
	// assign pointer taint to LI instruction
	auto P = LI->getPointerOperand();
	assignTaint(LI, P);
}


void pathCounter::runOnReturn(ReturnInst *RI) {
  	
  if (auto RV = RI->getReturnValue()) {
	auto retTaint = getTaint(RV);
	if(retTaint == 0){
		retTaint = assignTaint(RV);
	}
	std::cerr << F->getName().data() << ".ret=t" << retTaint << std::endl;
   }
}

void pathCounter::runOnCast(CastInst *I) {
	auto operand = I->getOperand(0);
	assignTaint(I, operand);
}

void pathCounter::runOnBinary(BinaryOperator *I) {
	auto operand0 = I->getOperand(0);
	auto operand1 = I->getOperand(1);
	auto t0 = getTaint(operand0);
	if(t0 == 0){
		t0 = assignTaint(operand0);
	}
	auto t1 = getTaint(operand1);
	if(t1 == 0){
		t1 = assignTaint(operand1);
	}
	auto instructionTaint = getTaint(I);
	assert(instructionTaint);
	std::cerr  <<  "t" << instructionTaint << "=("<< I->getOpcodeName() << ",t" << t0 << " , t" << t1 << ")" << std::endl;
}

void pathCounter::runOnICmp(ICmpInst *I) {
	auto op1 = I->getOperand(0);
	auto op2 = I->getOperand(1);
	auto Pred = I->getUnsignedPredicate();

	auto t1 = getTaint(op1);
	if(t1 == 0)
		t1 = assignTaint(op1);
	auto t2 = getTaint(op2);
	if(t2 == 0)
		t2 = assignTaint(op2);
	auto iTaint = getTaint(I);
				
	std::cerr << "t" << iTaint << "=(" << Predicate[Pred] << ",t" << t1 << ",t" << t2 << ")" << std::endl;
}

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
