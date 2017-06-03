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
#include <sstream>
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

/* linkBranch and linComparator structures are used to keep track of immediately previous
 * branch condition {next basic blocks} and comparator instruction {comparator, operand1 , operand2} 
 * that were processed while going through a path context. before going to any basic block
 * that is preceeded by a conditional statement, we store the comparator in linkComparator
 * data structure. the different basic blocks that one can go to due to this comparator 
 * evaluation is stored in linkBranch structure.
 * */

struct Branch {
	uint64_t taint;
	std::string b1;
	std::string b2;
}linkBranch;

std::map<int, const char *> varType {
{ 0, "i"},
{ 1, "pi"},
{ 2, "c"},
{ 3, "pc"},
{ 4, "ppc"},
};

struct Comparator {
	uint64_t taint;
	std::string sign;
	uint64_t t1;
	char t1Type;
	uint64_t t2;
	char t2Type;
} linkComparator;

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

  void runOnArgs(void);
  void printFunctionName(const char *s);
  void printGbbMap(std::map <std::string, uint64_t> *GbbMap);
  void pushToCallStack(const char *s);
  void printCallTrace();
  void printString(Instruction *I, const char *s);

uint64_t  LoadStoreSize(const DataLayout *DL, Value *P);
  void runOnLoad(LoadInst *LI);
  void runOnStore(StoreInst *SI);
  void runOnBranch(BranchInst *BI);
  bool runOnCall(CallInst *CI);
  void markVariable(CallInst *CI);
  void runOnReturn(ReturnInst *RI);
  void runOnUnary(UnaryInstruction *I);
  void runOnCast(CastInst *I);
  void addMarkerTaint();
  bool hasFunctionCall(BasicBlock *BB);
  void runOnBinary(BinaryOperator *I);
	void runOnICmp(ICmpInst *I);
	void runOnAlloca(AllocaInst *I, uint64_t);
	void runOnGetElementPtr(GetElementPtrInst *I);
  void getFunctionPPWithoutCalls();
	void cleanup();
	void initializeVariables(Module &M);

	void Store(uint64_t addr, uint64_t size, Taint t);
	
  void getModuleLevelPP( std::map <std::string, uint64_t> *GbbMap);
	//std::map <uint64_t, uint64_t> taintMap;
	bool markedProcessed();
	bool processedFunctionCaller();
	void analyseFunctionCalls();
// 	void runOnIntrinsic(MemIntrinsic *MI);
	void runOnInstructions(BasicBlock *B, int retNumber);
  int getFunctionPP(std::stack <const char*> *FStack, std::map<std::string, uint64_t> *GbbMap);
	//void processBlock(BasicBlock *BB);
	std::vector<const char *> processedBlocks;
  int getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map<std::string, uint64_t> *GbbMap);
	void processBasicBlock(BasicBlock *BB);
  //BasicBlock *getBB(const char *name);
	int getCF(BasicBlock *BB);
	uint64_t getBasicBlockPP(BasicBlock *BB, std::stack <const char *> *bbStack, std::map< const char *, uint64_t > *bbMap , std::stack <const char *> *FStack, std::map < std::string, uint64_t > *GbbMap);

	void printCFMap();
	void printPaths();
	void printFunctionPPMap();
	void printStack(std::stack <const char *> *bbStack);
	int  getConvergence(BasicBlock *BB);
	int  getMaxConvergence(TerminatorInst *I);

	void trackLoad(Value *I);
	void printMap();
	unsigned getConstant(Value *op);
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
	void enumeratePaths(std::map<std::string, uint64_t > *GbbMap, BasicBlock *BB);

	void __fslice_store (uint64_t size, Value  *addr , Value *taint);
	void printFunCallFromBB(const char *bbName);
	uint64_t queryPP(BasicBlock *BB, std::map<std::string, uint64_t> *GbbMap);
  void track(Value *V);
  int marked(Value *V);

  uint64_t getTaint(Value *V);
  uint64_t updateTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	// stores loopBack Basic Block and its successor basic block that creates
	// the loop
	std::map<BasicBlock *, BasicBlock *> loopBackBBs;

	std::map<BasicBlock *, uint64_t> *CFMap = new std::map <BasicBlock *, long unsigned int>;
	std::map<BasicBlock *, uint64_t> *PPMap = new std::map <BasicBlock *, long unsigned int>;
	std::map<const char *, uint64_t> functionPPMap;
  	std::vector <Value *> trackTaint;
	// map of functions and pointer to map of (BB,ConvergenceFactor)
	// for each BB in that function.
	std::map <const char *, void *> functionConvergenceFactorMap;
	void taintInstructions();
	void taintInstructions(BasicBlock *BB);
	void printMarkedInstructions(BasicBlock *BB);

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


void assignTaint(Value *Dest, Value *Src, char taintType, std::string tag);
uint64_t assignTaint(Value *Val);

// creates a map of function and map of instruction and taints

  std::map<Function *, std::map<Value *, uint64_t> *> FTMapMap;
// marks <value, symbolic type> [0,1,2 for INT, STR, VAR_ARRAY]
  std::map<Value *, uint64_t> markerTypeMap;
// created for every function. stores "value" of each operator
// and operand and corresponding taint number
  std::map <Value *, uint64_t > * TMap;
// created for every function, stores all taint numbers of
// marked variables and variables derived from marked variables
  std::vector < uint64_t > MarkedTaints;
// constant Taints
  std::vector < uint64_t > ConstantTaints;
// Map of all constant values being referred.
  std::map <uint64_t, uint64_t> * CMap; 
  int numVSets;
  uint64_t taintNo;
// Scheduler
	std::priority_queue<pathPotentialTuple, std::vector<pathPotentialTuple>, Compare> Scheduler;
	bool isSolvable();
	bool isSolvable(BasicBlock *);
	void updatePathContext(BasicBlock *currentBB);
	BasicBlock* getNextMaxBB(BasicBlock *currentBB, std::map<std::string, uint64_t > *GbbMap);
	void  getModel();
	BasicBlock* loadContext();
	void saveContext (BasicBlock *currentBB, std::map<std::string, uint64_t > *GbbMap);
	std::string pathContext;
	// functionname-bbname:functionname-bbname:functionname1-bbname1#call1!calledFunction&functionname1-bbname1#ret1!calledFunction:functionname1-bbname2#ret2!calledFunction
	// - function, bb separator
	// : <function, bb > tuple separator
	// #bbname-call/ret
	// !calledfunction
	// & pending ret calls
	std::vector <std::string > * parseBBString(std::string s);
	std::tuple <BasicBlock *, std::string> getNextBB(std::string *bbString);
	bool solve();
// z3
	bool linkComparatorIsEmpty();
	void clearLinkComparator();
	bool linkBranchIsEmpty();
	void clearLinkBranch();
	std::string  getSign(std::string pred);
	std::string  getSymbol(std::string pred);
	void  initializeLinkComparator(uint64_t iTaint, std::string pred, uint64_t t1, char t1Type, uint64_t t2, char t2Type);
	void derivePreviousCondition(BasicBlock *BB);
	// ****
	// symPtr is a vector that stores all pointer variables to symbolic array.
	// for each element that is accessed using getElementPtr instruction, we
	// add the resultant address computation taint (pointer) in this vector
	// ****
	// When store on an element happens, we update the pointer variable as well
	// and equate pointer variable with earlier taint of address (s.add p32 == p30)
	// we also add interger (i32) variable and add i32 == 10
	std::vector <int> symPtr;
	void z3printPointerAndInteger(uint64_t lhs, uint64_t rhs);

	// helper functions to enumerate bbs having function calls
	BasicBlock *getNextCalledBB( std::map<std::string, uint64_t > *GbbMap, std::string &pathContext);
	bool nonProcessedCalls(BasicBlock *bb);
	std::string getCallPathContext(BasicBlock *bb);
	BasicBlock *updatePendingBB();
	std::vector <std::string> tokenize(std::string callPath);
	bool pendingPaths();
	void updateCallPathContext(std::string callPathCtxt);
	void updateRetPathContext();
	bool returnBBsPresent();
	void processFunctionEntryBlock(BasicBlock *B);
	std::vector <uint64_t> g_argumentTaints;
	uint64_t g_CalledFunctionReturnTaint;
	// return Taint Stack of all 'x''s in x = A() type call.
	// when we encounter a return statement in Called Function, we do
	// g_returnTaintStack.top() = g_CalledFunctionReturnTaint;
	std::stack <uint64_t> g_returnTaintStack;
	Instruction * skipInstructions(BasicBlock *B, int retNumber);
};

/* derivePreviousCondition(BasicBlock *BB)
 * while traversing a basic block, we evaluate if its predecessor was a conditional block. If yes,
 * we obtain the comparision instruction that evaluated to either true or false to reach the current
 * Basic Block BB.
 * */

void pathCounter :: derivePreviousCondition(BasicBlock *BB)
{
	std::cerr << "#" << __func__ << "()" << std::endl;
	auto basicBlockName = BB->getName().data();
	bool comparator;
	if(linkBranchIsEmpty())
		return;
	else{
		// if current block was first basic block in previous branch
		// condition, comparator is True, else it is False
		// s.add( t2 < t17)
		comparator = !strcmp(basicBlockName, linkBranch.b1.c_str());
		std::cerr << "#" << __func__ << "(): linkComparator = " << linkComparator.t1 << " "  << linkComparator.sign << " " 
			<< linkComparator.t2  << std::endl;
		if(comparator){
			std::cerr << "s.add( " << linkComparator.t1Type << linkComparator.t1 << linkComparator.sign 
						<< " " << linkComparator.t2Type << linkComparator.t2 << " )"<< std::endl;
		}else{
			std::cerr << "s.add((" << linkComparator.t1Type << linkComparator.t1 << linkComparator.sign 
						<< " " << linkComparator.t2Type << linkComparator.t2 << ") == False )" << std::endl;
		}
		clearLinkBranch();
		clearLinkComparator();
	}
}

bool pathCounter :: linkComparatorIsEmpty()
{
	return (linkComparator.taint == 0);
}

bool pathCounter :: linkBranchIsEmpty()
{
	return (linkBranch.taint == 0);
}

void pathCounter :: clearLinkComparator()
{
	linkComparator.taint = 0;
	linkComparator.sign.clear();
	linkComparator.t1 = 0;
	linkComparator.t2 = 0;
	linkComparator.t1Type = '\0';
	linkComparator.t2Type = '\0';
}

void pathCounter :: clearLinkBranch()
{
	linkBranch.taint = 0;
	linkBranch.b1.clear();
	linkBranch.b2.clear();
}

std::string pathCounter :: getSymbol(std::string opCode){
	if(!opCode.compare("add")){
		return std::string (" + ");
	}else if(!opCode.compare("sub")){
		return std::string (" - ");
	}else if(!opCode.compare("ne")){
		return std::string (" != ");
	}else{
		std::cerr << "YYY TODO ADD CONDITION FOR PRED" << opCode << std::endl;
		assert(0);
	}
}

/* returns mathematical sign equavalent of the LLVM Compare string */

std::string  pathCounter :: getSign(std::string pred){
	if(!pred.compare("FCMP_FALSE")){
		return std::string (" != ");
	}else if(!pred.compare("ICMP_ULT")){
		return std::string (" < ");
	}else if(!pred.compare("ICMP_EQ")){
		return std::string (" == ");
	}else if(!pred.compare("ICMP_NE")){
		return std::string (" != ");
	}else{
		std::cerr << "XXX TODO ADD CONDITION FOR PRED " << pred << std::endl;
		assert(0);
	}
}

//bool pathCounter :: linkComparatorIsEmpty()
//std::string pathCounter :: getSign(std::string pred){
void pathCounter:: initializeLinkComparator(uint64_t iTaint, std::string pred, uint64_t t1, char t1Type, uint64_t t2 , char t2Type)
{
	linkComparator.taint = iTaint;
	linkComparator.t1 = t1;
	linkComparator.t2 = t2;
	linkComparator.t1Type = t1Type;
	linkComparator.t2Type = t2Type;
	linkComparator.sign = getSign(pred);
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

unsigned pathCounter :: getConstant(Value *op)
{
	if (ConstantInt *CI = dyn_cast<ConstantInt>(op)){
		if(CI->getBitWidth() <=64){
			auto integer1 = CI->getZExtValue();
			return integer1;
		}else{
			std::cerr << "Found const value with size > 64" << std::endl;
			assert(0);
		}
	}else{
		std::cerr << "NOT CONSTANT" << std::endl;
		assert(0);
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

int pathCounter :: getPPOfFunctionCalls(BasicBlock *BB, std::stack <const char *> *FStack, std::map <std::string, uint64_t > *GbbMap)
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

uint64_t pathCounter :: getBasicBlockPP(BasicBlock *BB, std::stack <const char *> *bbStack, std::map <const char *, uint64_t> *bbMap ,std::stack <const char *> *FStack, std::map<std::string, uint64_t> *GbbMap)
{
	if(BB == NULL){
		assert(0);
	}
	D(printStack(FStack);)
	auto TerminatorInst = BB->getTerminator();
	uint64_t numSucc = TerminatorInst->getNumSuccessors();
	uint64_t calledFunctionPP = 1;
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
		uint64_t alternateBB_PP;
		if(bbMap->find(alternateBBName) != bbMap->end()){
			alternateBB_PP = (*bbMap)[alternateBBName];
		}else{
			bbStack	->push(alternateBBName);
			alternateBB_PP = getBasicBlockPP(alternateBB, bbStack, bbMap, FStack, GbbMap);
			bbMap->insert(std::pair<const char *, uint64_t>(alternateBBName, alternateBB_PP)); 
			std::string funNameBB(FStack->top());
			funNameBB += ":";
			funNameBB += alternateBBName;
			GbbMap->insert(std::pair<std::string, uint64_t >(std::string(funNameBB.data()),alternateBB_PP));
			bbStack->pop();
		}
		auto currentBB_PP = calledFunctionPP * alternateBB_PP;
		if(bbMap->find(bbName) != bbMap->end()){
			std::cerr << "**** LOOP Collision ****" << FStack->top() << "():" << bbName << std::endl;
		}else{
			bbMap->insert(std::pair<const char *, uint64_t>(bbName, currentBB_PP));	
			std::string funNameBB(FStack->top());
			funNameBB += ":";
			funNameBB.append(bbName);
			GbbMap->insert(std::pair<std::string, uint64_t >(std::string(funNameBB.data()),currentBB_PP));
		}
		return currentBB_PP;
	}else{
		if (numSucc == 0){
			PPMap->insert(std::pair<BasicBlock *, uint64_t> (BB, 1));
			auto currentBB_PP = getPPOfFunctionCalls(BB, FStack, GbbMap);
			D(std::cerr << __func__ << "(): " << "reached terminator block " << BB->getName().data() << std::endl;)
			D(printStack(bbStack);)
			if(bbMap->find(bbName) != bbMap->end()){
				std::cerr << "**** SUCC 0 Collision ****" << FStack->top() << "():" << bbName << std::endl;
			}else{
				bbMap->insert(std::pair<const char *, uint64_t>(bbName, currentBB_PP));
				std::string funNameBB(FStack->top());
				funNameBB += ":";
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, uint64_t >(std::string(funNameBB.data()),currentBB_PP));
			}
			return currentBB_PP;
		}else{
			calledFunctionPP = getPPOfFunctionCalls(BB, FStack, GbbMap);	
			auto TerminatorInst = BB->getTerminator();
			uint64_t currentBB_PP = 0;
			for(uint64_t i = 0 ; i < numSucc ; i++){
				auto nextBB = TerminatorInst->getSuccessor(i);
				//calledFunctionPP = getPPOfFunctionCalls(nextBB, FStack);
				auto nextBBName = nextBB->getName().data();
				uint64_t nextBB_PP;
				if(bbMap->find(nextBBName) != bbMap->end()){
					nextBB_PP = (*bbMap)[nextBBName];
				}else{
					bbStack->push(nextBBName);
					D(std::cerr << __func__ << "(): calling BB_PP of " << nextBBName  << std::endl;)
					//printStack(bbStack);
					nextBB_PP = getBasicBlockPP(nextBB, bbStack, bbMap, FStack, GbbMap);
					bbMap->insert(std::pair<const char *, uint64_t>(nextBBName, nextBB_PP));
					std::string funNameBB(FStack->top());
					funNameBB += ":";
					funNameBB.append(nextBBName);
					GbbMap->insert(std::pair<std::string, uint64_t >(std::string(funNameBB.data()),nextBB_PP));
					bbStack->pop();
				}
				currentBB_PP += (calledFunctionPP * nextBB_PP);
			}
			PPMap->insert( std::pair<BasicBlock *, uint64_t> (BB, currentBB_PP) );
			if(bbMap->find(bbName) != bbMap->end()){
				std::cerr << "**** SUM UP children Collision ****" << FStack->top() << "():" << bbName << std::endl;
				std::cerr << "PREV VALUE = " << (*bbMap)[bbName] << " new value " << currentBB_PP << std::endl;
				(*bbMap)[bbName] = currentBB_PP;
				std::string funNameBB(FStack->top());
				funNameBB += ":";
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, unsigned >(std::string(funNameBB.data()),currentBB_PP));
			}else{
				bbMap->insert(std::pair<const char *, uint64_t>(bbName, currentBB_PP));
				std::string funNameBB(FStack->top());
				funNameBB += ":";
				funNameBB.append(bbName);
				GbbMap->insert(std::pair<std::string, uint64_t >(std::string(funNameBB.data()),currentBB_PP));
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

void pathCounter :: printGbbMap(std::map <std::string, uint64_t > *GbbMap)
{
	for(auto it = GbbMap->begin() ; it != GbbMap->end() ; it++)
	{
		std::cerr << it->first << " " << it->second << std::endl;
	}
}

std::vector <std::string > * pathCounter::parseBBString(std::string s)
{
	std::string var;
	std::vector <std::string> *V = new std::vector <std::string> ;
	D(std::cerr << "s is " << s << std::endl;)
	for(unsigned i = 0 ; i < s.size() ; i++){
		if(s[i] == ':'){
			V->push_back(var);
			var.clear();
		}else{
			var += s[i];
		}
	}
	V->push_back(var);
	return V;
}

const char* pathCounter :: isLoopBack(BasicBlock *BB)	// finds loopback in pathCounter
{
	auto BBName = BB->getName().data();
	auto FName = BB->getParent()->getName().data();
	std::string s(pathContext);
        std::string funDelimiter(":");
        std::string bbDelimiter("-");

	std::vector <std::string > *V = parseBBString(s);

	D(std::cerr << "V size is " << V.size() << std::endl;)

	if(V->size() == 0){
		delete V;
		return nullptr;
	}
	std::string searchString(std::string(FName) + "-" + std::string(BBName) + ":");
	for(unsigned i = 0 ; i < V->size() -1 ; i++){
		D(std::cerr << (*V)[i] << std::endl;)
		if((*V)[i].find(searchString) != std::string::npos){
			D(std::cout << "next tuple = " << (*V)[i+1] << std::endl;)
			std::string nextBB((*V)[i+1].substr((*V)[i+1].find('-') + 1, (*V)[i+1].length()));
			D(std::cout << "next bb = " << nextBB.c_str() << std::endl;)
			delete V;
			return nextBB.c_str();
		}
	}
	delete V;
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


int pathCounter :: getFunctionPP(std::stack <const char*> *FStack, std::map <std::string, uint64_t> *GbbMap)
{
	// get current Function Context.
	D(printStack(FStack);)
	assert(!FStack->empty());
	auto FunName = FStack->top();
	D(std::cerr << FunName << "()" << std::endl;)
	//FStack->pop();

	D(std::cerr << "Processing PP for Function " << FunName << "()" << std::endl;)
	if(isLoopBack(FunName,FStack)){
		D(std::cerr << __func__ << "(): " << FunName << " is loopback"  << std::endl;)
		FStack->pop();
		D(std::cerr << "PP: " << FunName << " = " << 0 << std::endl;)
		functionPPMap[FunName]=0;
		return 0;
	}
	// compute and return PP here
	int funPP;
	if(functionPPMap.find(FunName) == functionPPMap.end()){
		std::stack <const char *> localStack;
		std::map <const char *, uint64_t> bbMap;
		localStack.push("entry");
		funPP = getBasicBlockPP(M->getFunction(FunName)->begin(), &localStack, &bbMap , FStack, GbbMap);
		D(std::cerr << "PP: " << FunName << " = " << funPP << std::endl;)
		functionPPMap[FunName] = funPP;
	}else {
		funPP = functionPPMap[FunName];
		D(std::cerr << "PP: ALREADY PROCESSED, REUSING " << FunName  << funPP << std::endl;)
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

void pathCounter:: getModuleLevelPP( std::map < std::string, uint64_t> *GbbMap)
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
	uint64_t totalPP = getFunctionPP(&functionStack, GbbMap);
	std::cerr << "Total PP " << totalPP << std::endl;
}

uint64_t pathCounter::assignTaint(Value *V)
{
	std::cerr << "#" << __func__ << "()" << std::endl;
	uint64_t integer;
	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)){
		if(CI->getBitWidth() <=64){
			integer = CI->getZExtValue();
			if(CMap->find(integer) == CMap->end()){
				//std::cerr << __func__ << "():Assigning int constant " << integer << " taint value " << taintNo << std::endl;
				std::cerr << "i" << taintNo << " = Int('i" << taintNo << "')" << std::endl;
				std::cerr << "s.add(i" << taintNo << " == " << integer << ")" << std::endl;
				std::cerr << "# CONSTANT TAINT " << taintNo << std::endl;
				(*CMap)[integer] = taintNo++;
				if(std::find(ConstantTaints.begin(), ConstantTaints.end(), (*CMap)[integer]) == ConstantTaints.end())
					ConstantTaints.push_back((*CMap)[integer]);
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

void pathCounter::assignTaint(Value *Dest, Value *Src, char taintType, std::string tag)
{
	std::cerr << "#" << __func__ << "()" << std::endl;
	auto srcTaint = getTaint(Src);
	if(srcTaint == 0){
		srcTaint = assignTaint(Src);
	}
	auto destTaint = updateTaint(Dest);
	(*TMap)[Dest] = destTaint;

	if(std::find(MarkedTaints.begin(), MarkedTaints.end(), srcTaint) != MarkedTaints.end()){
		if(std::find(MarkedTaints.begin(), MarkedTaints.end(), destTaint) == MarkedTaints.end()){
			std::cerr <<"#" << __func__ << "():MARKED " << destTaint << std::endl;  
			MarkedTaints.push_back(destTaint);
		}
	}

	if(taintType == 'i'){
		std::cerr << "i" << (*TMap)[Dest] << " = Int('i" << (*TMap)[Dest] << "')" << std::endl;
		std::cerr << "s.add(" << taintType << (*TMap)[Dest] << " == " << taintType << srcTaint << ")" << std::endl;
	}else{
		z3printPointerAndInteger( (*TMap)[Dest], srcTaint);
	}
	if(!tag.compare("LOAD")){
		//XXX
		if(std::find(MarkedTaints.begin(), MarkedTaints.end(), srcTaint) != MarkedTaints.end()){
			if(taintType == 'i')
				std::cerr << "#READ " << taintType << " " << srcTaint << std::endl;
		}
	}else if(!tag.compare("STORE")){
		if(std::find(MarkedTaints.begin(), MarkedTaints.end(), (*TMap)[Dest]) != MarkedTaints.end()){
			if(taintType == 'i')
				std::cerr << "#WRITE " << taintType << " " << (*TMap)[Dest] << std::endl;
		}	
	}
}

void pathCounter::taintInstructions()
{
	std::cerr << "#" << __func__ << "()" << std::endl;
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

void pathCounter::z3printPointerAndInteger(uint64_t lhs, uint64_t rhs)
{
	// create symbolic variable of lhs.
	// add z3 assert s.add(lhs == rhs)
	std::cerr << "p" << lhs << "=Int('p" << lhs << "')" << std::endl;
	std::cerr << "s.add(p" << lhs << "==p" << rhs << ")" << std::endl;

	if( (std::find(symPtr.begin(), symPtr.end(), rhs) != symPtr.end() ) ){
		std::cerr << 'i' << lhs << "=Int('i"
			<< lhs << "')" << std::endl; 
		std::cerr << "s.add(i" << lhs << "==i"
			<< rhs << ")" << std::endl;
	}
	std::cerr << "#" << __func__ << ":end" << std::endl;
}

void pathCounter::taintInstructions(BasicBlock *B)
{
	std::cerr << "#" << __func__ << "()" << std::endl;
	for (auto &I : *B) {
		if(TMap->find(&I) == TMap->end()){
			(*TMap)[&I] =taintNo++;
		}	
		if(CallInst *CI = dyn_cast<CallInst>(&I)) {
			std::string callFunctionName(CI->getCalledFunction()->getName().data());
			if(callFunctionName.find("_mark") != std::string::npos){
				auto taintType = CI->getCalledFunction()->getReturnType()->isPointerTy() ? 'p' : 'i';
				if(taintType == 'i'){
					std::cerr << taintType << (*TMap)[&I] 
						<< "=" << taintType << (*TMap)[CI->getOperand(0)] << std::endl;
				}
				// if taint Type is pointer to array, create a variable equivalent for
				// the pointer to the array
				if(taintType == 'p'){
					z3printPointerAndInteger( (*TMap)[&I] , (*TMap)[CI->getOperand(0)] );
									// CI return also added as a symPtr
					symPtr.push_back((*TMap)[&I]);
					if(std::find(MarkedTaints.begin(), MarkedTaints.end(),(*TMap)[&I]) == MarkedTaints.end()){
						std::cerr << "#" << __func__ << "():MARKED " << (*TMap)[&I] << std::endl;
						MarkedTaints.push_back((*TMap)[&I]);
					}
				}
			}
		}	
	}
}

void pathCounter::runOnArgs(void) {
	for (auto &A : F->args()){
		uint64_t TA = getTaint(&A);
		if (TA == 0) {
			(*TMap)[&A] = taintNo++; 
		}
	}
}

Instruction *pathCounter :: skipInstructions(BasicBlock *B, int retNumber)
{
	return nullptr	;
//	int callCounter = 0;
//	if(retNumber == 0)
//		return B->begin();
//
//	for (auto I1 = 	B->begin() ; I1!= B->end() ; I1++){
//		CallInst *CI = dyn_cast<CallInst>(I1);
//		if(CI != nullptr){
//			std::string calledFunction(CI->getCalledFunction()->getName().data());
//			if(calledFunction.find("_mark") == std::string::npos){
//				callCounter++;
//				if(callCounter == retNumber){
//					return ++I1;
//				}
//			}
//		}
//	}
//	std::cerr << __func__ << "(): retNumber = " << retNumber 
//		<< " number of Function Calls Found = " << callCounter << std::endl;
//	assert(0);
}

/* retNumber is the call Instruction number in a basic block till which we 
 * should skip processing instructions.
 * */

void pathCounter:: runOnInstructions(BasicBlock *B, int retNumber)
{
	printMarkedInstructions(B);
	taintInstructions(B);
	derivePreviousCondition(B);
	uint64_t allocaCount = 0;
	bool firstTime = true;
	std::cerr << "#" << __func__ << "(): processing " << B->getParent()->getName().data() << "():" << B->getName().data() << std::endl;
	for (auto I = B->begin(); I != B->end() ;I++) {
		std::cerr << "#" << __func__ << "():for start " << std::endl;
		if(retNumber !=0 && firstTime){
			std::cerr << "#" << __func__ << "(): Ret Number " << retNumber << std::endl;
			// step through to Instruction after retNumber Call Instructions
			int callCounter = 0;
			while(callCounter != retNumber){
				std::cerr << "#" << __func__ << "():callCounter = " << callCounter << std::endl;
				CallInst *CI = dyn_cast<CallInst>(I);
				if(CI != nullptr){
					std::string calledFunction(CI->getCalledFunction()->getName().data());
					if(calledFunction.find("_mark") == std::string::npos){
						callCounter++;
						if(callCounter == retNumber){
							I++;
							break;
						}
					}
				}
				I++;
			}
			firstTime = false;
		}
		std::cerr << "#" << __func__ << "(): Ret Number " << retNumber << std::endl;
		std::cerr << "#" << __func__ << "(): NEXT INSTRUCTION " << std::endl;
		if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
			runOnLoad(LI); 
		} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
			runOnStore(SI);
		} else if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
			runOnBranch(BI);
		} else if (CallInst *CI = dyn_cast<CallInst>(I)) {
			bool ret = runOnCall(CI);
			if(ret){	// exit current BB	
					// process called function
				return;
			}
		} else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
			runOnReturn(RI);
		} else if (CastInst *CI = dyn_cast<CastInst>(I)) {
			runOnCast(CI);
		} else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(I)) {
			runOnBinary(BI);
		} else if (ICmpInst *IC = dyn_cast<ICmpInst>(I)) {
			runOnICmp(IC);
		} else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
			// allocaCount monitors number of allocations done in entry Basic Block
			runOnAlloca(AI, allocaCount);
			if(!std::string(B->getName().data()).compare ("entry") &&
				std::string(B->getParent()->getName().data()).compare("main")){
				allocaCount++;
			}
		} else if (GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(I)) {
			runOnGetElementPtr(GI);
		}else{
			std::cerr << __func__ << "(): Could not match instruction " << std::endl;
			assert(0);
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
		if(CallInst *CI = dyn_cast<CallInst>(&I)){
			std::string callFunctionName(CI->getCalledFunction()->getName().data());
			if(callFunctionName.find("_mark") == std::string::npos){
				std::cerr << "#" << __func__ << "():return True" << std::endl;
				return true;
			}	
		}
	}
	std::cerr << "#" << __func__ << "():return False" << std::endl;
	return false;
}

void pathCounter::printMarkedInstructions(BasicBlock *BB)
{
	for(auto &I : *BB){
		if(CallInst *CI = dyn_cast<CallInst>(&I)){
			std::string callFunctionName(CI->getCalledFunction()->getName().data());
			if(callFunctionName.find("_mark") != std::string::npos){
				markVariable(CI);
			}
		}
	}
}

uint64_t pathCounter :: queryPP(BasicBlock *BB, std::map<std::string, uint64_t> *GbbMap)
{
	auto currentBBName = BB->getName().data();
	auto functionName = BB->getParent()->getName().data();
	std::string s(functionName);
	s += ":";
	s += currentBBName;
	assert(GbbMap->find(s) != GbbMap->end());
	return (*GbbMap)[s];
}

/* this function reduces bbString by 1 basic block. returns the {basic block, skipCall number}
 * skipCall number is the number of function calls in basic block till when the basic block
 * instructions should not be processed. this is stored in bbString and used while creating
 * taint instructions.
 * */

//std::tuple <BasicBlock *, std::string callRetNumber> pathCounter:: getNextBB(std::string *bbString)
std::tuple <BasicBlock *, std::string> pathCounter:: getNextBB(std::string *bbString)
{
	std::string s(*bbString);
	std::vector <std::string> *V = parseBBString(s);
	std::string nextBB, nextFun;
	std::string token;
	std::string callRetNumber;
	if(V->size() == 0){
		token = s; 
		D(std::cerr << "#VSIZE = 0, token = " << token << std::endl;)
		nextBB = s.substr(s.find("-") + 1, s.find("#"));
		nextFun = s.substr(0, s.find("-"));
		D(std:: cerr << "#"<< __func__ << "():FUNName " << nextFun << " Basic Block = " << nextBB << std::endl;)
		bbString->clear();
	}else{  
		token = (*V)[0];
		D(std::cerr << "#VSIZE != 0, token = " << token << std::endl;)
		std::string leftString = token.substr(token.find("-") + 1);
		nextBB = leftString.substr(0,  leftString.find("#"));
		nextFun = token.substr(0, token.find("-"));
		D(std:: cerr << "#"<< __func__ << "():FUNName " << nextFun << " Basic Block = " << nextBB << std::endl;)
		bbString->clear();
		unsigned i;
		for( i= 1 ; i < V->size() ; i++){
			bbString->append((*V)[i]);
			if(i != V->size() - 1)
				bbString->append(":");
		}
		D(std::cout << " V() Size = " << V->size() << std::endl;)
	}

	if(token.find("#") != std::string::npos){
		callRetNumber = token.substr(token.find("#") + 1);
	}

	auto F = M->getFunction(nextFun.c_str());
	for(auto &BB : *F)
	{	
		if(!strcmp(BB.getName().data(), nextBB.c_str()))
			return std::make_tuple (&BB, callRetNumber);
	}
	std::cerr << "#" << __func__ << "():" << nextBB << " BB not found in function " << nextFun << "()" << std::endl;
	assert(0);
}

/* process Entry Block - checks if B is the entry block, checks
 * if taint elements are present in callVect.
 * asserts if callVect is not of same size as number of arguments
 * in function. assigns function argument taints to argument
 * stored in callVect
 * clears callVect
 * returns
 * */

void pathCounter :: processFunctionEntryBlock(BasicBlock *B)
{
	F = B->getParent();
	if(F->hasName()){
		std::cerr << "#" << __func__ << "(): retrived function name " << F->getName().data() << std::endl;
	}
	std::string funEntryBBName = B->getParent()->getEntryBlock().getName().data();
	std::cerr << "#" << __func__ << "(): fun entry block anme = " << funEntryBBName << std::endl;
	if(!funEntryBBName.compare(B->getName().data())){
		// entry Block
		int count = 0;
		for (auto &A : F->args()){
			std::cerr << "#" << __func__ << "(): scanning arg = " << count << std::endl;
			uint64_t TA = getTaint(&A);
			if (TA == 0) {
				D(std::cerr << "taint argument " << count << " argTaintSize = " << g_argumentTaints.size() << std::endl;)
				std::cerr << "#" << __func__ << "(): taints assigned " << g_argumentTaints[count] << std::endl;
				(*TMap)[&A] = g_argumentTaints[count++]; 
			}/*else{
				std::cerr << "ERROR: unexpected taint assignment for argument " << std::endl;
			}*/
		}
		g_argumentTaints.clear();
	}
}

bool pathCounter :: solve()
{
	std::string bbString(pathContext);
	std::cerr << "#"<< __func__ << "():PATH CONTEXT " << pathContext << std::endl;
	int retNumber = 0;
	while(!bbString.empty()){
		std::tuple <BasicBlock *, std::string> x = getNextBB(&bbString);
		auto callRet = std::get<1>(x);
		if(!callRet.compare(0, strlen("call") , "call")){
			// fun1-bb1#call1!A is a NOP
			continue;
		}else if(!callRet.compare(0, strlen("ret"), "ret")){
			std::string subBBNumber =  callRet.substr(3, callRet.find("#"));
			std::istringstream buffer(subBBNumber);
			buffer >> retNumber;
			std::cerr << "#" << __func__ << "(): return Number = " << retNumber << std::endl;
		}else{
			processFunctionEntryBlock(std::get<0>(x));
		}
		runOnInstructions(std::get<0>(x), retNumber);
		retNumber = 0;
	}
	return true;
}

bool pathCounter::isSolvable()
{
	assert(!pathContext.empty());
	std::cerr << __func__ << "():"<< pathContext << std::endl;
	D(std::cerr << __func__ << "():"<< pathContext << std::endl;)
	return true; 
}

bool pathCounter::isSolvable(BasicBlock *nextBB)
{
	std::string oldPathContext(pathContext);
	pathContext += ":";
	pathContext += nextBB->getParent()->getName().data();
	pathContext += "-";
	pathContext += nextBB->getName().data();
	bool result = isSolvable();
	pathContext.clear();
	pathContext = oldPathContext;
	return result;
}

void pathCounter :: updatePathContext(BasicBlock *currentBB){
	std::cerr << "#" << __func__ << "(): before pathContext = " << pathContext << std::endl;
	if(pathContext.find("&") == std::string::npos){
		pathContext += ":";
		pathContext += currentBB->getParent()->getName().data();
		pathContext += "-";
		pathContext += currentBB->getName().data();
	}else{
		std::string newPath = pathContext.substr(0, pathContext.find("&"));
		newPath += ":";
		newPath += currentBB->getParent()->getName().data();
		newPath += "-";
		newPath += currentBB->getName().data();
		newPath += "&";
		newPath += pathContext.substr(pathContext.find("&") + 1);
		pathContext = newPath;
	}
	std::cerr << "#" << __func__ << "(): after pathContext = " << pathContext << std::endl;
}

// saves current pathContext + currentBB.getName() to scheduler
void pathCounter:: saveContext (BasicBlock *currentBB, std::map<std::string, uint64_t > *GbbMap){
	std::cerr << __func__ << "():current BB is " << currentBB->getName().data() << std::endl;
	std::cerr << __func__ << "():pathContext = " << pathContext << std::endl;
	auto currentBBPP = queryPP(currentBB, GbbMap);
	std::string token = ":";
	token += currentBB->getParent()->getName().data();
	token += "-";
	token += currentBB->getName().data();

	std::cerr << __func__ << "(): token = " << token << std::endl;	
	std::string pathToSave;
	if(pathContext.find("&") == std::string::npos){
		pathToSave += pathContext;
		pathToSave += token;
	}else{
		pathToSave = pathContext.substr(0, pathContext.find("&"));
		pathToSave += token;
		pathToSave += "&";
		pathToSave += pathContext.substr(pathContext.find("&") + 1);
	}
	std::cerr << __func__ << "(): pathContext = " << pathContext << " pathToSave = " << pathToSave << std::endl;
	assert(!pathToSave.empty());
	std::cerr << __func__ << "():saved path " << pathToSave << " path Potential " << currentBBPP << std::endl;
	pathPotentialTuple p(pathToSave,currentBBPP);
	Scheduler.push(	p);
}

// return child BB with minimum PP
BasicBlock* pathCounter:: getAlternateBB(BasicBlock *parentBB, const char *loopBackBlock){
	for(unsigned i = 0 ; i < parentBB->getTerminator()->getNumSuccessors(); i++){
		D(std::cerr <<__func__ << "loopBack Block " << loopBackBlock << 
	" compared block = " << parentBB->getTerminator()->getSuccessor(i)->getName().data() << std::endl;)
		if(strcmp(loopBackBlock,parentBB->getTerminator()->getSuccessor(i)->getName().data()) != 0){
			return parentBB->getTerminator()->getSuccessor(i);
		}
	}
	assert(0);
}

// choose between saved contexts and child basic blocks
// DO: add to path context before returning a basic block, if new basic block is detected

BasicBlock* pathCounter::getNextMaxBB(BasicBlock *currentBB, std::map<std::string, uint64_t > *GbbMap)
{
	BasicBlock *maxChildBB = currentBB->getTerminator()->getSuccessor(0);
	uint64_t maxChildBBPP = queryPP(maxChildBB, GbbMap);
	unsigned numSuccessors = currentBB->getTerminator()-> getNumSuccessors();
	uint64_t schedulerMaxPP = 0;
	if(!Scheduler.empty()){
		schedulerMaxPP = Scheduler.top().pathPotential;
		std::cout << __func__ << "():picked up scheduler element " << Scheduler.top().path << std::endl;
	}else{
		std::cerr << __func__ << "():scheduler is empty " << std::endl;
	}

	const char* alternateBBName = isLoopBack(currentBB);
	if(alternateBBName != nullptr){
		std::cerr << __func__ << "(): LOOP DETECTED " << std::endl;
		D(std::cerr << __func__ << "(): return block with less PP " << std::endl;)
		auto alternateBB = getAlternateBB(currentBB, alternateBBName);
		D(std::cerr << __func__ << "(): block returned " << alternateBB->getName().data() << std::endl;)
		updatePathContext(alternateBB);
		return alternateBB;
	}

	std::cerr << "#" << __func__ << "():number of successors = " << numSuccessors << std::endl;
	std::cerr << "#" << __func__ << "():pathContext = " << pathContext << std::endl;
	
	// choose max child, save state of other children
	for(unsigned i=1; i < numSuccessors ; i++){
		BasicBlock* nextChildBB = currentBB->getTerminator()->getSuccessor(i);
		uint64_t nextChildBBPP = queryPP(nextChildBB, GbbMap);
		if(nextChildBBPP > maxChildBBPP ){ // save less PP context
			std::cerr << __func__ << "():saving max child " << maxChildBB->getName().data() << std::endl;
			if(isSolvable(maxChildBB)){
				saveContext(maxChildBB, GbbMap);
			}
			maxChildBB = nextChildBB;
			maxChildBBPP = nextChildBBPP;
		}else{
			std::cerr << __func__ << "():saving next child " << nextChildBB->getName().data() << std::endl;
			if(isSolvable(nextChildBB)){
				saveContext(nextChildBB, GbbMap);
			}
		}
	}
	std::cerr << __func__ << "():child having max path potential " << maxChildBB->getName().data() << std::endl;
	std::cerr << __func__ << "(): path Context " <<pathContext << std::endl;
	std::cerr << __func__ << "(): max Child " << maxChildBB->getName().data() << std::endl; 
	// if max child is greater than scheduler max, or scheduler is empty,
	// continue. else save max child, load scheduler top

	if(maxChildBBPP < schedulerMaxPP){
		assert(schedulerMaxPP > 0);
		D(std::cerr << __func__ << "():picked scheduler top context " << Scheduler.top().path << std::endl;)
		D(std::cerr << __func__ << "():saved current Context " << pathContext << std::endl;)
		if(isSolvable(maxChildBB)){
			saveContext(maxChildBB, GbbMap);
		}
		D(std::cerr << __func__ << "():loaded new context " << std::endl;)
		maxChildBB = loadContext();
		D(std::cerr << __func__ << "context path " << pathContext << std::endl;)
	}else{
		D(std::cerr << __func__ << "():no update from scheduler " << currentBB->getName().data() << std::endl;)
		updatePathContext(maxChildBB);
	}
	std::cerr << __func__ << "(): path Context " << pathContext << std::endl;
	D(std::cerr << __func__ << "(): max Child " << maxChildBB->getName().data() << std::endl;)
	return maxChildBB;
}

void pathCounter :: getModel()
{
	std::cerr << "#>>>:::GETMODEL:::<<<" << std::endl;
	std::cerr << "#" << pathContext << std::endl;
	TMap = new std::map<Value *, uint64_t>;
	CMap = new std::map<uint64_t , uint64_t>;
	taintNo = 1;
	if(TMap == nullptr)
		std::cerr << __func__ << "null value allocated" << std::endl;

	solve();
//	for(auto it = MarkedTaints.begin() ; it!=MarkedTaints.end() ; it++){
//		std::cerr << "#MARKED " << *it << std::endl;
//	}
	MarkedTaints.clear();
	delete TMap;
	delete CMap;
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
	
		std::cerr << "#" << __func__ << "(): pathContext = " << pathContext << std::endl;
		std::string bbDelimiter = ":";
	        std::string funDelimiter = "-";
	        int lastIndex;
	        std::string lastBB(pathContext.substr(0, pathContext.find("&")));
	        while(lastBB.find(bbDelimiter)!=std::string::npos){
	                lastIndex = lastBB.find(bbDelimiter);
	                lastBB = lastBB.substr(lastIndex+1, lastBB.length());
	        }
	        lastIndex = lastBB.find(funDelimiter);
	        std::string lastFunName = lastBB.substr(0, lastIndex);
	        lastBB = lastBB.substr(lastIndex+1, lastBB.length());
		
		std::cerr << "#" << __func__ << "():loading path " << pathContext << std::endl;
		std::cerr << "#" << __func__ << "():last Basic Block received " << lastBB << std::endl;
		std::cerr << "#" << __func__ << "():last function name " << lastFunName << std::endl;

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

/* return BB after "&" sign. update pathContext from < & ret > to <ret & > */

BasicBlock *pathCounter::updatePendingBB()
{
	std::string newPath = pathContext.substr(0, pathContext.find("&"));
	std::string remainingPath = pathContext.substr(pathContext.find("&") +1);
	std::string nextBBName = remainingPath.substr(0,remainingPath.find(":"));
	newPath += ( ":" + nextBBName + "&" );
	remainingPath = remainingPath.substr(remainingPath.find(":") + 1);
	newPath += remainingPath;
	pathContext = newPath;
	D(std::cerr << __func__ << " new path " << pathContext << std::endl;)
		
	std::string bbTemp = nextBBName.substr(nextBBName.find("-") + 1);
	std::string bb = bbTemp.substr(0, bbTemp.find("#"));
	std::string fun = nextBBName.substr(0,nextBBName.find("-"));
	D(std::cerr << __func__ << " bbName " << bb << " funName " << fun << std::endl;)
	for(auto &F_ : M->functions()){
		F = &F_;
		if(F->getName().data() == fun){
			std::cerr << __func__ << "(): Next Function " << fun << std::endl; 
			break;	
		}
	}
	for (auto &B : *F) {
		if(B.getName().data() == bb){
			std::cerr << __func__ << "(): Next Basic Block " << std::endl; 
			return &B;
		}
	}
	assert(0);
	return nullptr;
}

// splits callpath by : and stores them in a vector
std::vector <std::string> pathCounter:: tokenize(std::string callPath)
{
	std::vector < std::string> res;
	std::stringstream ss(callPath);
	std::string token;
	while (ss >> token){
		res.push_back(token);
		if (ss.peek() == ':')
		          ss.ignore();	
	}
	for(auto it = res.begin() ; it != res.end() ; it++)
		std::cerr << "#" << __func__ << "():" << *it << std::endl;
	return res;
}

// 1. from pathContext and callPath, get next function and BB to be called.
// 2. if no new function is left to be called from callPath, return nullptr.
// 3. if next function to be called exists - update path context

// (move fun:bb#call and fun:bb#ret to left of &) get new bb
// (get called function, get bb for called function)
// add entry block of called function in path context as well

BasicBlock *pathCounter::getNextCalledBB( std::map<std::string, uint64_t > *GbbMap,  std::string &callPath)
{
	std::vector <std::string> calledFunctions = tokenize(callPath);
	std::string traversedPath = pathContext.substr(0,pathContext.find("&"));
	D(std::cerr << __func__ << "():traversed Path = " << traversedPath << std::endl;)
	for(auto callFun = calledFunctions.begin(); callFun != calledFunctions.end() ; callFun != calledFunctions.end()){
		if(traversedPath.find(*callFun) == std::string::npos){ // function not explored yet
			D(std::cerr << __func__ << "():found " << *callFun << " not traversed yet " << std::endl;)
			std::string funNameStart = callFun->substr(callFun->find("!") + 1);
			std::string funName = funNameStart.substr(0, funNameStart.find(":") );
			D(std::cerr << __func__ << "():called function " << funName << std::endl;)
			// get function from Module
			for(auto &F_ : M->functions()){
				F = &F_;
				if(F->getName().data() == funName){
					break;	
				}
			}

			D(std::cerr << __func__ << "(): extracted function " << F->getName().data() << std::endl;)
			// get function entry block from Module
			BasicBlock *entryBB = &(F->getEntryBlock());
			if(entryBB == nullptr){
				std::cerr << __func__ << "():RETURNING NULL" << std::endl;
			}
			std::string newPathContext = pathContext.substr(0,pathContext.find("&"));
			D(std::cerr << __func__ << "():path context after extraction " << newPathContext << std::endl;)
			std::string remainingPath = pathContext.substr(pathContext.find("&") +1);
			std::string nextCalledBB = remainingPath.substr(0,remainingPath.find(":"));
			remainingPath = remainingPath.substr(remainingPath.find(":") + 1);
			D(std::cerr << __func__ << "():remainingPath " << remainingPath << std::endl;)
			D(std::cerr << __func__ << "():newPathContext " << newPathContext << std::endl;)
			newPathContext += ":";
			D(std::cerr << __func__ << "():newPathContext " << newPathContext << std::endl;)
			newPathContext += nextCalledBB;
			D(std::cerr << __func__ << "():after adding nextCalledBB " << newPathContext << std::endl;)
			newPathContext += ( ":" + funName + "-" + entryBB->getName().data() );
			D(std::cerr << __func__ << "():after adding called function " << newPathContext << std::endl;)
			newPathContext += ( "&" + remainingPath );
			D(std::cerr << __func__ << "():after adding remaining path " << newPathContext << std::endl;)
			// change pathContext from <> & <fun1:> to <:fun1> & <fun2>
			pathContext = newPathContext;
			D(std::cerr << __func__ << "():new path Context " << pathContext << std::endl;)
			return entryBB; 
		}
	}
	return nullptr;	
}

// return true if there are any left over calls in pathContext
// i.e. any function1:bb1#ret1 where bb1 matches bb
bool pathCounter :: nonProcessedCalls(BasicBlock *bb )
{
	std::string bbName = bb->getName().data();
	std::string funName = bb->getParent()->getName().data();
	std::string calledFunctionToken = funName + "-" + bbName + "#call";
	D(std::cerr << "#" << __func__ << "(): pathContext = " << pathContext << std::endl;)
	if(pathContext.find("&") == std::string::npos){
		D(std::cerr << "#" << __func__ << "(): no more pending calls " << std::endl;)
		return false;
	}
	std::string unprocessedPath = pathContext.substr(pathContext.find("&") + 1);
	// search if any other calls are left in pathCtxt from bb
	D(std::cerr << "#" << __func__ << "():calledFunctionToken = " << calledFunctionToken << std::endl;
	std::cerr << "#" << __func__ << "():unprocessedPath = " << unprocessedPath << std::endl;)
	if( !unprocessedPath.empty() && unprocessedPath.find(calledFunctionToken) != std::string::npos)
	{
		std::cerr << "#" << __func__ << "() TRUE FOR PATH " << pathContext << std::endl;
		return true;
	}
	std::cerr << "#" << __func__ << "(): FALSE FOR PATH " << pathContext << std::endl;
	return false;	
}

bool pathCounter :: pendingPaths()
{
	if(pathContext.find("&") == std::string::npos)
		return false;
	std::string remainingPath = pathContext.substr(pathContext.find("&") + 1);
	std::cerr << "#" << __func__ << "(): pathContext = "<< pathContext << std::endl;
	std::cerr << "#" << __func__ << "(): remainingPath = "<< remainingPath << std::endl;
	if(remainingPath.find("call") !=std::string::npos)
		return true;
	return false;
}

// returns string of the form
// fun1-bb1#call1:fun1-bb1#ret1:fun1-bb1#call2:fun1-bb1#ret2

std::string pathCounter:: getCallPathContext(BasicBlock *B)
{
	std::string callString;
	std::string funName = B->getParent()->getName().data();
	std::string bbName = B->getName().data();
	int callCount=1;
	std::cerr << "#" << __func__ << "(): Basic Block name : " << B->getParent()->getName().data() << "():" << B->getName().data() << std::endl;
	for (auto I = B->begin(); I != B->end() ; I++) {
		CallInst *CI = dyn_cast<CallInst>(I);
		if (CI != nullptr) {
			std::string calledFunction = CI->getCalledFunction()->getName().data();
			std::cerr << "#" << __func__ << "(): CALL " << calledFunction << std::endl;
			if(calledFunction.find("_mark") != std::string::npos){
				continue;					
			}
			if(callString != ""){
				callString += ":";
			}
			callString += (funName	+ "-" + bbName + "#" + "call" + std::to_string(callCount) + "!" +calledFunction + ":" );
			callString += (funName	+ "-" + bbName + "#" + "ret" + std::to_string(callCount) + "!" + calledFunction );
			callCount++;
		}	
	}	
	std::cerr << "#" << __func__ << "():callString" << callString << std::endl;
	return callString;
}

/* append callPathContext to end of pathContext if not present in pathContext */
void pathCounter:: updateCallPathContext(std::string callPathCtxt)
{
	std::string anyToken = callPathCtxt.substr(0, callPathCtxt.find(":"));
	if(pathContext.find(anyToken) == std::string::npos){
		pathContext += ( "&" + callPathCtxt );
	}		
	std::cerr << "#" << __func__ << "(): " << pathContext << std::endl;
}

/* move first ret in funName:bb1#call1!A&funName:bb1#ret1!A from rhs of & to lhs */

void pathCounter:: updateRetPathContext()
{
	std::string newPath = pathContext.substr(0, pathContext.find("&"));
	std::string remPath = pathContext.substr(pathContext.find("&")+1);
	std::string retTuple = remPath.substr(0, remPath.find(":"));
	std::string leftPath;
	if(remPath.find (":") != std::string::npos){
		leftPath = remPath.substr(remPath.find(":") + 1);
	}
	std::cerr << "#" << __func__ << "(): newPath = " << newPath 
		<< " remPath = " << remPath << " retTuple = " << retTuple 
		<< " leftPath = " << leftPath << std::endl;
	newPath += ( ":" + retTuple );
	if(!leftPath.empty()){
		newPath += ( "&" + leftPath );
	}
	std::cerr << "#" << __func__ << "(): pathContext = " << pathContext << std::endl;
	pathContext = newPath;
}

bool pathCounter :: returnBBsPresent()
{
// XXX XXX
	D(std::cerr  << "#" << __func__ << "(): path = " << pathContext << std::endl;)
	if(pathContext.find("&") == std::string::npos)
		return false;
	return true;
}

/* List out all paths in path potential first manner.
 * A context is a tuple with string path and a path potential.
 * We save stuff on a Scheduler only if it isSolvable()
 * */
/** need to add function name as well **/

void pathCounter::enumeratePaths(std::map<std::string, uint64_t > *GbbMap, BasicBlock *currentBB)
{
	D(std::cerr << "#" << __func__ << "():START " << currentBB->getName().data() << std::endl;)
	if(hasFunctionCall(currentBB)){
		// if its first time the basic block is being processed
		// add & and <call1:ret1> tuples to pathContext
		updateCallPathContext(getCallPathContext(currentBB));
		// while there are calls in pathContext in currentBB that are not expanded/explored yet
		// nonProcessedCalls - returns true if there is a fun-bb-callXX on rhs of &
		std::cerr << "#" << __func__ << "():path Context = " << pathContext << std::endl;
		while(nonProcessedCalls(currentBB)){
			// getCallPathContext generates basic Block strings of the form
			// fun1-bb1#call1:fun1-bb1#ret1:fun1-bb1#call2:fun1-bb1#ret2
			std::string callPathCtxt = getCallPathContext(currentBB);
			// goes through pathContext and checks next Called function. returns
			// next called functions entry block - OR if last function call has already been
			// made, just call the non-function-call routine 
			// updates pathContext
			BasicBlock *tempBB = getNextCalledBB(GbbMap,callPathCtxt);
			if(tempBB == nullptr){
				std::cerr << "#" << __func__ << " no more next BB's " << std::endl;
				break;
			}else{
				std::cerr << "#" << __func__ << "(): NextCalledBB present, updated pathContext "
					<< pathContext << std::endl;
				enumeratePaths(GbbMap, tempBB);
				updateRetPathContext();
			}
		}
	}
	std::cerr << "#" << __func__ << "():Done processing All function calls " << std::endl;
	std::cerr << "#" << __func__ << "(): current function = " << currentBB->getParent()->getName().data() <<
			"current BB = " << currentBB->getName().data() << std::endl;
	unsigned numSuccessors = currentBB->getTerminator()-> getNumSuccessors();
	std::cerr << "#" << __func__ << "(): num Successors = " << numSuccessors << std::endl;
		 
	// once function calls have been processed, for the terminal return, go through the
	// successors of the current Basic Block
	if(numSuccessors == 0){
		D(std::cerr << "#" <<__func__ << "():reached terminal path " << pathContext << std::endl;)
		if(!pendingPaths()){
			std::cerr << "#" << __func__ << "():PENDING PATH = FALSE" << std::endl;
			if(returnBBsPresent()){	// reached terminal of sub-function
				D(std::cerr << __func__ << "(): END of Called Function " << std::endl;)
				return;
			}
		//	currentBB = loadContext();
		//	if(currentBB == nullptr){
		//		std::cerr  << "#GETMODEL" << std::endl;
		//		std::cerr << "#TESTING COMPLETE" << std::endl;
		//		return;
		//	}else{		// Scheduler has unexplored paths in Queue
		//		D(std::cerr << __func__ << "():new context loaded " << pathContext << std::endl;
		//		std::cerr << "#" << __func__ << "():new currentBB = " << currentBB->getName().data() << std::endl;)
		//		enumeratePaths(GbbMap, currentBB);
		//	}
		}else{
			std::cerr << "#" << "PENDING PATH = TRUE" << std::endl;
			std::cerr << "#" << __func__ << "(): before updating BB " << pathContext << std::endl;
			currentBB = updatePendingBB();
			std::cerr << "#" << __func__ << "(): after updating BB " << pathContext << std::endl;
			std::cerr << "#" << __func__ << "(): currentBB name " << currentBB->getName().data() << std::endl;
			//return;
			if(currentBB != nullptr){
				std::cerr << "#" << __func__ << "(): successors = 0 , pending path = none " << std::endl;
				std::cerr << "#" << __func__ << "(): currentBB = " << currentBB->getName().data() << std::endl;
				enumeratePaths(GbbMap, currentBB);
			}else{
				getModel();	
				std::cerr << "#" << "No more pending Paths, try to load new context " << std::endl;
			}
		}
	}else if(numSuccessors == 1){
		currentBB = currentBB->getTerminator()->getSuccessor(0);
		if(currentBB == nullptr){
			getModel();
			currentBB = loadContext();
			if(currentBB != nullptr){
				enumeratePaths(GbbMap, currentBB);	
			}
		}else{
			std::cerr << "#" << __func__ << "(): 1 successor, currentBB = " << currentBB->getName().data() << std::endl;
			updatePathContext(currentBB);
			std::cerr << "#"<< __func__ << "():only 1 child, extend only 1 path" << std::endl;
			if(isSolvable()) // move to child basic block
				enumeratePaths(GbbMap, currentBB);
		}
	}else{	// choose max among child Basic Blocks or saved contexts
		std::cerr << "#" << __func__ << "():num successors > 1, current path " << pathContext << std::endl;
		std::cerr << "#" << __func__ << "():currentBB before calling getMaxBB = " << currentBB->getName().data() << std::endl;
		currentBB = getNextMaxBB(currentBB,GbbMap);
		std::cerr << "#" << __func__ << "():path Context " << pathContext << std::endl;
		std::cerr << "#" << __func__ << "():currentBB " << currentBB->getName().data() << std::endl;
		if(isSolvable())
			enumeratePaths(GbbMap, currentBB);
	}
}

void pathCounter :: initializeVariables(Module &M_)
{
	// initialization stuff
        M = &M_;
        C = &(M->getContext());
        DL = M->getDataLayout();
        IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
        VoidTy = Type::getVoidTy(*C);
        VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));
	taintNo = 1;
}

bool pathCounter::runOnModule(Module &M_) {
	std::map< std::string, uint64_t> GbbMap;
	initializeVariables(M_);
	
	for(auto &F_ : M->functions()){
		F = &F_;
		D(if(!F->isDeclaration())
			std::cerr << __func__ << "():FUNCTION():" << F->getName().data() << std::endl;)
	}
	
	D(std::cerr << __func__ << std::endl;)
	// get different possible paths from each basic block.
	getModuleLevelPP(&GbbMap);
	printGbbMap(&GbbMap);

	auto mainF = M->getFunction("main");
	assert(mainF !=nullptr);
	BBLocal = &(mainF->getEntryBlock());
	pathContext += "main-entry";
	std::cerr<< "START ENUMERATION" << std::endl;
	std::cerr << "taintNo = " << taintNo << std:: endl;
	enumeratePaths(&GbbMap, BBLocal);

        return true;
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

uint64_t pathCounter::updateTaint(Value *V) {
   if (V->getType()->isFPOrFPVectorTy()) return 0;
	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)){
		if(CI->getBitWidth() <=64){
			auto integer = CI->getZExtValue();
			if(CMap->find(integer) != CMap->end()){
				return (*CMap)[integer];
			}
		}
	}
	if(TMap->find(V) != TMap->end()){
		(*TMap)[V] = taintNo++;
		return (*TMap)[V];
	}
	return 0;
}

/* 
 * corresponding to the instructions of type
 * %0 = load i32** %a, align 8
 * %5 = load i32* %4, align 4
 * we derive python code in single static assignment form without any phi nodes
 * because each path containing basic blocks have basic blocks predefined, there
 * are no unknown predecessor conditional paths or variables.
 * for each load assignment, the equavalent code generated is as follows:
 * t_a = t_b
 * or
 * p_a = p_b
 * where t_a is temporary variable for a value.
 * p_a is a temporary variable for a pointer.
 * if p_a is a "marked variable" that has not yet been defined, we assign an
 * empty list (or list of lists) to p_a
 * */

void pathCounter::runOnLoad(LoadInst *LI) {
	//std:: cerr << "#" << __func__ << "()"<< std::endl;
	// eg. %0 = load *x
	// get taint of pointer, get taint of LI instruction
	// assign pointer taint to LI instruction
	auto P = LI->getPointerOperand();
	/* print both operand types */
	auto containedType = P->getType()->getContainedType(0);
	if ( containedType -> isPointerTy()){
		std::cerr << "#" << __func__ << "():contained type -- pointer type " << std::endl;
	}
	if ( containedType -> isIntegerTy()){
		std::cerr << "#" << __func__ << "():contained type -- integer type " << std::endl;
	}
	char taintVariable = containedType ->isPointerTy() ? 'p' : 'i';
	auto prevPTaint = getTaint(P);
	assignTaint(LI, P, taintVariable, "LOAD");
	// XXX if P is in symPtr, Taint of V is also in symPtr
	if(taintVariable == 'i'){
		if(std::find(symPtr.begin(), symPtr.end(), getTaint(P)) != symPtr.end()){
			symPtr.push_back(getTaint(LI));
			std::cerr << "p" << getTaint(LI) << " = Int('p" << getTaint(LI) << "')" << std::endl;
			std::cerr << "s.add(p" << getTaint(LI) << " == p" << prevPTaint << ")" << std::endl;
		}	
	}if(taintVariable == 'p'){
		if(std::find(symPtr.begin(), symPtr.end(), getTaint(P)) != symPtr.end()){
			symPtr.push_back(getTaint(LI));
		}
	}
}

// Instrument a single instruction.
void pathCounter::runOnStore(StoreInst *SI) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	// store taint of Value, to taint of PointerAddress
	// get Taint of Value, get taint of Pointer Address
	// store Value of Pointer address, taint of Value

	auto V = SI->getValueOperand();
	
	auto P = SI->getPointerOperand();
	auto containedType = P->getType()->getContainedType(0);
	if ( containedType -> isPointerTy()){
		// XXX store %incdec.ptr, *p. 
		// if incdec.ptr which is "V" is in sym.ptr, then Taint of P also gets added to sym.ptr
		std::cerr << "#" << __func__ << "():contained type -- pointer type " << std::endl;
	}
	if ( containedType -> isIntegerTy()){
		std::cerr << "#" << __func__ << "():contained type -- integer type " << std::endl;
		// XXX if P is sym.ptr, create new Pointer symbolic variable with
		// p = p('new Next Taint'). do s.add(p32 == prev taint of P)
		// do i('new next taint') = i'V'
	}
	char taintVariable = containedType ->isPointerTy() ? 'p' : 'i';
	auto prevPointerTaint = getTaint(P);
	std::cerr << "#" << __func__ <<"():ptr taint before assignTaint " << getTaint(P) << std::endl;
	assignTaint(P, V , taintVariable , "STORE" );
	std::cerr <<"#" << __func__ << "():ptr taint after assignTaint " << getTaint(P) << std::endl;
	if(taintVariable == 'p'){
		if(std::find(symPtr.begin(), symPtr.end(), getTaint(V)) != symPtr.end())
			symPtr.push_back(getTaint(P));
	}else{
		std::cerr << "#" << __func__ << "(): taint Variable i " << std::endl;
		if(std::find(symPtr.begin(), symPtr.end(), prevPointerTaint) != symPtr.end()){
			std::cerr << "#" << __func__ << "(): " << std::endl;
			std::cerr << "p" << getTaint(P) << " = Int('p" << getTaint(P) << "')" << std::endl;
			// Pointer variable remains same, only value got updated
			std::cerr << "s.add(p" << getTaint(P) << " == p" << prevPointerTaint << ")" << std::endl;
			if(std::find(MarkedTaints.begin(), MarkedTaints.end(), prevPointerTaint) != MarkedTaints.end()){
				if(std::find(MarkedTaints.begin(), MarkedTaints.end(), getTaint(P)) == MarkedTaints.end()){
					std::cerr << "#" << __func__ << "():MARKED " << getTaint(P) << std::endl;
					MarkedTaints.push_back(getTaint(P));
				}	
			}
		//XXX
		//	std::cerr << "s.add(i" << getTaint(P) << " == i" << prevPointerTaint << ")" << std::endl;
		}
		std::cerr << "#WRITE i " << getTaint(P) << std::endl;		
	}
}

void pathCounter::markVariable(CallInst *CI){
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	int markerType = 0;	

	auto markedValue = CI->getArgOperand(0);
	uint64_t markedTaintValue;	

	if(TMap->find(markedValue) != TMap->end()){
		markedTaintValue = (*TMap)[markedValue];
	}else{
		markedTaintValue = taintNo++;
		(*TMap)[markedValue] = markedTaintValue;
	}
	std::string calledFunctionName(CI->getCalledFunction()->getName().data());
	if(!calledFunctionName.compare("_mark_int")){
		std::cerr << "i" << (*TMap)[markedValue] << "=" << "Int('i" << (*TMap)[markedValue] <<"')" << std::endl;
		markerType = INT;			
	} else if(!calledFunctionName.compare("_mark_char")){
		std::cerr << "t" << (*TMap)[markedValue] << "=" << "Char('t" << (*TMap)[markedValue] << "')" << std::endl;
		markerType = CHAR;
	} else if(!calledFunctionName.compare("_mark_var_str_arr")){
		std::cerr << "t" << (*TMap)[markedValue] << "=" << "CharArr2D('t" << (*TMap)[markedValue] << "')" << std::endl;
		symPtr.push_back((*TMap)[markedValue]);
		markerType = VAR_STR_ARR;
	} else if(!calledFunctionName.compare("_mark_var_int_arr")){
		std::cerr << "p" << (*TMap)[markedValue] << "=" << "Int('p" << (*TMap)[markedValue] << "')" << std::endl;
		std::cerr << "i" << (*TMap)[markedValue] << "=" << "Int('i" << (*TMap)[markedValue] << "')" << std::endl;
		symPtr.push_back((*TMap)[markedValue]);
		markerType = VAR_INT_ARR;
		if(std::find(MarkedTaints.begin(), MarkedTaints.end(), (*TMap)[markedValue]) == MarkedTaints.end()){
			std::cerr << "#" << __func__ << "():#MARKED " << (*TMap)[markedValue] << std::endl;
			MarkedTaints.push_back((*TMap)[markedValue]);
		}
	} else if(!calledFunctionName.compare("_mark_const_int_arr")){
		//unsigned arrLength = getConstant(CI->getArgOperand(1));
		std::cerr << "p" << (*TMap)[markedValue] << "=" << "Int('p" << (*TMap)[markedValue]  << "')" << std::endl;
		std::cerr << "i" << (*TMap)[markedValue] << "=" << "Int('i" << (*TMap)[markedValue]  << "')" << std::endl;
		symPtr.push_back((*TMap)[markedValue]);
		markerType = CONST_INT_ARR;
		if(std::find(MarkedTaints.begin(), MarkedTaints.end(), (*TMap)[markedValue]) == MarkedTaints.end()){
			std::cerr << "#" << __func__ << "():#MARKED " << (*TMap)[markedValue] << std::endl;
			MarkedTaints.push_back((*TMap)[markedValue]);
		}
	} else {
		std::cerr << "TODO: add type for " << calledFunctionName << "(): function "<< std::endl;
		assert(0);
	}

	markerTypeMap[markedValue] = markerType;

}

bool pathCounter::runOnCall(CallInst *CI) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	if(CI !=nullptr && CI->getCalledFunction() != nullptr && (CI->getCalledFunction()->hasName())){
		std::string callFunctionName(CI->getCalledFunction()->getName().data());
		std:: cerr << "#" << __func__ << "(): Function Called " << callFunctionName << std::endl;
		if(callFunctionName.find("_mark") == std::string::npos){
			// assign all arguments taint values
			auto numArgs = CI->getNumArgOperands();
			D(std::cerr << __func__ << "(): numArgs = " << numArgs << std::endl;)
			for(unsigned i = 0 ; i < numArgs ; i++){
				auto argi = CI->getArgOperand(i);
				auto taint_argi = getTaint(argi);
				if(taint_argi == 0){
					taint_argi = assignTaint(argi);
				}
				//char taintType = (argi->getType()->isPointerTy())? 'p' : 'i';
				//std::cerr << CI->getCalledFunction()->getName().data() << "_arg" << i << "=" << taintType << taint_argi  << std::endl;
				g_argumentTaints.push_back(taint_argi);
				std::cerr << "#" << __func__ << " argument Taint saved " << taint_argi << std::endl;
			}
			if(CI->getCalledFunction()->getReturnType()->isVoidTy()){
				// enter dummy taint as placeholder. we do not write
				// return taint == retvalue for such taints
				g_returnTaintStack.push(0);
				return true;					
			}
			// assign return value taints
			auto retTaint = getTaint(CI);
			if(retTaint == 0){
				retTaint = assignTaint(CI);
			}
			char retTaintType = (CI->getType()->isPointerTy())? 'p' : 'i';
			assert(retTaint);
			if(retTaintType == 'p'){
				std::cerr << retTaintType << retTaint << "=Int('p" << retTaintType << "')" << std::endl;
			}
			std::cerr << "i" << retTaint << "=Int('i" << retTaint << "')" << std::endl;
			std::cerr << "#" << __func__ << "():caller return taint saved " << retTaint << std::endl;
			//std::cerr << CI->getCalledFunction()->getName().data() << "_ret=" << retTaintType << retTaint << std::endl;
			g_returnTaintStack.push(retTaint);
			return true;
		}
	}
	return false;
}

void pathCounter::runOnBranch(BranchInst *BI) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	//int numSuccessors = BI->getNumSuccessors();
	if(BI->isConditional()){
		auto cond = BI->getCondition();
		auto condTaint = getTaint(cond);
		if(condTaint == 0){
			condTaint = assignTaint(cond);
		}
		std::cerr << "#" << __func__ << "():BRANCH_COND " << std::endl ;
		assert(linkBranchIsEmpty());
		linkBranch.taint = condTaint;
		linkBranch.b1.assign(BI->getSuccessor(0)->getName().data());
		linkBranch.b2.assign(BI->getSuccessor(1)->getName().data());
	//	for(auto i = 0; i < numSuccessors ; i++){
	//		auto bbName = BI->getSuccessor(i)->getName().data();
	//		std::cerr << bbName << " ";
	//	}
	//	std::cerr << ")" << std::endl;
	//}else{
	//	std::cerr << "BRANCH_UNCOND " << " " ;
	//	for(auto i = 0 ; i < numSuccessors ; i++)
	//		std::cerr << BI->getSuccessor(i) -> getName().data() << " ";
	//	std::cerr << std::endl;
	}
}

void pathCounter::runOnReturn(ReturnInst *RI) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;

	std::string funName(RI->getParent()->getParent()->getName().data());
	if(!funName.compare("main")){
		return;
	}
	
  if (auto RV = RI->getReturnValue()) {
	auto retTaint = getTaint(RV);
	if(retTaint == 0){
		retTaint = assignTaint(RV);
	}
	g_CalledFunctionReturnTaint = retTaint;
	if(g_returnTaintStack.top() == 0){
		// return from void function
		g_returnTaintStack.pop();
		return;
	}
	if(RV->getType()->isPointerTy()){
		std::cerr << "s.add(p" << g_returnTaintStack.top() << " == p" << g_CalledFunctionReturnTaint << ")" << std::endl;	
	}
	std::cerr << "s.add(i" << g_returnTaintStack.top() << " == i" << g_CalledFunctionReturnTaint << ")" << std::endl;
	std::cerr << "#" << __func__ << " returning from callee, saved taint = " << retTaint << std::endl;
	g_returnTaintStack.pop();
   }
}

void pathCounter::runOnCast(CastInst *I) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	auto operand = I->getOperand(0);
	auto containedType = operand->getType();
	char taintVariable = containedType ->isPointerTy() ? 'p' : 'i';
	assignTaint(I, operand, taintVariable, std::string());
}

void pathCounter::runOnBinary(BinaryOperator *I) {
	std:: cerr  << "#" << __func__ << "()"<< std::endl;
	auto operand0 = I->getOperand(0);
	auto operand1 = I->getOperand(1);
	auto t0 = getTaint(operand0);
	if(t0 == 0){
		t0 = assignTaint(operand0);
	}
	auto t0Ty = operand0->getType()->isPointerTy() ? 'p' : 'i';
	auto t1 = getTaint(operand1);
	if(t1 == 0){
		t1 = assignTaint(operand1);
	}
	auto t1Ty = operand1->getType()->isPointerTy() ? 'p' : 'i';
	auto instructionTaint = updateTaint(I);
	assert(instructionTaint);
	auto instructionTy = (t0Ty == 'i' && t1Ty == 'i') ? 'i' : 'p';
	if(instructionTy == 'i'){ 
		std::cerr  <<  instructionTy << instructionTaint << " = "<< t0Ty 
		<< t0  << getSymbol(I->getOpcodeName())  << " " << t1Ty << t1 << std::endl;
	}else{
		std::cerr << 'p' << instructionTaint << "=Int('p" << instructionTaint << "')" << std::endl;
		std::cerr << "s.add(p" << instructionTaint << " == " << t0Ty << t0
		<< getSymbol(I->getOpcodeName()) << " " << t1Ty << t1 << ")" << std::endl;	
	}
	// if binary operation happens, and one of the operands is a symbolic pointer,
	// the resultant pointer should also be added to symPtr vector
	if((t0Ty == 'p' && std::find(symPtr.begin(),symPtr.end(),t0) != symPtr.end()) ||
		(t1Ty == 'p' && std::find(symPtr.begin(),symPtr.end(),t1) !=symPtr.end())
	){
		symPtr.push_back(instructionTaint);
	}
}

/* XXX do not allocate = 0 if its function entry block and there are 
 * input parameters to the function that are being declared using
 * allocate
 * */

void pathCounter::runOnAlloca(AllocaInst *I, uint64_t allocateCount) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	assert(TMap->find(I) != TMap->end());
	// create new Taint for every time Instruction is called for allocation
	(*TMap)[I] = taintNo++;	
	auto tnum = (*TMap)[I];
	std::cerr << "#" << __func__ << "():Alloca Taint = " << tnum << std::endl;
// XXX HACK - we assume that alloca instructions appear in order of argument parameters.
// For alloca corresponding to non-argument parameters - we initialize taints to 0
// For alloca corresponding to argument parameters, we declare the argument as symbolic
// variables and equate them to g_args taint that we had stored earlier
	std::string bbName = I->getParent()->getName().data();
	std::string funName = I->getParent()->getParent()->getName().data(); 
	if(!bbName.compare("entry") && funName.compare("main") &&
		allocateCount < I->getParent()->getParent()->arg_size()){
			std::cerr << "i" << tnum << "=Int('i" << tnum << "')" << std::endl;
			std::cerr << "s.add(i" << tnum << "== i" << g_argumentTaints[allocateCount] << ")" << std::endl;
	}else{
		if(I->getAllocatedType()->isIntegerTy()){
			std::cerr << "i" << tnum << " = 0" << std::endl;
		}else if(I->getAllocatedType()->isPointerTy()){
			std::cerr << "p" << tnum << " = 0" << std::endl;
		}
	}
}

void pathCounter::runOnGetElementPtr(GetElementPtrInst *I) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	if(I->hasIndices()){
		int integer1 = -1;
		int IndexTaintNo = 0;
		unsigned numIndexes = 0;
		// taint and collect all Indexes
		for(auto op = I->idx_begin(); op!= I->idx_end() ; op++){
			if (ConstantInt *CI = dyn_cast<ConstantInt>(op)){
				if(CI->getBitWidth() <=64){
                			integer1 = CI->getZExtValue();
					if(TMap->find(CI) == TMap->end()){
						std::cerr << "i" << taintNo << " = Int('i" << taintNo << "')" << std::endl;
						std::cerr << "s.add(i" << taintNo << " == " <<integer1 << ")" << std::endl;
						std::cerr << "#CONSTANT TAINT " << taintNo << std::endl; 
						(*TMap)[CI] = taintNo++;
						IndexTaintNo = (*TMap)[CI];
						if(std::find(ConstantTaints.begin(), ConstantTaints.end(), (*TMap)[CI]) == ConstantTaints.end()){
							ConstantTaints.push_back((*TMap)[CI]);
						}
					}
				}else{
					std::cerr << "Found const value with size > 64" << std::endl;
					assert(0);
				}
			}else{
				if(TMap->find(*op)!=TMap->end()){
					IndexTaintNo = (*TMap)[*op];	
				}else{
					(*TMap)[*op] = taintNo++;
					IndexTaintNo = (*TMap)[*op];
				}
			}
			numIndexes ++;
		}
		auto ptrOperand = I->getPointerOperand();
		int arrTaint = (*TMap)[ptrOperand];
		//auto instructionTaint = (*TMap)[I];
		auto instructionTaint = updateTaint(I);
		if(numIndexes == 1){ // 1D Array

			// getElement in python code creates an Integer z3py variable of the name
			// p<arrTaint>t<indexNumber> and assigns it to p<instructionTaint>
			// for every getElementPtr instruction on a 1 D array, we get the following taint format:
			// p45 = p44 + i5
			// i45 = Int('p44i5')

			std::cerr << "namep" << arrTaint << "= get_var_name(p" << arrTaint << "=p" << arrTaint << ")" << std::endl;
			std::cerr << "namei" << IndexTaintNo << "= get_var_name(i" << IndexTaintNo << "=i" << IndexTaintNo << ")" << std::endl;
			std::cerr << "nameinst" << instructionTaint << "=\"i" << instructionTaint << "\"" << std::endl;
			std::cerr << "i" << instructionTaint << " = getElement(p" << arrTaint << ",i" << IndexTaintNo 
				<< ",namep" << arrTaint << ",namei" << IndexTaintNo << ",nameinst" << instructionTaint  << ")" << std::endl;
			std::cerr << "p" << instructionTaint << " = Int('p" << instructionTaint << "')" << std::endl;
			std::cerr << "s.add(p" << instructionTaint << " == p" << arrTaint  << " + i" << IndexTaintNo << ")" << std::endl;
			// pointer address is computed using symbolic pointer 
			// variable add that variable to symPtr as well
			// i28 = getElement(p26,i27)
			// symPtr.add(28)
			if(std::find(MarkedTaints.begin(), MarkedTaints.end(), arrTaint) != MarkedTaints.end()){
				if(std::find(MarkedTaints.begin(), MarkedTaints.end(), instructionTaint) == MarkedTaints.end()){
					std::cerr << "#" << __func__ << "():MARKED " << instructionTaint << std::endl;
					MarkedTaints.push_back(instructionTaint);
				}
			}

			if(std::find(symPtr.begin(), symPtr.end(), arrTaint) != symPtr.end())
				symPtr.push_back(instructionTaint);
		}else{
			std::cerr << __func__ << "():TODO: more than 1D Index" << std::endl;
			assert(0);
		}
	}else{
		std::cerr << "Found getElementPTR with 0 indices " << std::endl;
		assert(0);
	}	
}

void pathCounter::runOnICmp(ICmpInst *I) {
	std:: cerr << "#" << __func__ << "()"<< std::endl;
	auto op1 = I->getOperand(0);
	auto op2 = I->getOperand(1);
	auto Pred = I->getUnsignedPredicate();

	auto t1 = getTaint(op1);
	if(t1 == 0)
		t1 = assignTaint(op1);
	auto t1Type = op1->getType()->isPointerTy() ? 'p' : 'i';

	auto t2 = getTaint(op2);
	if(t2 == 0)
		t2 = assignTaint(op2);
	auto t2Type = op2->getType()->isPointerTy() ? 'p' : 'i';
	auto iTaint = getTaint(I);
	if(iTaint == 0){
		assert(0);
	}

	// should not overwrite existing comparision instruction
	assert(linkComparatorIsEmpty());
	initializeLinkComparator(iTaint, Predicate[Pred], t1, t1Type, t2, t2Type);
				
	//std::cerr << "t" << iTaint << "=(" << Predicate[Pred] << ",t" << t1 << ",t" << t2 << ")" << std::endl;
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
