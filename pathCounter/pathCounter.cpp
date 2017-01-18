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

using namespace llvm;


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
  void pushToCallStack(const char *s);
  void printCallTrace();
  void printString(Instruction *I, const char *s);
  void runOnInstructions(void);

  void runOnLoad(BasicBlock *B, LoadInst *LI);
  void runOnStore(BasicBlock *B, StoreInst *SI);
  void runOnCall(BasicBlock *B, CallInst *CI);
  void runOnReturn(BasicBlock *B, ReturnInst *RI);
  void runOnUnary(BasicBlock *B, UnaryInstruction *I);
  void runOnBinary(BasicBlock *B, BinaryOperator *I);
	void runOnICmp(BasicBlock *B, ICmpInst *I);
  void traceFunctionCallGraph();
  void generateConvergenceFactor();
  void generateBranchingFactor();
  void runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI);
	int getCF(BasicBlock *BB);
	int getBF(BasicBlock *BB);

	void displayCFMap();
	void displayBFMap();
	void printStack(std::stack <const char *> *bbStack);
	int  getConvergence(BasicBlock *BB);
	int  getMaxConvergence(TerminatorInst *I);

	void runOnBB(BasicBlock *BB);
	void trackLoad(Value *I);
	void displayMap();
	void generatePaths(std::stack <const char *> *);
	bool isLoopBack(const char *currentBB, std::stack <const char *> *bbStack);
	bool isLoopBackBB(const char *currentBB);
	bool inStack(const char *element, std::stack<const char *> *bbStack);
	const char * getAlternatePath(const char *currentBB, std::stack <const char *> *bbStack);

	void printFunCallFromBB(const char *bbName);
  void track(Value *V);
  int marked(Value *V);

  Value *getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

	std::map<BasicBlock *, int> *CFMap = new std::map <BasicBlock *, int>;
	std::map<BasicBlock *, int> *BFMap = new std::map <BasicBlock *, int>;
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
	std::cerr << F->getName().data() << "():"; 
	std::stack <const char *> temp;
	if(bbS->empty())
		std::cerr << "STACK IS ALREADY EMPTY" << std::endl;
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

int pathCounter :: getBF(BasicBlock *BB)
{
	auto TerminatorInst = BB->getTerminator();
	int numSucc = TerminatorInst->getNumSuccessors();
	if (numSucc == 0){
		BFMap->insert(std::pair<BasicBlock *, int> (BB, 1));
		return 1;
	}else{
		auto TerminatorInst = BB->getTerminator();
		int currentBB_BF = 0;
		for(int i = 0 ; i < numSucc ; i++){
			currentBB_BF += getBF(TerminatorInst->getSuccessor(i));
		}
		BFMap->insert( std::pair<BasicBlock *, int> (BB, currentBB_BF) );
		return currentBB_BF;
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
		std::cerr << it->first->getName().data() << " -> " << it->second << std::endl;
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

bool pathCounter :: isLoopBack(const char *currentBB, std::stack <const char *> *bbStack){
	std::stack <const char *> temp;
	bool bbIsLoopBack = false;
	// removing top element since its currentBB
	auto elem = bbStack->top();
	temp.push(elem);
	bbStack->pop();
	// checking if current BB is already in the stack
	while(!bbStack->empty()){
		auto top = bbStack->top();
		if(top == currentBB){
			bbIsLoopBack = true;
		}
		temp.push(top);
		bbStack->pop();		
	}
	while(!temp.empty()){
		auto top = temp.top();
		bbStack->push(top);
		temp.pop();
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

void pathCounter :: generateBranchingFactor()
{
	auto StartBB = F->begin();
	BFMap = new std::map <BasicBlock *, int>;
	assert(StartBB->getName().data() != NULL);
	int StartBBcount = getBF(StartBB);
	CFMap->insert (std::pair<BasicBlock *, int >  (StartBB,StartBBcount));
	displayBFMap();
	delete BFMap;
	return;
}

bool pathCounter::runOnModule(Module &M_) {
        M = &M_;
        C = &(M->getContext());
        DL = M->getDataLayout();
        IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
        VoidTy = Type::getVoidTy(*C);
        VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));

	// get different function call paths possible.

	for(auto &F_ : M->functions())
	{
		F = &F_;
		if(!F->isDeclaration()){
		//	traceFunctionCallGraph();
		//	generateConvergenceFactor();
			generateBranchingFactor();
		}
	}

	// get different basic block sequence of calls possible.

        // do all tainting and tracking
        //for (auto &F_ : M->functions())
        //{
  	//      F = &F_;
  	//      if(!F->isDeclaration()){
  	//	      runOnFunction();
  	//      }
        //}

        //// link tracking
        //for (auto &F_ : M->functions()) {
  	//      F = &F_;
  	//      for(auto &BB : *F){
  	//	      std::cout << "calling runOnBB for " << F->getName().data() << std::endl;
  	//	      runOnBB(&BB);
  	//      }
        //}

        //// track all dependent variables
        return true;
}

void pathCounter::runOnBB(BasicBlock *BB) {
	for (auto &I: *BB)	{
		if (dyn_cast<LoadInst>(&I)!=nullptr) {
			std::cout << "calling trackLoad " << std::endl;
      trackLoad(&I);
    } /*else if (StoreInst *SI = dyn_cast<StoreInst>(II.I)) {
      runOnStore(II.B, SI);
    } else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(II.I)) {
      runOnIntrinsic(II.B, MI);
    } else if (CallInst *CI = dyn_cast<CallInst>(II.I)) {
			std::cerr << "Call Instruction intercepted " << CI->getCalledFunction()->getName().data() << std::endl;
      runOnCall(II.B, CI);
    } else if (ReturnInst *RI = dyn_cast<ReturnInst>(II.I)) {
      runOnReturn(II.B, RI);
    } else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(II.I)) {
      runOnUnary(II.B, UI);
    } else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(II.I)) {
      runOnBinary(II.B, BI);
    } else if (ICmpInst *IC = dyn_cast<ICmpInst>(II.I)) {
      runOnICmp(II.B, IC);	
    }   */
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
  //printFunctionName(s);
  //pushToCallStack(s);
  //if(strcmp(s,"read_blocks") == 0){
  //  printCallTrace();
  //}else if(strcmp(s,"write_blocks") == 0){
  //  printCallTrace();
  //}
  runOnInstructions();
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
			std::cerr << F->getName().data() << "():"<< B.getName().data() ; std::cerr << " " << &I << std::endl;
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

// Instrument the original instructions.
void pathCounter::runOnInstructions(void) {
  for (auto II : IIs) {
    if (LoadInst *LI = dyn_cast<LoadInst>(II.I)) {
      runOnLoad(II.B, LI);
    } else if (StoreInst *SI = dyn_cast<StoreInst>(II.I)) {
      runOnStore(II.B, SI);
    } else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(II.I)) {
      runOnIntrinsic(II.B, MI);
    } else if (CallInst *CI = dyn_cast<CallInst>(II.I)) {
			std::cerr << "Call Instruction intercepted " << CI->getCalledFunction()->getName().data() << std::endl;
      runOnCall(II.B, CI);
    } else if (ReturnInst *RI = dyn_cast<ReturnInst>(II.I)) {
      runOnReturn(II.B, RI);
    } else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(II.I)) {
      runOnUnary(II.B, UI);
    } else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(II.I)) {
      runOnBinary(II.B, BI);
    } else if (ICmpInst *IC = dyn_cast<ICmpInst>(II.I)) {
      runOnICmp(II.B, IC);	
    }   
  }
}

// Returns the size of a loaded/stored object.
static uint64_t LoadStoreSize(const DataLayout *DL, Value *P) {
  PointerType *PT = dyn_cast<PointerType>(P->getType());
  return DL->getTypeStoreSize(PT->getElementType());
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

// Instrument a single instruction.
void pathCounter::runOnLoad(BasicBlock *B, LoadInst *LI) {
  if (auto TV = getTaint(LI)) {
    auto &IList = B->getInstList();
    auto P = LI->getPointerOperand();
    auto S = LoadStoreSize(DL, P);
    auto A = CastInst::CreatePointerCast(P, IntPtrTy);
		
    auto LoadFunc = CreateFunc(IntPtrTy, "__fslice_load", std::to_string(S),
                               IntPtrTy);
    auto T = CallInst::Create(LoadFunc, {A});
    IList.insert(LI, A);
    IList.insert(LI, T);
    IList.insert(LI, new StoreInst(T, TV));
  }
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
  auto &IList = B->getInstList();
  auto V = SI->getValueOperand();
  auto P = SI->getPointerOperand();
  auto S = LoadStoreSize(DL, P);
  auto A = CastInst::CreatePointerCast(P, IntPtrTy);

  auto T = LoadTaint(SI, V);
  std::vector<Value *> args = {A, T};
  auto StoreFunc = CreateFunc(VoidTy, "__fslice_store", std::to_string(S),
                              IntPtrTy, IntPtrTy);
  IList.insert(SI, A);
  IList.insert(SI, CallInst::Create(StoreFunc, args));
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
  if (!isa<CastInst>(I)) return;
  auto TD = getTaint(I);
  if (!TD) return;
  auto &IList = B->getInstList();
  auto T = LoadTaint(I, I->getOperand(0));
  IList.insert(I, new StoreInst(T, TD));
}

void pathCounter::runOnBinary(BasicBlock *B, BinaryOperator *I) {
  auto TD = getTaint(I);
  if (!TD) return;

  auto &IList = B->getInstList();
  auto LT = LoadTaint(I, I->getOperand(0));
  auto RT = LoadTaint(I, I->getOperand(1));
  auto Op = CreateString(I->getOpcodeName());
  auto Operator = CreateFunc(IntPtrTy, "__fslice_op2", "",
                             Op->getType(), IntPtrTy, IntPtrTy);

  std::vector<Value *> args = {Op, LT, RT};
  auto TV = CallInst::Create(Operator, args);
  IList.insert(I, TV);
  IList.insert(I, new StoreInst(TV, TD));
}

void pathCounter::runOnICmp(BasicBlock *B, ICmpInst *I) {
	auto TD = getTaint(I);
	if(!TD) return;

	auto &IList = B->getInstList();
	auto LT = LoadTaint(I, I->getOperand(0));
	auto RT = LoadTaint(I, I->getOperand(1));
	auto Pred = I->getUnsignedPredicate();

    	auto Predic = ConstantInt::get(IntPtrTy, Pred, false);
	auto Op = CreateFunc(VoidPtrTy, "__fslice_run_on_icmp","", IntPtrTy, IntPtrTy, IntPtrTy);
	std::vector <Value *> args = {LT, RT, Predic};
	auto TV = CallInst::Create(Op, args);
	IList.insert(I, TV);
//	IList.insert(I, TV); 	
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

static RegisterPass<pathCounter> X(
    "pathCounter",
    "pathCounter",
    false,  // Only looks at CFG.
    false);  // Analysis Pass.
