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

enum operationType {
	INCREMENT,
	DECREMENT,
	UNKNOWNOP,
};

enum condition {
  FCMP_FALSE = 0,
  FCMP_OEQ =  1,
  FCMP_OGT =  2,
  FCMP_OGE =  3,
  FCMP_OLT =  4,
  FCMP_OLE =  5,
  FCMP_ONE =  6,
  FCMP_ORD =  7,
  FCMP_UNO =  8,
  FCMP_UEQ =  9,
  FCMP_UGT = 10,
  FCMP_UGE = 11,
  FCMP_ULT = 12,
  FCMP_ULE = 13,
  FCMP_UNE = 14,
  FCMP_TRUE= 15,
  ICMP_EQ  = 32,
  ICMP_NE  = 33,
  ICMP_UGT = 34,
  ICMP_UGE = 35,
  ICMP_ULT = 36,
  ICMP_ULE = 37,
  ICMP_SGT = 38,
  ICMP_SGE = 39,
  ICMP_SLT = 40,
  ICMP_SLE = 41,
};

// Introduces generic dynamic program slic recording into code.
class loopSymx : public ModulePass {
	public:
		struct iteratorOperation {
			enum operationType oT;
			uint64_t operand;
		};

		struct loopEndCondition {
			bool FIL;
			bool IDL;
			enum condition cond;
			uint64_t startValue;
			uint64_t endValue;	// XXX add more types
			uint64_t loopCount;
			loopEndCondition() : FIL(false), IDL(false){}
		};

		struct pathMeta {
			std:: list <BasicBlock *> *bbList;
			bool loopExists;
			struct iteratorOperation itOp;
			struct loopEndCondition loopEndCond;
			std:: list <char> *branchConditionTree;		
		};

		loopSymx(void);
		virtual bool runOnModule(Module &M) override;
		static char ID;

		std::map<const char *,Value *> StrValues;
		std::list<BasicBlock *> loopEntryBBs;

		// map of loop entry block and list of basic blocks containing loopback path
		// from entry to loop block
		std::map<BasicBlock *, std::list<BasicBlock *> *> loopEntryBlock_loopPath_map;
		std::list <struct pathMeta *> pathList;
	//	std::map<BasicBlock *, std::map<Value *, enum operandType > *> basicBlock_operandType_map;
		std::map<Value *, enum operandType> operandMap;

	private:
		void printBBStack(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB);
		void storeLoopEntryBlockAndLoopPath(std::stack <BasicBlock *> *bbStack, BasicBlock *currentBB);
		bool hasLoop(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack);
		void enumeratePaths(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack);
		void taintVariables(void);
		bool getLoopType(void);			
		void extractIteratorOperation(void);
		void analyseBranches(void);
		//void markInput(Value *V, BasicBlock *BB);
		void markInput(Value *V);
		void addLoopPath(std::stack <BasicBlock *>);
		void deriveIteratorProperties();
	
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
		void displayPathList();
		void displayBBTaintMap();
		void displayStack(std::stack <BasicBlock *> *bbStack);
		void addLoopPath(std::stack <BasicBlock *> *bbStack);
		BasicBlock *getLoopBackBB(std::list <BasicBlock *> *bbList);
		Value *getIteratorLLVMValue(BasicBlock *);
		unsigned getConstant(Value *op);
		void updateLoopPaths();
		uint64_t getStartValue(struct pathMeta *);
		void getOperation(struct pathMeta *, struct iteratorOperation *, struct loopEndCondition *loopEndCond);
		void getEndCondition(BasicBlock *loopEntryBB, struct loopEndCondition *loopEndCond, struct iteratorOperation *);
		BasicBlock *getPenultimateBB(std::list <BasicBlock *> *path);
		void getIteratorOperation(struct BasicBlock *, struct iteratorOperation *, BasicBlock *loopBackBB);

		void setOperator(BinaryOperator *BI, enum operationType *op);
	//	void setOperator(UnaryInstruction *UI, enum operationType *op);
		enum operandType getOperandType(Value *V);
		void setOperandType(Value *V, enum operandType opType);
		void solveConstraints();
		void expandPath(struct pathMeta *pathM);
		void buildBranchConditionTree(struct pathMeta *pathM);
		void listDataFlowConstraints();
		std::list <BasicBlock *> *getLoopBodyPath(std::list <BasicBlock *> *path);

		void copyIteratorMetadata(struct pathMeta *, struct iteratorOperation *, struct loopEndCondition *);

		template <typename T>
			bool isLoopBack(T *currentBB, std::stack <T *> *bbStack);
		template <typename T>
			bool isLoopBack(T *currentBB, std::stack <T *> *bbStack, T *loopBackBB);
		// returns true if path has a loopEntry Basic Block
		bool hasLoopEntryBlock(std::list <BasicBlock *> *path);

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

enum operandType loopSymx:: getOperandType(Value *V)
{
	if(operandMap.find(V)  == operandMap.end()){
		enum operandType opType = UNKNOWN; 
		if(dyn_cast<ConstantInt>(V)){
			opType = CONSTANT;
		}
		operandMap[V] = opType;
		std::cerr << __func__ << "(): " << opType << std::endl;
		return opType;
	} else {
		std::cerr << __func__ << "(): " << operandMap[V] << std::endl;
		return operandMap[V];
	}
}

void loopSymx:: setOperandType(Value *V, enum operandType opType)
{
	if(operandMap.find(V) == operandMap.end()){
		operandMap[V] = opType;
	}else{
		auto op = operandMap[V];
		if(opType > op){
			operandMap[V] = opType;
		}
	}
}

//void loopSymx:: markInput(Value *V, BasicBlock *BB)
void loopSymx:: markInput(Value *V)
{
//	if(basicBlock_operandType_map[BB] == nullptr){
//		basicBlock_operandType_map[BB] = new std::map<Value *, enum operandType >;		
//	}
	//std::cerr << "MARKED INPUT ARGUMENT AS INPUT_DEPENDENT " << BB->getName().data() << V->getName().data() << std::endl;
		// || basicBlock_operandType_map[BB]->find(V)->second != UNKNOWN) { 
//	basicBlock_operandType_map[BB]->insert (std::pair <Value *, enum operandType>(V, INPUT_DEPENDENT));
	operandMap [V] = INPUT_DEPENDENT;
}

void loopSymx:: runOnLoad(LoadInst *LI)
{
	std::cerr << LI->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
	auto P = LI->getPointerOperand();
	enum operandType opType = getOperandType(P);
	
	setOperandType(LI , opType);
}

void loopSymx:: runOnStore(StoreInst *SI)
{				
	auto V = SI->getValueOperand();
	auto P = SI->getPointerOperand();
	
	std::cerr << SI->getParent()->getName().data() << " " << __func__ << "():" << std::endl;
//	std::cerr << __func__ << "():" << std::endl;
	enum operandType opType = getOperandType(V);
//	std::cerr << " operand Type of " << V->getName().data() << " = " << opType << std::endl;
	setOperandType(P , opType);
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
		enum operandType opType = getOperandType(cond);
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
	enum operandType opType = getOperandType(operand);
	setOperandType(I, opType);
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
	enum operandType op1Type = getOperandType(op1);
	enum operandType op2Type = getOperandType(op2);
	if(op1Type == UNKNOWN && op2Type == CONSTANT){
		std::cerr << __func__ << "():Setting Value " << op1-> getName().data() << " as  CONSTANT " << std::endl;
		setOperandType(op1, op2Type);
		setOperandType(I, op2Type);
	}else if(op1Type == INPUT_DEPENDENT){
		setOperandType(I, INPUT_DEPENDENT);
	}else if(op1Type == op2Type){
		setOperandType(I, op1Type);
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
	enum operandType opType = getOperandType(ptrOperand);
	std::cerr << I->getParent()->getName().data() << __func__ << "():" << std::endl;
	for(auto op = I->idx_begin(); op!= I->idx_end() ; op++){
		opType = (getOperandType( op ->get())  == INPUT_DEPENDENT) ? 
				INPUT_DEPENDENT : opType;
	}
	setOperandType(I, opType);
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
		//markInput( &A, &(F->getEntryBlock()));
		markInput( &A);
 	}

	// iterate through each path in pathList

	for(auto &pathTuple : pathList){
		std::cerr << "=== LOOP ===" << std::endl;
		for(auto &BB : *(pathTuple->bbList)){ // get each basic block in each path
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

unsigned loopSymx :: getConstant(Value *op)
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

// helper function to get loopBackBB from a path (basic block that occurs twice)

BasicBlock * loopSymx:: getLoopBackBB(std::list <BasicBlock *> *bbList)
{
	for(auto it1 = bbList->begin() ; it1 != bbList->end() ; it1++){
		for(auto it2 = std::next(it1, 1) ; it2 != bbList->end() ; it2++){
			if ((*it1)->getName().data() == (*it2)->getName().data()){
				std::cerr << __func__ << "(): GOT LoopBack BB " << (*it1)->getName().data() << std::endl;
				return *it1;
			}	
		}
	}
	return nullptr;
}

// helper function get the Value of lvalue of the comparator operation in loopBackBB
Value * loopSymx:: getIteratorLLVMValue(BasicBlock * loopBackBB)
{
	std::map <Value *, Value * > loadInstructionMap;
	for(auto &I : *loopBackBB)
	{
		if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
			loadInstructionMap[LI] = LI->getPointerOperand();
		}
		if (ICmpInst *IC = dyn_cast<ICmpInst>(&I))
		{
 			auto comparedValue = IC->getOperand(0);
			for(auto instVal : loadInstructionMap){
				if(comparedValue == instVal.first){
					return instVal.second;
				}	
			}
		}
	}
	std::cerr << __func__ << "(): no comparision instruction found in basic block " << loopBackBB->getName().data() << std::endl;
	assert(0);
}

// update all paths that have loop Entry blocks repeated twice
// in the entire path

void loopSymx :: updateLoopPaths()
{
	int numLoopEntries = 0;
	for(auto loopEntryBB : loopEntryBBs) {
		for( auto &pathStructure : pathList){
			std::cerr << "NEW PATH " << std::endl;
			auto path = pathStructure->bbList;
			for(auto &pathBB : *path){
				if(pathBB->getName().data() == loopEntryBB->getName().data()){				
					D(std::cerr << "pathBB = " << pathBB->getName().data() << " loopEntry BB = " << loopEntryBB->getName().data() << std::endl;)
					numLoopEntries++;
				}
			}	
			if(numLoopEntries >= 2){
				pathStructure->loopExists = true;
			}		
			numLoopEntries = 0;
		}
	}	
}

uint64_t loopSymx :: getStartValue( struct pathMeta *pathStructure)
{
	uint64_t startVal;
	bool startValueAssigned = false;
	if(pathStructure->loopExists) {
		// START VALUE
		BasicBlock* loopBackBB = getLoopBackBB(pathStructure->bbList);
		assert(loopBackBB != nullptr);
		auto itVal = getIteratorLLVMValue(loopBackBB);
		for(auto &pathBB : *(pathStructure->bbList)) {
			if(pathBB->getName().data() == loopBackBB->getName().data()){
				break;
}
		// from entry in the loop path, check what numerical value is stored in ix
		std::cerr << " processing " << pathBB->getName().data() << " checking value " << loopBackBB->getName().data() << std::endl;
			for(auto &i : *pathBB){
				if (StoreInst *SI = dyn_cast<StoreInst>(&i)) {
					std::cerr << " detected store instruction " << std::endl;
					auto P = SI->getPointerOperand();
					auto V = SI->getValueOperand();
					if ( itVal == P){
						startVal = getConstant(V);								
						startValueAssigned = true;
					}	
				}
			}
		}
		// if no start value, assert
		if(!startValueAssigned){
			std::cerr << "COULD NOT ASSIGN START VALUE " << std::endl;
			assert(0);
		}
	}
	return startVal;
}
/*
void loopSymx :: setOperator(UnaryInstruction *UI, enum operationType *op)
{
	if(UI->getOpcode() == Instruction::Add){
		*op = INCREMENT;
	}else if(UI->getOpcode() == Instruction::Sub) {
		*op = DECREMENT;
	}
}
*/
void loopSymx :: setOperator(BinaryOperator *BI, enum operationType *op)
{
	if(BI->getOpcode() == Instruction::Add){
		*op = INCREMENT;
	}else if(BI->getOpcode() == Instruction::Sub) {
		*op = DECREMENT;
	}
}

/* returns Basic block immediately preceeding loopBackBlock */

BasicBlock * loopSymx::getPenultimateBB(std::list <BasicBlock *> *path)
{
	auto pathBB = path->begin();
	// move iterator to loopEntry position

	BasicBlock* loopBackBB = getLoopBackBB(path);
	assert(loopBackBB != nullptr);
	
	while(*pathBB != loopBackBB){
		pathBB = std::next(pathBB,1);
	}
	pathBB = std::next(pathBB, 1);
	auto prevPathBB = pathBB;
	while(*pathBB != loopBackBB){
		prevPathBB = pathBB;
		pathBB = std::next(pathBB,1);
	}
	if(pathBB == path->end()){
		std::cerr << "COULD NOT FIND LOOPBACK BLOCK IN PATH CONTAINING LOOP" << std::endl;
		assert(0);
	}
	pathBB = prevPathBB;
	return *pathBB;
}

/* in loop path, get the iterator value. check for load, operation and store on the variable. operation could be ADD, SUB, or some other operation. assert if the no OP detected between load and store. this means there is another operation, other than ADD or SUB that has taken place.
*/

void loopSymx:: getIteratorOperation(BasicBlock *pathBB, struct iteratorOperation *itOp, BasicBlock *loopBackBB)
{
	bool processingIterator = false;
	bool validOperation = false;

	uint64_t constOperator;
	enum operationType op;

	auto itVal = getIteratorLLVMValue(loopBackBB);
	auto newitVal = itVal;
	for(auto &I : *pathBB){
		if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
			auto op = LI->getPointerOperand();
			if(op == itVal){
				processingIterator = true;
				newitVal = LI;
			}
		}
        	if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
			auto storeLocationValue = SI->getPointerOperand();
			if(processingIterator && validOperation
				 && storeLocationValue == itVal) {
				// copy valid instruction
	        	        //runOnStore(SI);
	        	        itOp -> oT = op;
				itOp -> operand = constOperator; 
				validOperation = false;
			}
		}
		if (BinaryOperator *BI = dyn_cast<BinaryOperator>(&I)) {
			auto operand0 = BI->getOperand(0);
		        auto operand1 = BI->getOperand(1);
			if(operand0 == newitVal){
				constOperator = getConstant(operand1);								
				std::cerr << __func__ << "(): constOperator = " << constOperator << std::endl;
				validOperation = true;
				setOperator(BI, &op);
			}else if(operand1 == newitVal){
				constOperator = getConstant(operand0);		
				validOperation = true;
			
				setOperator(BI, &op);
			}else if (operand0 == newitVal && operand1 == itVal){
				setOperator(BI, &op);
				std::cerr << "ITERATOR PROCESSED WITH OWN ITERATOR" << std::endl;
				assert(0);		
			}
		}
	}
}

void loopSymx:: getEndCondition(BasicBlock *loopEntryBB, struct loopEndCondition *loopEndCond, struct iteratorOperation *itOp)
{
	for(auto &I : *loopEntryBB)
	{
		if (ICmpInst *IC = dyn_cast<ICmpInst>(&I)) {
        		auto op2 = IC->getOperand(1);
		        auto Pred = IC->getUnsignedPredicate();
				
        		if (dyn_cast<ConstantInt>(op2)){
				loopEndCond-> FIL = true; 
				loopEndCond-> IDL = false;
				loopEndCond-> endValue = getConstant(op2);
			}else{
				loopEndCond-> FIL = false; 
				loopEndCond-> IDL = true;
			}
			loopEndCond -> cond = static_cast<enum condition>(Pred);
			std::cerr << __func__ << "loop End Cond operand = " << loopEndCond -> endValue << " operation operand " <<  itOp-> operand <<  std::endl;
			loopEndCond -> loopCount = abs(loopEndCond-> endValue - loopEndCond-> startValue) / (itOp -> operand);
			std::cerr << "absolute value assigned = " << abs(loopEndCond-> endValue - loopEndCond -> startValue) / (itOp -> operand);
			std::cerr << __func__ << " loop end count is " << loopEndCond -> loopCount << std::endl;
		}
	}
}

// XXX revisit.
// we currently only look at prenultimate basic block, immediately before the loopback block. there, we track the load, store and unary / binary operations.

void loopSymx :: getOperation(struct pathMeta *pathStruct, struct iteratorOperation *itOp , struct loopEndCondition *loopEndCond)
{
	// get loopback block and iterator LLVM Value
	BasicBlock* loopBackBB = getLoopBackBB(pathStruct->bbList);
	assert(loopBackBB != nullptr);

	auto pathBB = getPenultimateBB(pathStruct->bbList);
	getIteratorOperation(pathBB, itOp, loopBackBB);
	std::cerr << __func__ << " itOp operand = " << itOp-> operand << std::endl;
	getEndCondition(loopBackBB, loopEndCond, itOp);
	std::cerr << __func__ << " after end condition itOp operand = " << itOp-> operand << std::endl;
}


void loopSymx :: copyIteratorMetadata(struct pathMeta *pathM, struct iteratorOperation *itOp, struct loopEndCondition *lec)
{
	pathM -> itOp.oT = itOp->oT;
	pathM -> itOp.operand = itOp->operand;
	pathM -> loopEndCond.FIL =  lec->FIL;
	pathM -> loopEndCond.IDL =  lec->IDL;
	pathM -> loopEndCond.cond =  lec->cond;
	pathM -> loopEndCond.startValue =  lec->startValue;
	pathM -> loopEndCond.loopCount = lec->loopCount;
}

// get loop iteartor START value, END value, operation, and loop Count 
// values for FIL or loop type as IDL

void loopSymx:: deriveIteratorProperties()
{
	updateLoopPaths();
	// go through all paths and derive iterator start, end, operation type
	// in loopentry block, mark what is being loaded and compared. this value
	// is the iterator Value.
	
	for( auto pathStructure : pathList) {
		std::cerr << __func__ << " BEGIN " << std::endl;
		if(pathStructure -> loopExists ){ 
			struct iteratorOperation *itOp = new struct iteratorOperation; 
			struct loopEndCondition *loopEndCond = new struct loopEndCondition;
			std::cerr << "PATH Structure Loopexists = " << pathStructure-> loopExists << std::endl;
			uint64_t startVal = getStartValue(pathStructure);
			std::cerr << __func__ << "(): START VALUE = " << startVal << std::endl;
			// OPERATION

			loopEndCond->startValue = startVal;
			getOperation(pathStructure, itOp, loopEndCond);
			
			std::cerr << __func__ << " OPERATION = " << itOp->oT << std::endl;
		
			std::cerr << __func__ << " OPERAND = " << itOp->operand << std::endl;
			std::cerr << __func__ << " LOOP COUNT = " << loopEndCond->loopCount << std::endl;
			copyIteratorMetadata(pathStructure, itOp, loopEndCond);

			// END VALUE
			// get cmp operation. the end value would be iterator < 64 == FALSE.
			// GET LOOP COUNT
			// op value = post value - pre value / operation = 64 - 0 / 1 = 64 times
			// derive loop Count if FIL. mark loop count = INPUT_DEPENDANT if IDL
		}
	}
}

bool loopSymx:: hasLoopEntryBlock(std::list <BasicBlock *> *path)
{
	for(auto elem : *path){
		for(auto loopEntryBB : loopEntryBBs){
			if(!(elem->getName().data() == loopEntryBB->getName().data())){
				std::cerr << " PATH CONTAINS LOOP ENTRY BB " << elem -> getName().data() << std::endl;
				return true;
			}else {
				std::cerr << " XXX " << elem->getName().data()  << " DOES NOT MATCH " << loopEntryBB->getName().data() << std::endl;
			}
		}
	}
	return false;
}

void loopSymx:: addLoopPath(std::stack <BasicBlock *> *bbStack)
{
	std::stack <BasicBlock *> *tmpStack = new std::stack <BasicBlock *>;
	std::list <BasicBlock *> *newList = new std::list <BasicBlock *>;

	std::cerr << __func__ << "()"<< std::endl;
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
	std::list< struct pathMeta *>::iterator it = pathList.end();
	it--;
	struct pathMeta *s = new struct pathMeta;
	s -> loopExists = false;
//	std::cerr << "LOOP EXISTS = " << s->loopExists << std::endl;
	s -> bbList = newList;
	pathList.insert(it,s);
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
	for(auto &it : operandMap){
		std::cerr << it.first->getName().data() << " -- " << it.second  << std::endl;
	}
}

void loopSymx:: displayPathList()
{
	for(auto &it : pathList){
		for(auto &it2 : *(it->bbList)){
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
				std::cerr << "loop Entry BB = " << currentBB->getName().data() << std::endl;
				loopEntryBBs.insert(loopEntryBBs.begin(),currentBB);
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
 * pathList 
 * */

void loopSymx::enumeratePaths(BasicBlock *currentBB, std::stack<BasicBlock *> *bbStack)
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
			enumeratePaths(BB, bbStack);
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
				enumeratePaths(BB, bbStack);
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
				storeLoopEntryBlockAndLoopPath(bbStack, currentBB);
				printBBStack(bbStack, currentBB);
				loopExists = true;
			}
		}
	}
	return loopExists;
}

/* traverse the entire path and extract path between start of loop Entry and
 * of loopEntry
 * */
std::list <BasicBlock *> * loopSymx:: getLoopBodyPath(std::list <BasicBlock *> *path)
{
	BasicBlock *loopBackBB = getLoopBackBB(path);
	
	std::list <BasicBlock *> *loopBodyBBs = new std::list <BasicBlock *>;
	bool append = false;
	for(auto &bb : *path )
	{
		if(bb->getName().data() == loopBackBB->getName().data() ) {
			if(!append){
				append = true;
				loopBodyBBs->push_back(bb);
			}else{
				return loopBodyBBs;
			}
		}
		else if(append){
			loopBodyBBs->push_back(bb);
		}	
	}
	assert(0);	 
}

/* for paths containing loop entry blocks, we elongate the path so that all blocks
 * within the loop segment are repeated till loopentry branch condition gets dissatisfied
 * */

void loopSymx:: expandPath(struct pathMeta *pathM)
{
	std::cerr << __func__ << "():" << std::endl;
	BasicBlock *loopBackBB = getLoopBackBB(pathM -> bbList);
	std::list <BasicBlock *>:: iterator it;
	it = pathM -> bbList->begin();

	// move iterator to the first loopback block
	while(((*it)->getName().data() != loopBackBB->getName().data()) && it!= pathM->bbList->end() ){
		D(std::cerr << __func__ << " bb name " << (*it)->getName().data() << " loopback name " << loopBackBB->getName().data() << std::endl;)
		it++;
	}
	assert(it != pathM->bbList->end()); //COULD NOT FIND loopback BB

	auto loopCount = pathM-> loopEndCond.loopCount;
					
	std::list <BasicBlock *> *loopBodyList = getLoopBodyPath(pathM->bbList);

	std::cerr << "Loop body contents " << std::endl;
	for(auto &it : *loopBodyList){
		std::cerr << it->getName().data() << std::endl;
	}
	std::cerr << "loopcount = " << loopCount << std::endl;
	for(unsigned i=0; i < loopCount -1 ; i++){
		pathM->bbList->insert(it, loopBodyList->begin(), loopBodyList->end());
	}
	std::cerr << "Extended Path " << std::endl;
	for(auto &it : *(pathM->bbList)){
		std::cerr << it->getName().data() << std::endl;
	}
}

/* we generate a path constraint list for the expanded paths containing bit trails of 
 * 0 and 1. This signifies which branch was taken after reaching a certain path
 * */

void loopSymx:: buildBranchConditionTree(struct pathMeta *pathM)
{
	// iterate through path. if you find a branch condition, check which of the
	// children are explored.	
	pathM -> branchConditionTree = new std::list<char>;
	for( std::list<BasicBlock *>::iterator bb_it = pathM->bbList->begin();bb_it != pathM->bbList->end() ; std::advance(bb_it,1))
	{
		if((*bb_it)->getTerminator()->getNumSuccessors() == 2){
			auto nextbb = std::next(bb_it,1);
			if((*bb_it)->getTerminator() -> getSuccessor(0) == *nextbb){
				pathM->branchConditionTree->push_back('T');
			}else {
				pathM->branchConditionTree->push_back('F');
			}
		}else if((*bb_it)->getTerminator()->getNumSuccessors() > 2){
			assert(0);	
		}
	}
}

/* start from entry block, go instruction by instruction marking the input blocks and
 * printing the other instruction equavalent taints to be processed later by Z3 python
 * API
 * */

void loopSymx:: listDataFlowConstraints()
{

}

// expand all loop based paths.
// go through entire basic block and for each instruction write down the data flow.
// for blocks having multiple successors, we add constraint that makes control flow
// move from parent to the child in the expected path.
// for loop constructs, control flow goes to loop entry block until loop entry branch
// condition is negated

void loopSymx :: solveConstraints()
{
	for(auto &pathM : pathList){
		std::cerr << __func__ << "(): PATH " << std::endl;
		for(auto &it : *(pathM->bbList)){
			std::cerr << it->getName().data() << std::endl;
		}

		if(pathM->loopExists) {
			expandPath(pathM);
		}
		buildBranchConditionTree(pathM);
		for(auto bb_it : *(pathM->branchConditionTree) ) {
			std::cerr << bb_it << std::endl;
		}
		//listDataFlowConstraints();
	}
}

bool loopSymx::runOnModule(Module &M_) {
	M = &M_;
	for(auto &F_ : M->functions()){
		F = &F_;
		std::stack <BasicBlock *> *bbStack = new std::stack <BasicBlock *>;
		if(!F->isDeclaration()){
			enumeratePaths(&F->getEntryBlock(), bbStack);
			displayPathList();
			taintVariables();
			deriveIteratorProperties();

		// TODO
		// get Loop Dependent variables, get loop dependent branches, derive iteration count to evaluate
		// loop dependent branches to true.
		//
		// TODO
		// IDL - how do you get minimum iterations?
		//
			solveConstraints();
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
