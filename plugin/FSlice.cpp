/* Copyright 2015 Peter Goodman (peter@trailofbits.com), all rights reserved. */

#define DEBUG_TYPE "FSlice"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <iostream>
#include <map>
#include <vector>
#include <string>


// #define DEBUG
#ifdef DEBUG
#  define D(x) x
#else
#  define D(x)
#endif


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
class FSliceModulePass : public ModulePass {
 public:
  FSliceModulePass(void);

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

  void runOnFunction(const char *);
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
  void runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI);

  Value *getTaint(Value *V);
  Value *LoadTaint(Instruction *I, Value *V);

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

  int numVSets;
};

FSliceModulePass::FSliceModulePass(void)
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

bool FSliceModulePass::runOnModule(Module &M_) {
  M = &M_;
  C = &(M->getContext());
  DL = M->getDataLayout();
  IntPtrTy = Type::getIntNTy(*C,  DL->getPointerSizeInBits());
  VoidTy = Type::getVoidTy(*C);
  VoidPtrTy = PointerType::getUnqual(IntegerType::getInt8Ty(*C));

  for (auto &F_ : M->functions()) {
    F = &F_;
    if (F->isDeclaration()) {
      if (F->getName() == "memset") {
        F->setName("__fslice_memset");
      } else if (F->getName() == "memcpy") {
        F->setName("__fslice_memcpy");
      } else if (F->getName() == "memmove") {
        F->setName("__fslice_memmove");
      } else if (F->getName() == "strcpy") {
        F->setName("__fslice_strcpy");
      } else if (F->getName() == "bzero") {
        F->setName("__fslice_bzero");
      } else if (F->getName() == "malloc") {
        F->setName("__fslice_malloc");
      } else if (F->getName() == "calloc") {
        F->setName("__fslice_calloc");
      } else if (F->getName() == "mark") {
	F->setName("__fslice_mark");
      } else if (F->getName() == "strlen") {
	F->setName("__fslice_strlen");
//	printFunctionName(F->getName().data());
      }
    } else {
        runOnFunction(F->getName().data());
    }   
  }
  return true;
}

// Instrument every instruction in a function.
void FSliceModulePass::runOnFunction(const char* s) {
  numVSets = 0;
  collectInstructions();
  initVSets();
  combineVSets();
  labelVSets();
  allocaVSetArray();
  runOnArgs();
  printFunctionName(s);
  pushToCallStack(s);
  if(strcmp(s,"read_blocks") == 0){
    printCallTrace();
  }else if(strcmp(s,"write_blocks") == 0){
    printCallTrace();
  }
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
void FSliceModulePass::collectInstructions(void) {
  for (auto &B : *F) {
    for (auto &I : B) {
      IIs.push_back({&B, &I});
    }
	D(std::cerr << "Basic Block " << B.getName().data() << IIs.size() << std::endl; )
  }
}

// Group the values (instructions, arguments) into sets where each set
// represents a logical variable in the original program.
void FSliceModulePass::initVSets(void) {
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
	D(std::cerr << "VtoVSet Size = " << VtoVSet.size() << std::endl;)
}

// Combine value sets.
// go through each of the Instructions. Check the incoming 
// nodes of each of the instructions. If the incoming vertex is
// not from a constant, combine the incoming value with the Vset corresponding
// to the Instruction that you just read.
void FSliceModulePass::combineVSets(void) {
  for (auto &II : IIs) {
    auto I = II.I;
    auto VSet = VtoVSet[I];
    if (PHINode *PHI = dyn_cast<PHINode>(I)) {
	D(std::cerr << "Detected phi node " << II.B->getName().data() << std::endl;)
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
void FSliceModulePass::combineVSet(VSet *VSet1, VSet *VSet2) {
  VSet1 = getVSet(VSet1);
  VSet2 = getVSet(VSet2);
  if (VSet1 < VSet2) {
    VSet2->rep = VSet1;
  } else if (VSet1 > VSet2){
    VSet1->rep = VSet2;
  }
}

// Get the representative of this VSet. Implements union-find path compression.
VSet *FSliceModulePass::getVSet(VSet *VSet) {
  while (VSet->rep != VSet) {
    VSet = (VSet->rep = VSet->rep->rep);
  }
  return VSet;
}

// Assign array indices to each VSet. This labels all variables from 0 to N-1.
void FSliceModulePass::labelVSets(void) {
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
void FSliceModulePass::allocaVSetArray(void) {
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
	D(std::cerr << "numVsets = " << numVSets << " IdxToVar Size = " << IdxToVar.size() << std::endl;)
  AfterAlloca = &FirstI;
}

// Instrument the arguments.
void FSliceModulePass::runOnArgs(void) {
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

// Insert function to print Function Name.
void FSliceModulePass::printFunctionName(const char * s){
	if(!AfterAlloca) return;
	if(!s) return;
	auto &IList = AfterAlloca->getParent()->getInstList();
  	auto FunName = CreateString(s);
	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", FunName->getType());
	auto PR = CallInst::Create(PrintFunc, {FunName});
	IList.insert(AfterAlloca, PR); 	
}

// Insert function to print Function Name.
void FSliceModulePass::pushToCallStack(const char *s){
	if(!AfterAlloca) return;
	auto &IList = AfterAlloca->getParent()->getInstList();
  	auto FunName = CreateString(s);
	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_push_to_call_stack","", FunName->getType());
	auto PR = CallInst::Create(PrintFunc, {FunName});
	IList.insert(AfterAlloca,PR); 	
}

// Print call Trace for a function.
void FSliceModulePass::printCallTrace() {
	if(!AfterAlloca) return;
	auto &IList = AfterAlloca->getParent()->getInstList();
	//auto Arglist = CreateString(bt.c_str());
	//auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", Arglist->getType());
	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_call_trace","");
	auto PR = CallInst::Create(PrintFunc);
	IList.insert(AfterAlloca, PR); 	
}

// Insert function to print a string before I.
void FSliceModulePass::printString(Instruction *I, const char * s){
	return;
	if(!AfterAlloca) return;
	if(!s) return;
	auto &IList = AfterAlloca->getParent()->getInstList();
  	auto FunName = CreateString(s);
	auto PrintFunc = CreateFunc(VoidPtrTy, "__fslice_print_func","", FunName->getType());
	auto PR = CallInst::Create(PrintFunc, {FunName});
	IList.insert(I, PR); 	
}

// Instrument the original instructions.
void FSliceModulePass::runOnInstructions(void) {
  for (auto II : IIs) {
    if (LoadInst *LI = dyn_cast<LoadInst>(II.I)) {
      runOnLoad(II.B, LI);
    } else if (StoreInst *SI = dyn_cast<StoreInst>(II.I)) {
      runOnStore(II.B, SI);
    } else if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(II.I)) {
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
    }
  }
}

// Returns the size of a loaded/stored object.
static uint64_t LoadStoreSize(const DataLayout *DL, Value *P) {
  PointerType *PT = dyn_cast<PointerType>(P->getType());
  return DL->getTypeStoreSize(PT->getElementType());
}

// Instrument a single instruction.
void FSliceModulePass::runOnLoad(BasicBlock *B, LoadInst *LI) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
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

// Get taint value of V if it already exists using getTaint.
// If taint for V does not exist, create a taint for the value V
// most probably V is a constant. If it is a constant integer value
//  it would load it from fslice_value.
Value *FSliceModulePass::LoadTaint(Instruction *I, Value *V) {
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
void FSliceModulePass::runOnStore(BasicBlock *B, StoreInst *SI) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
  auto &IList = B->getInstList();
  auto V = SI->getValueOperand();
  auto P = SI->getPointerOperand();
  auto S = LoadStoreSize(DL, P);
  auto A = CastInst::CreatePointerCast(P, IntPtrTy);

  auto T = LoadTaint(SI, V);
  std::vector<Value *> args = {A, T};
  auto StoreFunc = CreateFunc(VoidTy, "__fslice_store", std::to_string(S),
                              IntPtrTy, IntPtrTy);
  auto T2 = getTaint(P);
	if(T2 == nullptr){
		D(std::cerr << __func__ << "():Pointer operand is null" << std::endl;)
;
	}else{
		D(std::cerr << __func__ << "():Pointer operand not null" << std::endl;)
;
	}
  IList.insert(SI, A);
  IList.insert(SI, CallInst::Create(StoreFunc, args));
}

void FSliceModulePass::runOnCall(BasicBlock *B, CallInst *CI) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
  auto &IList = B->getInstList();
  auto StoreFunc = CreateFunc(VoidTy, "__fslice_store_arg", "",
                              IntPtrTy, IntPtrTy);
  auto i = 0UL;
  for (auto &A : CI->arg_operands()) {
    std::vector<Value *> args = {ConstantInt::get(IntPtrTy, i++, false),
                                 LoadTaint(CI, A.get())};
    IList.insert(CI, CallInst::Create(StoreFunc, args));
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

void FSliceModulePass::runOnReturn(BasicBlock *B, ReturnInst *RI) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
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


void FSliceModulePass::runOnUnary(BasicBlock *B, UnaryInstruction *I) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
  if (!isa<CastInst>(I)) {
	return;
  }
  auto TD = getTaint(I);
  if (!TD) {
	 return;
  }
  auto &IList = B->getInstList();
  auto T = LoadTaint(I, I->getOperand(0));
  IList.insert(I, new StoreInst(T, TD));
}

void FSliceModulePass::runOnBinary(BasicBlock *B, BinaryOperator *I) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
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

void FSliceModulePass::runOnICmp(BasicBlock *B, ICmpInst *I) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
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

void FSliceModulePass::runOnIntrinsic(BasicBlock *B, MemIntrinsic *MI) {
	D(std::cerr << __func__ << "(): Basic Block " << B->getName().data() << std::endl;)
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

Value *FSliceModulePass::getTaint(Value *V) {
  if (V->getType()->isFPOrFPVectorTy()) return nullptr;
  if (VtoVSet.count(V)) {
    D(std::cerr << __func__ << "(): got instruction from VtoVSet" << std::endl;)
    auto index = VtoVSet[V]->index;
    if (-1 == index) {
	D(std::cerr << "Index is -1, returning NULL" << std::endl;)
	return nullptr;
	}
	D(std::cerr << "returning value from IdxToVar at index " << index << std::endl;)
    return IdxToVar[index];
  } else {
	D(std::cerr << __func__ << "(): fetched instruction from IdxToVar" << std::endl;)
    auto it = std::find(IdxToVar.begin(), IdxToVar.end(), V);
    if (it == IdxToVar.end()){
	D(std::cerr << "returning null Pointer" << std::endl;)
	 return nullptr;
	}
	D(std::cerr << "returning IdxToVar value " << it - IdxToVar.begin() << std::endl;)
    return *it;
  }
}

char FSliceModulePass::ID = '\0';

static RegisterPass<FSliceModulePass> X(
    "fslice",
    "File system runtime program slicing pass.",
    false,  // Only looks at CFG.
    false);  // Analysis Pass.
