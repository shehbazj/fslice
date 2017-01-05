#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Analysis/CallGraph.h"
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <iostream>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>

using namespace std;
using namespace llvm;

namespace {
  class pathCounter : public ModulePass {
	public:
	    static char ID;
   		pathCounter() : ModulePass(ID) {}
		virtual bool runOnModule(Module &M) override;
	private:
		Module *M;
		Function *F;
		BasicBlock *BB;
		void runOnFunction();
  };
}

bool pathCounter:: runOnModule(Module &M_)
{
	M  = & M_;		
	for (auto &F_ : M -> functions()){
		F = &F_;
		std::cerr << (F->getName()).data() << std::endl;
		runOnFunction();
	}
	return false;
}

void pathCounter:: runOnFunction()
{
	for(auto &BB : *F)
	{
		auto TermInst = BB.getTerminator();
		std::cerr << "\t"<< BB.getName().data() << " ";
		std::cerr << "\t\t" << TermInst->getOpcodeName(TermInst->getOpcode()) ;
		if(!strcmp(TermInst->getOpcodeName(TermInst->getOpcode()),"br")){
			BranchInst *BI = dyn_cast<BranchInst>(TermInst);
			std::cerr << std::endl<< "Num successors = " << BI->getNumSuccessors() << std::endl;
			for(unsigned i =0 ; i <  BI->getNumSuccessors() ; i++){
				std::cerr << BI->getSuccessor(i)->getName().data() << " ";
			}
			std::cerr << std::endl;
			if(BI->isConditional()){
				std::cerr << " CONDITIONAL " ;
				std::cerr << BI->getCondition()->getName().data() ;
				std::cerr << std::endl;
			}else{
				std::cerr << " UN-CONDITIONAL" << std::endl;
			}
		}
	}
	std::cerr << "\n";
}

char pathCounter::ID = 0;
static RegisterPass<pathCounter> X("pathCounter", "pathCounter", false, false);














