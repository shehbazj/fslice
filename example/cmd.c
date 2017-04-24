#include<stdio.h>
#include"sym.h"
#include<string.h>

int main()
{
	int argc = _mark_int(argc);
	char **argv = _mark_var_str_arr(argv);

//	if(argc < 3){
//		;
//	}
	if(argv[0][3] == 'p'){
		;
	}
	if(!strcmp(argv[2], "abc")){
		;
	}
//	int x = 1;
//	char **operands = argv + x;
//	char **operand_lim = argv + argc;
//	if (x == argc)
//	    *operand_lim++ = "y";//bad_cast ("y");
//	
//	size_t bufalloc = 0;
//	bool reuse_operand_strings = true;
// 	for (char **operandp = operands; operandp < operand_lim; operandp++)
//	{ 
//		size_t operand_len = strlen (*operandp);
//		bufalloc += operand_len + 1;
//		if (operandp + 1 < operand_lim
//          		&& *operandp + operand_len + 1 != operandp[1])
//		        	reuse_operand_strings = false;
//    	}
}
