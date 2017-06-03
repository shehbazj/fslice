/* TESTCASE 1 - function call with no parameters
 * TESTCASE 2 - function call with 1 parameter
 * TESTCASE 3 - function call with 2 parameters
 * TESTCASE 4 - without return value
 * TESTCASe 5 - multiple calls to same function call - no return value
 * TESTCASE 6 - multiple calls to same function call - return value
 * TESTCASE 7 - 3 function calls
 * TESTCASE 8 - recursion <TERMINATE!>
 * TESTCASE 9 - pointer argument
 * TESTCASE 10 - return pointer
 * */

/* Function Call with 0 parameters */

#include"sym.h"

int voidFunction()
{
	return 30;
}

int main()
{
	int p = _mark_int(p);	
	int x;
	x = voidFunction();
	int y = x + p;
	if (y == 10){
		;
	}
	return 0;
}

/* solution 
 * -20
 *  -19
 * */
