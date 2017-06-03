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
 * TESTCASE 11 - function call with loops
 * TESTCASE 12 - function call inside a condition
 * TESTCASE 13 - function call inside a loop
 * TESTCASE 14 - function call with if-else
 * */

#include"sym.h"

/*
 * TESTCASE 14 - function call with if-else
 * TESTCASE 6 - multiple calls to same function call with return value
*/

int C(int y)
{
	if(y < 20){
		return y+=20;
	}else{
		return y-=20;
	}
}

int main()
{
	int p = _mark_int(p);	
	int x = C(p);
	return 0;
}
