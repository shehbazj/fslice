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

#include"sym.h"

// TESTCASE 3 - function call with 2 parameters

int A(int y, int z)
{
	return y + z;
}

int main()
{
	int p = _mark_int(p);	
	int x;
	int q = 20;
	x = A(p, q);
	if (x == 10){
		;
	}
	return 0;
}
/* -10
 * not -10
 * */
