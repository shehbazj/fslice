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

int A(int y)
{
//	int y = 30 + x;
//	if (x ==5 ){
//		y = x * 10;
//	}else{
//		y = x - 5;
//	}
	return y;
}

/*
int B(int x)
{
	int c = 10 + x;
	return c;
}
*/

//int C(int x){
//	if (x == 0){
//		return 1;
//	}else{
//		return 1 + C(x-1);
//	}
//}
/*
int B(int x)
{
	x = A(x);
	if(x < 10){
		x--;
	}else{
		x++;
	}
	x = C(x);
	return A(x);
}
*/
int main()
{
	int p = _mark_int(p);	
	int x;
	x = A(p);
	if (x == 10){
		;
	}
//	int y = B(30);
//	int z = C(40);
	return 0;
}

/* solution
 * 10 
 * 11
 * */
