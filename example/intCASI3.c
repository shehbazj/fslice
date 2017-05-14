#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
//	CASE 1
/*
	int *p = a;
	p++;
	*p = 10;

	if(a[1] == 10){
		;
	}else{
		;
	}
*/

// 	CASE 2


	int *p = a + 4;
	if(*p == 10){
		;
	}


//	int x;
//	int y;
//	x = 10;
//	y = x;
//	CASE 3
//	int i = _mark_int( i )
//	int *p = a + i;
//	x = *p;

//	x++;
//	y = x;

//	*p++ = 10;
}
