#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
//	CASE 3
	int i = _mark_int( i );
	int *p = a + i;
	int x,y;
	x = *p;

	x++;
	y = x;

	*p++ = y;
	if(y == 12){
		;
	}else{
		;
	}
}
