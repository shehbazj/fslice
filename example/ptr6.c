#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
//	CASE 3
	int i = _mark_int( i );
	int *p = a;
	int y;
	i = *p;
	y = i + 1;
	p++;
	*p = y;
	if(*p == 12 ){
		;
	} 
}
