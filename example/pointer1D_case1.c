#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
//	CASE 1

	int *p = a;
	p++;
	*p = 10;

	if(a[1] == 10){
		;
	}else{
		;
	}
}
