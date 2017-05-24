#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
	int i = 2;

	int x = 5;
	if(a[i] == 4){
		a[i] = x;
	}
	return 0;
}
