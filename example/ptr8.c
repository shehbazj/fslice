#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
	int i = _mark_int(i);

	int x = a[i+1];
	if(a[i] == 4){
		a[i] = x;
		if(a[i] == 10){
			;
		}
	}
	return 0;
}
