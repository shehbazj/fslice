#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_const_int_arr( a ,5);
	int i = 2;

	if(a[i] == 4){
		;
	}else{
		i++;
		if(a[i] == 4){
			a[i] = 5;
		}
	}
	return 0;
}
