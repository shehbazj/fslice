#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a);
	int i = _mark_int(i);

	if(a[i] == 4){
		;
	}else{
		i++;
		int x = a[i];
		if(a[x] == 3){
			a[x] = a[i];
		}
		if(a[x + i] == a[i]){
			a[i] = 20;
		}else{
			a[x] = 20;
		}
	}
	return 0;
}
