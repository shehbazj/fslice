#include<stdio.h>
#include "sym.h"

int main()
{
	int *a = _mark_var_int_arr( a );
	int *p1, *p2, *p3;	
	int i = _mark_int( i);

	p1 = a + 4;
	p2 = a + 1;
	p3 = p2 + i;

	if(p1 == p3){
			if(*p1 == *p2){
				;
			}
	}else{
			if(*p1 + 4 == *p3++){
				p3 = p1;
			}
	}
	return 0;
}
