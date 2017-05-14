#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<stdint.h>
#include"sym.h"

int main()
{
	int x = _mark_int(x);
	if(x == 1){
		;
	}
	x++;
	if(x == 2){
		;
	}
	return 0;
}

/* unsat
 * unsat
 * 1
 * 2
 * */
