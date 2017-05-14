#include<unistd.h>
#include<stdlib.h>
#include"sym.h"

int main()
{
	int y, z;
	int x = _mark_int(x);
	if(x < 5)
	{
		y = x + 1;
	}else{
		y = x  + 2;
	}

	if ( y < 10)
	{
		z = 2;
	}
	else {
		z = 6;
	}
	return 0;
}

/* 5
 * 0
 * unsat
 * 8 
 * */
