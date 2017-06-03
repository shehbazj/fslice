#include "sym.h"

int main()
{
	int x, y, i;
	int n = _mark_int(n);
	x = n  - 2;
	for(i = 0; i < n ; i++){
		if(x < 5){
			x++;
		}else{
			x--;
		}
	}
	y = x;
	return 0;
}
/* 1
 * 0
 * unsat
 * without loop extension
 * */
