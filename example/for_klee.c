static void mark(int addr);

#include<stdio.h>
//#include<klee/klee.h>

int main()
{
	int i,n, y;
	mark(n);
	//klee_make_symbolic(&n, sizeof n, "n");
	for(i = 0 ; i < n ; i++ )
		;
	if ( i % 2){
		y = 1;
	}else{  
		y = 0;
	}
	return y;
}
