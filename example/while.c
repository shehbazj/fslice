#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<stdint.h>
#include"sym.h"

int main()
{
	int i;
	int n;
//	_mark(INT, n);
	i = 0;
	do{
	 	i++;
	}while( i < n );
	return 0;
}
