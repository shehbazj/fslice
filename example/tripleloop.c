#include<assert.h>

extern void mark(int );

int main(){
	int i,j,k,n;
	mark(n); // n is the input variable
	for(i=0;i<n;i++)
		;
	for(j=0;j<n;j++)
		;
	for(k=0;k<n;k++)
		;
	if(i+j+k==3000) // C1
		assert(0);
}
