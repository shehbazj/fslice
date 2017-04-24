#include<stdio.h>
#define bool unsigned
#define false 0
#define true 1

void test(int n)
{
	int a,b,i;
	bool loop_complete = false;
	for(i=n;i>0;i--){
		assert(i>0);
		// interval i [n to 0]
		if(i==500){
			assert(i==500);
			a=1;
		}else{
			assert(i!=500);
		}
		if(i==1000){
			assert(i==1000);
			a=2;
		}else{
			assert(i!=1000);
		}
	}
	if(i<=0){
		loop_complete = true;
	}
	if(loop_complete){
		assert(i<=0);
	}

	if(a==0){
		assert(a==0);
		;
	}else{
		assert(a!=0);
	}
	if(a==1){
		assert(a==1);
		;
	}else{
		assert(a!=1);
		}
	if(a==2){
		assert(a==2);
		b=5;
	}else{
		assert(a!=2);
	}
}

int main()
{
	int n;
	test(n);
}
