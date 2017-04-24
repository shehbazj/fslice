int A(int x)
{
	int y;
	if (x ==5 ){
		y = x * 10;
	}else{
		y = x - 5;
	}
	return y;
}
/*
int C(int x){
	if (x == 0){
		return 1;
	}else{
		return 1 + C(x-1);
	}
}

int B(int x)
{
	x = A(x);
	if(x < 10){
		x--;
	}else{
		x++;
	}
	x = C(x);
	return A(x);
}
*/
int main()
{
	int x = A(20);
	return 0;
}
