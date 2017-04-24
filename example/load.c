static void _mark(int addr);

int main()
{
	int x,y,z;
	_mark(x);
	y = x;
	z = y;	
	return 0;
}
