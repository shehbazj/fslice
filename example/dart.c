#include<stdlib.h>

void top(char input[4])
{
	int cnt=0;
	if (input[0] == 'b') cnt++;
	if (input[1] == 'a') cnt++; else return;
	if (input[2] == 'd') cnt++;
	if (input[3] == '!') cnt++; else return;
	if (cnt >= 3) abort();	// error	
}

int main()
{
	const char input[4] = {'b', 'a', 'd', 'x'};
	top(input);
	return 0;
}
