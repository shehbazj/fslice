#include"headers.h"

void hello(char *str)
{
	printf("%s\n", str);
}

int main(int argc, char *argv[])
{
	char str[20];
	strcpy(str, "hello");
	mark(str);
	hello(str);
}
