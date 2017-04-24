#include "headers.h"

int main(int argc, char *argv[])
{
	char new[20];
	mark(new);
	if(strlen(new) < 5){
		printf("less than 5 %lu\n", strlen(new));
	}else{
		printf("greater than 5 %lu\n", strlen(new));
	}
		return 0;
}
