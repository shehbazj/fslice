/* Sequential Loop */

#include<stdbool.h>

extern int GetValue(int x, int y);

bool sequentialLoop() {
	int noOfColumns = 10, noOfRows = 10, i, j;
	for (i = 0; i < noOfRows; i++) {
		j = j+ 5;
	}
	for ( i = 0 ; i < j ; i++){
		i+= 2;
	}
	return true;
}
