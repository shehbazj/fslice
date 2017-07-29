/* IDL that performs data validation in NGenerics 
 * symbolic input - noOfRows, noOfColumns
 * */

#include<stdbool.h>

extern int GetValue(int x, int y);

bool IsSymmetric() {
	int noOfColumns = 10, noOfRows = 10, i, j;
	int a[10][10];
	for (i = 0; i < noOfRows; i++) {
		// IDL. skip loop once.
		// enter loop once.
		for (j = 0; j < i; j++) {
			if (a[i][j] != a[j][i]){
				return false;
			}
		}
	}
	return true;
}
