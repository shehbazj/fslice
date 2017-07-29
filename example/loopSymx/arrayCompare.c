
#define ENOSPC 3

int arrayCompare(char b[64]) {
    if (b[0] != (char)0xff ) {
      	return 0;
    }
    return -ENOSPC;
}
