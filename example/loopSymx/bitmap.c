
#define ENOSPC 3

int bitmap_alloc(char b[64]) {
    for (unsigned ix = 0; ix < 64; ix++) {
        if (b[ix] != (char)0xff ) {
        	return ix;
        }
    }
    return -ENOSPC;
}
