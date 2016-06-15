#include "testfs.h"
#include "super.h"
#include "inode.h"
#include "dir.h"
#include "block.h"
#include "bitmap.h"
#include "csum.h"
#include "fslice.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

struct super_block *
testfs_make_super_block(char *file) {
	struct super_block *sb = calloc(1, sizeof(struct super_block));

	if (!sb) {
		EXIT("malloc");
	}
	if ((sb->dev = fopen(file, "w")) == NULL) {
		EXIT(file);
	}
	sb->sb.inode_freemap_start = SUPER_BLOCK_SIZE;
	sb->sb.block_freemap_start = sb->sb.inode_freemap_start +
	INODE_FREEMAP_SIZE;
	sb->sb.csum_table_start = sb->sb.block_freemap_start +
	BLOCK_FREEMAP_SIZE;
	sb->sb.inode_blocks_start = sb->sb.csum_table_start +
	CSUM_TABLE_SIZE;
	sb->sb.data_blocks_start = sb->sb.inode_blocks_start + NR_INODE_BLOCKS;
	sb->sb.modification_time = 0;
	testfs_write_super_block(sb);
	inode_hash_init();
	return sb;
}

void testfs_make_inode_freemap(struct super_block *sb) {
	zero_blocks(sb, sb->sb.inode_freemap_start, INODE_FREEMAP_SIZE);
}

void testfs_make_block_freemap(struct super_block *sb) {
	zero_blocks(sb, sb->sb.block_freemap_start, BLOCK_FREEMAP_SIZE);
}

void testfs_make_csum_table(struct super_block *sb) {
	/* number of data blocks cannot exceed size of checksum table */
	assert(MAX_NR_CSUMS > NR_DATA_BLOCKS);
	zero_blocks(sb, sb->sb.csum_table_start, CSUM_TABLE_SIZE);
}

void testfs_make_inode_blocks(struct super_block *sb) {
	/* dinodes should not span blocks */
	assert((BLOCK_SIZE % sizeof(struct dinode)) == 0);
	zero_blocks(sb, sb->sb.inode_blocks_start, NR_INODE_BLOCKS);
}

/* returns negative value on error 
 file is name of the disk that was given to testfs.
 this function initializes all the in memory data structures maintained by the sb
 block.
 */
int testfs_init_super_block(const char *file, int corrupt,
		struct super_block **sbp) {
	struct super_block *sb = malloc(sizeof(struct super_block));
	char block[BLOCK_SIZE];
	int ret, sock;

	if (!sb) {
		return -ENOMEM;
	}

	if ((sock = open(file, O_RDWR
#ifndef DISABLE_OSYNC
			| O_SYNC
#endif
			)) < 0) {
		return errno;
	} else if ((sb->dev = fdopen(sock, "r+")) == NULL) {
		return errno;
	}

	// sb->dev type = FILE
	// read from sb into block.
	read_blocks(sb, block, 0, 1);
	// copy only 24 bytes from block corresponding to dsuper_block
	_memcpy(&sb->sb, block, sizeof(struct dsuper_block));

	// 64 * 1 * 8
	// bitmap create will return a inode_bitmap structure.
	// and point sb->inode_freemap to that structure.
	// currently the inode bitmap is all 0.
	// at the end of this function, bitmap is created in memory 
	ret = bitmap_create(BLOCK_SIZE * INODE_FREEMAP_SIZE * BITS_PER_WORD,
			&sb->inode_freemap);
	if (ret < 0)
		return ret;
	// bitmap_getdata returns v -> the byte array containing bit info
	// read_blocks reads sb->v into sb at offset freemap_start till 
	// INODE_FREEMAP_SIZE
	// sb is only sent to read_blocks since we need the sb device handle.
	// data from sb->dev is used to populate arg 2  sb->inode_freemap
	read_blocks(sb, bitmap_getdata(sb->inode_freemap),
			sb->sb.inode_freemap_start, INODE_FREEMAP_SIZE);

	ret = bitmap_create(BLOCK_SIZE * BLOCK_FREEMAP_SIZE * BITS_PER_WORD,
			&sb->block_freemap);
	if (ret < 0)
		return ret;
	read_blocks(sb, bitmap_getdata(sb->block_freemap),
			sb->sb.block_freemap_start, BLOCK_FREEMAP_SIZE);
	sb->csum_table = malloc(CSUM_TABLE_SIZE * BLOCK_SIZE);
	if (!sb->csum_table)
		return -ENOMEM;
	read_blocks(sb, (char *) sb->csum_table, sb->sb.csum_table_start,
	CSUM_TABLE_SIZE);
	sb->tx_in_progress = TX_NONE;
	/*
	 inode_hash_init() initializes inode_hash_table of size 256 bytes
	 each entry of the inode table contains a first pointer. each
	 node of the first pointer has a prev pointer and a next pointer.
	 */
	inode_hash_init();
	*sbp = sb;

	return 0;
}

/*
 * from in memory data structure sb, copy dsuper_block
 * into buffer block. then send it for writing to write_blocks
 */
void testfs_write_super_block(struct super_block *sb) {
	char block[BLOCK_SIZE] = { 0 };

	assert(sizeof(struct dsuper_block) <= BLOCK_SIZE);
	_memcpy(block, &sb->sb, sizeof(struct dsuper_block));
	write_blocks(sb, block, 0, 1);
}

void testfs_close_super_block(struct super_block *sb) {
	testfs_tx_start(sb, TX_UMOUNT);
	// write sb->sb of type dsuper_block to disk at offset 0.
	testfs_write_super_block(sb);
	// assume there are no entries in the inode hash table. 
	// delete the 256 hash size inode hash table 
	inode_hash_destroy();
	if (sb->inode_freemap) {
		// write inode map to disk.
		write_blocks(sb, bitmap_getdata(sb->inode_freemap),
				sb->sb.inode_freemap_start, INODE_FREEMAP_SIZE);
		// free in memory bitmap file.
		bitmap_destroy(sb->inode_freemap);
		sb->inode_freemap = NULL;
	}
	if (sb->block_freemap) {
		// write inode freemap to disk
		write_blocks(sb, bitmap_getdata(sb->block_freemap),
				sb->sb.block_freemap_start, BLOCK_FREEMAP_SIZE);
		// destroy inode freemap
		bitmap_destroy(sb->block_freemap);
		sb->block_freemap = NULL;
	}
	testfs_tx_commit(sb, TX_UMOUNT);
	fflush(sb->dev);
	fclose(sb->dev);
	sb->dev = NULL;
	// free in memory data structure sb superblock
	free(sb);
}

static void testfs_write_inode_freemap(struct super_block *sb, int inode_nr) {
	char *freemap;
	int nr;

	assert(sb->inode_freemap);
	freemap = bitmap_getdata(sb->inode_freemap);
	nr = inode_nr / (BLOCK_SIZE * BITS_PER_WORD);
	write_blocks(sb, freemap + (nr * BLOCK_SIZE),
			sb->sb.inode_freemap_start + nr, 1);
}

static void testfs_write_block_freemap(struct super_block *sb, int block_nr) {
	char *freemap;
	int nr;

	assert(sb->block_freemap);
	freemap = bitmap_getdata(sb->block_freemap);
	nr = block_nr / (BLOCK_SIZE * BITS_PER_WORD);
	write_blocks(sb, freemap + (nr * BLOCK_SIZE),
			sb->sb.block_freemap_start + nr, 1);
}

/* return free block number or negative value */
static int testfs_get_block_freemap(struct super_block *sb) {
	u_int32_t index;
	int ret;

	assert(sb->block_freemap);
	ret = bitmap_alloc(sb->block_freemap, &index);
	if (ret < 0)
		return ret;
	testfs_write_block_freemap(sb, index);
	return index;
}

/* release allocated block */
static void testfs_put_block_freemap(struct super_block *sb, int block_nr) {
	assert(sb->block_freemap);
	bitmap_unmark(sb->block_freemap, block_nr);
	testfs_write_block_freemap(sb, block_nr);
}

/* return free inode number or negative value */
int testfs_get_inode_freemap(struct super_block *sb) {
	u_int32_t index;
	int ret;

	assert(sb->inode_freemap);
	ret = bitmap_alloc(sb->inode_freemap, &index);
	if (ret < 0)
		return ret;
	testfs_write_inode_freemap(sb, index);
	return index;
}

/* release allocated inode */
void testfs_put_inode_freemap(struct super_block *sb, int inode_nr) {
	assert(sb->inode_freemap);
	bitmap_unmark(sb->inode_freemap, inode_nr);
	testfs_write_inode_freemap(sb, inode_nr);
}

/* allocate a block and return its block number.
 * returns negative value on error. */
int testfs_alloc_block(struct super_block *sb, char *block) {
	int phy_block_nr;

	phy_block_nr = testfs_get_block_freemap(sb);
	// if error occurred, return -ENOSPC
	if (phy_block_nr < 0)
		return phy_block_nr;
	_bzero(block, BLOCK_SIZE);
	return sb->sb.data_blocks_start + phy_block_nr;
}

/* free a block.
 * returns negative value on error. */
int testfs_free_block(struct super_block *sb, int block_nr) {

	zero_blocks(sb, block_nr, 1);
	block_nr -= sb->sb.data_blocks_start;
	assert(block_nr >= 0);
	testfs_put_block_freemap(sb, block_nr);
	return 0;
}

static int testfs_checkfs(struct super_block *sb, struct bitmap *i_freemap,
		struct bitmap *b_freemap, int inode_nr) {
	struct inode *in = testfs_get_inode(sb, inode_nr);
	int size;
	int size_roundup = ROUNDUP(testfs_inode_get_size(in), BLOCK_SIZE);

	assert((testfs_inode_get_type(in) == I_FILE) || (testfs_inode_get_type(in) == I_DIR));

	/* inode processing */
	bitmap_mark(i_freemap, inode_nr);
	if (testfs_inode_get_type(in) == I_DIR) {
		int offset = 0;
		struct dirent *d;
		for (; (d = testfs_next_dirent(in, &offset)); free(d)) {
			if ((d->d_inode_nr < 0) || (strcmp(D_NAME(d), ".") == 0)
					|| (strcmp(D_NAME(d), "..") == 0))
				continue;
			testfs_checkfs(sb, i_freemap, b_freemap, d->d_inode_nr);
		}
	}
	/* block processing */
	size = testfs_check_inode(sb, b_freemap, in);
	assert(size == size_roundup);
	testfs_put_inode(in);
	return 0;
}

int cmd_checkfs(struct super_block *sb, struct context *c) {
	struct bitmap *i_freemap, *b_freemap;
	int ret;

	if (c->nargs != 1) {
		return -EINVAL;
	}
	ret = bitmap_create(BLOCK_SIZE * INODE_FREEMAP_SIZE * BITS_PER_WORD,
			&i_freemap);
	if (ret < 0)
		return ret;
	ret = bitmap_create(BLOCK_SIZE * BLOCK_FREEMAP_SIZE * BITS_PER_WORD,
			&b_freemap);
	if (ret < 0)
		return ret;
	testfs_checkfs(sb, i_freemap, b_freemap, 0);

	if (!bitmap_equal(sb->inode_freemap, i_freemap)) {
		printf("inode freemap is not consistent\n");
	}
	if (!bitmap_equal(sb->block_freemap, b_freemap)) {
		printf("block freemap is not consistent\n");
	}
	printf("nr of allocated inodes = %d\n",
			bitmap_nr_allocated(sb->inode_freemap));
	printf("nr of allocated blocks = %d\n",
			bitmap_nr_allocated(sb->block_freemap));
	return 0;
}
