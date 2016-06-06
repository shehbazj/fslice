#include "testfs.h"
#include "inode.h"
#include "dir.h"
#include "tx.h"
#include "fslice.h"

int cmd_cat(struct super_block *sb, struct context *c) {
	char *buf;
	int inode_nr;
	struct inode *in;
	int ret = 0;
	int sz;
	int i;

	if (c->nargs < 2) {
		return -EINVAL;
	}

	for (i = 1; ret == 0 && i < c->nargs; i++) {
		inode_nr = testfs_dir_name_to_inode_nr(sb, &c->cur_dir, c->cmd[i]);
		if (inode_nr < 0)
			return inode_nr;
		in = testfs_get_inode(sb, inode_nr);
		if (testfs_inode_get_type(in) == I_DIR) {
			ret = -EISDIR;
			goto out;
		}
		sz = testfs_inode_get_size(in);
		if (sz > 0) {
			buf = malloc(sz + 1);
			if (!buf) {
				ret = -ENOMEM;
				goto out;
			}
			testfs_read_data(in, 0, buf, sz);
			buf[sz] = 0;
			printf("%s\n", buf);
			free(buf);
		}
		out: testfs_put_inode(in);
	}

	return ret;
}

int cmd_catr(struct super_block *sb, struct context *c) {
	char *cdir = ".";
	int inode_nr;
	struct inode *in, *tmp_inode;
	int offset = 0;
	struct dirent *d;
	int ret = 0;
	int sz;
	char *buf;

	if (c->nargs > 2) {
		return -EINVAL;
	}

	if (c->nargs == 2) {
		cdir = c->cmd[1];
	}
	assert(c->cur_dir);

	/* Store the current directory. */
	tmp_inode = c->cur_dir;

	/* Get the inode number that corresponds to the provided
	 * directory name. If no directory name is specified, search
	 * for the current directory. */
	inode_nr = testfs_dir_name_to_inode_nr(sb, &c->cur_dir, cdir);
	if (inode_nr < 0)
		return inode_nr;

	/* Get the corresponding inode object. */
	in = testfs_get_inode(sb, inode_nr);

	for (; (d = testfs_next_dirent(in, &offset)); free(d)) {
		struct inode *cin;

		if (d->d_inode_nr < 0)
			continue;

		if((strcmp(D_NAME(d), ".") != 0) && (strcmp(D_NAME(d), "..") != 0)) {
			cin = testfs_get_inode(testfs_inode_get_sb(in), d->d_inode_nr);

			if (testfs_inode_get_type(cin) == I_DIR) {
				c->cur_dir = cin;
				ret = cmd_catr(sb, c);
				if(ret < 0) {
					testfs_put_inode(cin);
					goto out;
				}
				c->cur_dir = tmp_inode;
			}
			else {
				printf("%s:\n", D_NAME(d));
				sz = testfs_inode_get_size(cin);
				if (sz > 0) {
					buf = malloc(sz + 1);
					if (!buf) {
						testfs_put_inode(cin);
						ret = -ENOMEM;
						goto out;
					}
					testfs_read_data(cin, 0, buf, sz);
					buf[sz] = 0;
					printf("%s\n", buf);
					free(buf);
				}
			}
			testfs_put_inode(cin);
		}
	}
	out: testfs_put_inode(in);

	return 0;
}

int cmd_write(struct super_block *sb, struct context *c) {
	int inode_nr;
	struct inode *in;
	int size;
	int ret = 0;
	char *filename = NULL;
	char *content = NULL;

	if (c->nargs != 3) {
		return -EINVAL;
	}

	filename = c->cmd[1];
	content = c->cmd[2];

	inode_nr = testfs_dir_name_to_inode_nr(sb, &c->cur_dir, filename);
	if (inode_nr < 0)
		return inode_nr;
	in = testfs_get_inode(sb, inode_nr);
	if (testfs_inode_get_type(in) == I_DIR) {
		ret = -EISDIR;
		goto out;
	}
	size = strlen(content);
	testfs_tx_start(sb, TX_WRITE);
	ret = testfs_write_data(in, 0, content, size);
	if (ret >= 0) {
		testfs_truncate_data(in, size);
	}
	testfs_sync_inode(in);
	testfs_tx_commit(sb, TX_WRITE);
	out: testfs_put_inode(in);
	return ret;
}

int cmd_owrite(struct super_block *sb, struct context *c) {
	int inode_nr;
	struct inode *in;
	int size;
	int ret = 0;
	long offset;
	char *filename = NULL;
	char *content = NULL;
	char *temp = NULL;

	if (c->nargs != 4)
		return -EINVAL;

	filename = c->cmd[1];
	content = c->cmd[3];
	offset = strtol(c->cmd[2], &temp, 10);
	if (*temp != '\0')
		return -EINVAL;

	/* Verify the validity of the specified offset. */
	if(offset < 0)
		return -EINVAL;

	inode_nr = testfs_dir_name_to_inode_nr(sb, &c->cur_dir, filename);
	if (inode_nr < 0)
		return inode_nr;
	in = testfs_get_inode(sb, inode_nr);
	if (testfs_inode_get_type(in) == I_DIR) {
		ret = -EISDIR;
		goto out;
	}
	size = strlen(content);
	testfs_tx_start(sb, TX_WRITE);
	ret = testfs_write_data(in, offset, content, size);
	if (ret >= 0) {
		testfs_truncate_data(in, size + offset);
	}
	testfs_sync_inode(in);
	testfs_tx_commit(sb, TX_WRITE);
	out: testfs_put_inode(in);
	return ret;
}

int cmd_oread(struct super_block *sb, struct context *c) {
	int inode_nr;
	struct inode *in;
	int size, file_size;
	int ret = 0;
	long offset;
	char *buf;
	char *temp = NULL;

	if (c->nargs != 4)
		return -EINVAL;

	offset = strtol(c->cmd[2], &temp, 10);
	if (*temp != '\0')
		return -EINVAL;

	size = strtol(c->cmd[3], &temp, 10);
	if (*temp != '\0')
		return -EINVAL;

	/* Verify the validity of the specified arguments. */
	if(offset < 0 || size < 0)
		return -EINVAL;

	if(size == 0)
		return ret;

	inode_nr = testfs_dir_name_to_inode_nr(sb, &c->cur_dir, c->cmd[1]);
	if (inode_nr < 0)
		return inode_nr;

	in = testfs_get_inode(sb, inode_nr);
	if (testfs_inode_get_type(in) == I_DIR) {
		ret = -EISDIR;
		goto out;
	}

	file_size = testfs_inode_get_size(in);
	if (file_size > 0) {

		/* Verify that the specified offset is valid. */
		if(offset >= file_size) {
			ret = -EINVAL;
			goto out;
		}

		/* In case the specified arguments exceed the available offsets
		 * inside the file, truncate the specified size. */
		if(offset + size > file_size)
			size = file_size - offset;

		buf = malloc(size + 1);
		if (!buf) {
			ret = -ENOMEM;
			goto out;
		}
		testfs_read_data(in, offset, buf, size);
		buf[size] = 0;
		printf("%s\n", buf);
		free(buf);
	}

	out: testfs_put_inode(in);
	return ret;
}
