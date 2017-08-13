
ssize_t btrfs_listxattr(struct dentry *dentry, char *buffer, size_t size)
{
	struct btrfs_key key;
	struct inode *inode = d_inode(dentry);
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_path *path;
	int ret = 0;
	size_t total_size = 0, size_left = size;

	/*
	 * ok we want all objects associated with this id.
	 * NOTE: we set key.offset = 0; because we want to start with the
	 * first xattr that we find and walk forward
	 */
	key.objectid = btrfs_ino(BTRFS_I(inode));
	key.type = BTRFS_XATTR_ITEM_KEY;
	key.offset = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->reada = READA_FORWARD;

	/* search for our xattrs */
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto err;

	while (1) {
		struct extent_buffer *leaf;
		int slot;
		struct btrfs_dir_item *di;
		struct btrfs_key found_key;
		u32 item_size;
		u32 cur;

		leaf = path->nodes[0];
		slot = path->slots[0];

		/* this is where we start walking through the path */
		if (slot >= btrfs_header_nritems(leaf)) {
			/*
			 * if we've reached the last slot in this leaf we need
			 * to go to the next leaf and reset everything
			 */
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto err;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		/* check to make sure this item is what we want */
		if (found_key.objectid != key.objectid)
			break;
		if (found_key.type > BTRFS_XATTR_ITEM_KEY)
			break;
		if (found_key.type < BTRFS_XATTR_ITEM_KEY)
			goto next_item;

		di = btrfs_item_ptr(leaf, slot, struct btrfs_dir_item);
		item_size = btrfs_item_size_nr(leaf, slot);
		cur = 0;
		while (cur < item_size) {
			u16 name_len = btrfs_dir_name_len(leaf, di);
			u16 data_len = btrfs_dir_data_len(leaf, di);
			u32 this_len = sizeof(*di) + name_len + data_len;
			unsigned long name_ptr = (unsigned long)(di + 1);

			if (verify_dir_item(fs_info, leaf, di)) {
				ret = -EIO;
				goto err;
			}

			total_size += name_len + 1;
			/*
			 * We are just looking for how big our buffer needs to
			 * be.
			 */
			if (!size)
				goto next;

			if (!buffer || (name_len + 1) > size_left) {
				ret = -ERANGE;
				goto err;
			}

			read_extent_buffer(leaf, buffer, name_ptr, name_len);
			buffer[name_len] = '\0';

			size_left -= name_len + 1;
			buffer += name_len + 1;
next:
			cur += this_len;
			di = (struct btrfs_dir_item *)((char *)di + this_len);
		}
next_item:
		path->slots[0]++;
	}
	ret = total_size;

err:
	btrfs_free_path(path);

	return ret;
}
static int btrfs_initxattrs(struct inode *inode,
			    const struct xattr *xattr_array, void *fs_info)
{
	const struct xattr *xattr;
	struct btrfs_trans_handle *trans = fs_info;
	char *name;
	int err = 0;

	for (xattr = xattr_array; xattr->name != NULL; xattr++) {
		name = kmalloc(XATTR_SECURITY_PREFIX_LEN +
			       strlen(xattr->name) + 1, GFP_KERNEL);
		if (!name) {
			err = -ENOMEM;
			break;
		}
		strcpy(name, XATTR_SECURITY_PREFIX);
		strcpy(name + XATTR_SECURITY_PREFIX_LEN, xattr->name);
		err = __btrfs_setxattr(trans, inode, name,
				       xattr->value, xattr->value_len, 0);
		kfree(name);
		if (err < 0)
			break;
	}
	return err;
}
