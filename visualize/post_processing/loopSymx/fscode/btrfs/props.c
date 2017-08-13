
void __init btrfs_props_init(void)
{
	int i;

	hash_init(prop_handlers_ht);

	for (i = 0; i < ARRAY_SIZE(prop_handlers); i++) {
		struct prop_handler *p = &prop_handlers[i];
		u64 h = btrfs_name_hash(p->xattr_name, strlen(p->xattr_name));

		hash_add(prop_handlers_ht, &p->node, h);
	}
}
						 size_t),
				void *ctx)
{
	int ret;
	char *name_buf = NULL;
	char *value_buf = NULL;
	int name_buf_len = 0;
	int value_buf_len = 0;

	while (1) {
		struct btrfs_key key;
		struct btrfs_dir_item *di;
		struct extent_buffer *leaf;
		u32 total_len, cur, this_len;
		int slot;
		const struct hlist_head *handlers;

		slot = path->slots[0];
		leaf = path->nodes[0];

		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);
		if (key.objectid != objectid)
			break;
		if (key.type != BTRFS_XATTR_ITEM_KEY)
			break;

		handlers = find_prop_handlers_by_hash(key.offset);
		if (!handlers)
			goto next_slot;

		di = btrfs_item_ptr(leaf, slot, struct btrfs_dir_item);
		cur = 0;
		total_len = btrfs_item_size_nr(leaf, slot);

		while (cur < total_len) {
			u32 name_len = btrfs_dir_name_len(leaf, di);
			u32 data_len = btrfs_dir_data_len(leaf, di);
			unsigned long name_ptr, data_ptr;
			const struct prop_handler *handler;

			this_len = sizeof(*di) + name_len + data_len;
			name_ptr = (unsigned long)(di + 1);
			data_ptr = name_ptr + name_len;

			if (name_len <= XATTR_BTRFS_PREFIX_LEN ||
			    memcmp_extent_buffer(leaf, XATTR_BTRFS_PREFIX,
						 name_ptr,
						 XATTR_BTRFS_PREFIX_LEN))
				goto next_dir_item;

			if (name_len >= name_buf_len) {
				kfree(name_buf);
				name_buf_len = name_len + 1;
				name_buf = kmalloc(name_buf_len, GFP_NOFS);
				if (!name_buf) {
					ret = -ENOMEM;
					goto out;
				}
			}
			read_extent_buffer(leaf, name_buf, name_ptr, name_len);
			name_buf[name_len] = '\0';

			handler = find_prop_handler(name_buf, handlers);
			if (!handler)
				goto next_dir_item;

			if (data_len > value_buf_len) {
				kfree(value_buf);
				value_buf_len = data_len;
				value_buf = kmalloc(data_len, GFP_NOFS);
				if (!value_buf) {
					ret = -ENOMEM;
					goto out;
				}
			}
			read_extent_buffer(leaf, value_buf, data_ptr, data_len);

			iterator(ctx, handler, value_buf, data_len);
next_dir_item:
			cur += this_len;
			di = (struct btrfs_dir_item *)((char *) di + this_len);
		}

next_slot:
		path->slots[0]++;
	}

	ret = 0;
out:
	btrfs_release_path(path);
	kfree(name_buf);
	kfree(value_buf);

	return ret;
}
			 struct inode *inode,
			 struct inode *parent)
{
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret;
	int i;

	if (!test_bit(BTRFS_INODE_HAS_PROPS,
		      &BTRFS_I(parent)->runtime_flags))
		return 0;

	for (i = 0; i < ARRAY_SIZE(prop_handlers); i++) {
		const struct prop_handler *h = &prop_handlers[i];
		const char *value;
		u64 num_bytes;

		if (!h->inheritable)
			continue;

		value = h->extract(parent);
		if (!value)
			continue;

		num_bytes = btrfs_calc_trans_metadata_size(fs_info, 1);
		ret = btrfs_block_rsv_add(root, trans->block_rsv,
					  num_bytes, BTRFS_RESERVE_NO_FLUSH);
		if (ret)
			goto out;
		ret = __btrfs_set_prop(trans, inode, h->xattr_name,
				       value, strlen(value), 0);
		btrfs_block_rsv_release(fs_info, trans->block_rsv, num_bytes);
		if (ret)
			goto out;
	}
	ret = 0;
out:
	return ret;
}
