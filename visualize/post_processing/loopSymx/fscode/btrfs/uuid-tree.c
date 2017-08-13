static int btrfs_uuid_tree_lookup(struct btrfs_root *uuid_root, u8 *uuid,
				  u8 type, u64 subid)
{
	int ret;
	struct btrfs_path *path = NULL;
	struct extent_buffer *eb;
	int slot;
	u32 item_size;
	unsigned long offset;
	struct btrfs_key key;

	if (WARN_ON_ONCE(!uuid_root)) {
		ret = -ENOENT;
		goto out;
	}

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	btrfs_uuid_to_key(uuid, type, &key);
	ret = btrfs_search_slot(NULL, uuid_root, &key, path, 0, 0);
	if (ret < 0) {
		goto out;
	} else if (ret > 0) {
		ret = -ENOENT;
		goto out;
	}

	eb = path->nodes[0];
	slot = path->slots[0];
	item_size = btrfs_item_size_nr(eb, slot);
	offset = btrfs_item_ptr_offset(eb, slot);
	ret = -ENOENT;

	if (!IS_ALIGNED(item_size, sizeof(u64))) {
		btrfs_warn(uuid_root->fs_info,
			   "uuid item with illegal size %lu!",
			   (unsigned long)item_size);
		goto out;
	}
	while (item_size) {
		__le64 data;

		read_extent_buffer(eb, &data, offset, sizeof(data));
		if (le64_to_cpu(data) == subid) {
			ret = 0;
			break;
		}
		offset += sizeof(data);
		item_size -= sizeof(data);
	}

out:
	btrfs_free_path(path);
	return ret;
}
			struct btrfs_fs_info *fs_info, u8 *uuid, u8 type,
			u64 subid)
{
	struct btrfs_root *uuid_root = fs_info->uuid_root;
	int ret;
	struct btrfs_path *path = NULL;
	struct btrfs_key key;
	struct extent_buffer *eb;
	int slot;
	unsigned long offset;
	u32 item_size;
	unsigned long move_dst;
	unsigned long move_src;
	unsigned long move_len;

	if (WARN_ON_ONCE(!uuid_root)) {
		ret = -EINVAL;
		goto out;
	}

	btrfs_uuid_to_key(uuid, type, &key);

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	ret = btrfs_search_slot(trans, uuid_root, &key, path, -1, 1);
	if (ret < 0) {
		btrfs_warn(fs_info, "error %d while searching for uuid item!",
			   ret);
		goto out;
	}
	if (ret > 0) {
		ret = -ENOENT;
		goto out;
	}

	eb = path->nodes[0];
	slot = path->slots[0];
	offset = btrfs_item_ptr_offset(eb, slot);
	item_size = btrfs_item_size_nr(eb, slot);
	if (!IS_ALIGNED(item_size, sizeof(u64))) {
		btrfs_warn(fs_info, "uuid item with illegal size %lu!",
			   (unsigned long)item_size);
		ret = -ENOENT;
		goto out;
	}
	while (item_size) {
		__le64 read_subid;

		read_extent_buffer(eb, &read_subid, offset, sizeof(read_subid));
		if (le64_to_cpu(read_subid) == subid)
			break;
		offset += sizeof(read_subid);
		item_size -= sizeof(read_subid);
	}

	if (!item_size) {
		ret = -ENOENT;
		goto out;
	}

	item_size = btrfs_item_size_nr(eb, slot);
	if (item_size == sizeof(subid)) {
		ret = btrfs_del_item(trans, uuid_root, path);
		goto out;
	}

	move_dst = offset;
	move_src = offset + sizeof(subid);
	move_len = item_size - (move_src - btrfs_item_ptr_offset(eb, slot));
	memmove_extent_buffer(eb, move_dst, move_src, move_len);
	btrfs_truncate_item(fs_info, path, item_size - sizeof(subid), 1);

out:
	btrfs_free_path(path);
	return ret;
}
			    int (*check_func)(struct btrfs_fs_info *, u8 *, u8,
					      u64))
{
	struct btrfs_root *root = fs_info->uuid_root;
	struct btrfs_key key;
	struct btrfs_path *path;
	int ret = 0;
	struct extent_buffer *leaf;
	int slot;
	u32 item_size;
	unsigned long offset;

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	key.objectid = 0;
	key.type = 0;
	key.offset = 0;

again_search_slot:
	ret = btrfs_search_forward(root, &key, path, 0);
	if (ret) {
		if (ret > 0)
			ret = 0;
		goto out;
	}

	while (1) {
		cond_resched();
		leaf = path->nodes[0];
		slot = path->slots[0];
		btrfs_item_key_to_cpu(leaf, &key, slot);

		if (key.type != BTRFS_UUID_KEY_SUBVOL &&
		    key.type != BTRFS_UUID_KEY_RECEIVED_SUBVOL)
			goto skip;

		offset = btrfs_item_ptr_offset(leaf, slot);
		item_size = btrfs_item_size_nr(leaf, slot);
		if (!IS_ALIGNED(item_size, sizeof(u64))) {
			btrfs_warn(fs_info,
				   "uuid item with illegal size %lu!",
				   (unsigned long)item_size);
			goto skip;
		}
		while (item_size) {
			u8 uuid[BTRFS_UUID_SIZE];
			__le64 subid_le;
			u64 subid_cpu;

			put_unaligned_le64(key.objectid, uuid);
			put_unaligned_le64(key.offset, uuid + sizeof(u64));
			read_extent_buffer(leaf, &subid_le, offset,
					   sizeof(subid_le));
			subid_cpu = le64_to_cpu(subid_le);
			ret = check_func(fs_info, uuid, key.type, subid_cpu);
			if (ret < 0)
				goto out;
			if (ret > 0) {
				btrfs_release_path(path);
				ret = btrfs_uuid_iter_rem(root, uuid, key.type,
							  subid_cpu);
				if (ret == 0) {
					/*
					 * this might look inefficient, but the
					 * justification is that it is an
					 * exception that check_func returns 1,
					 * and that in the regular case only one
					 * entry per UUID exists.
					 */
					goto again_search_slot;
				}
				if (ret < 0 && ret != -ENOENT)
					goto out;
			}
			item_size -= sizeof(subid_le);
			offset += sizeof(subid_le);
		}

skip:
		ret = btrfs_next_item(root, path);
		if (ret == 0)
			continue;
		else if (ret > 0)
			ret = 0;
		break;
	}

out:
	btrfs_free_path(path);
	return ret;
}
