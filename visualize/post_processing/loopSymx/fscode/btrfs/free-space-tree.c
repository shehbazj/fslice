				  struct btrfs_block_group_cache *block_group,
				  struct btrfs_path *path)
{
	struct btrfs_root *root = fs_info->free_space_root;
	struct btrfs_free_space_info *info;
	struct btrfs_key key, found_key;
	struct extent_buffer *leaf;
	u8 *bitmap, *bitmap_cursor;
	u64 start, end;
	u64 bitmap_range, i;
	u32 bitmap_size, flags, expected_extent_count;
	u32 extent_count = 0;
	int done = 0, nr;
	int ret;

	bitmap_size = free_space_bitmap_size(block_group->key.offset,
					     fs_info->sectorsize);
	bitmap = alloc_bitmap(bitmap_size);
	if (!bitmap) {
		ret = -ENOMEM;
		goto out;
	}

	start = block_group->key.objectid;
	end = block_group->key.objectid + block_group->key.offset;

	key.objectid = end - 1;
	key.type = (u8)-1;
	key.offset = (u64)-1;

	while (!done) {
		ret = btrfs_search_prev_slot(trans, root, &key, path, -1, 1);
		if (ret)
			goto out;

		leaf = path->nodes[0];
		nr = 0;
		path->slots[0]++;
		while (path->slots[0] > 0) {
			btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0] - 1);

			if (found_key.type == BTRFS_FREE_SPACE_INFO_KEY) {
				ASSERT(found_key.objectid == block_group->key.objectid);
				ASSERT(found_key.offset == block_group->key.offset);
				done = 1;
				break;
			} else if (found_key.type == BTRFS_FREE_SPACE_EXTENT_KEY) {
				u64 first, last;

				ASSERT(found_key.objectid >= start);
				ASSERT(found_key.objectid < end);
				ASSERT(found_key.objectid + found_key.offset <= end);

				first = div_u64(found_key.objectid - start,
						fs_info->sectorsize);
				last = div_u64(found_key.objectid + found_key.offset - start,
					       fs_info->sectorsize);
				le_bitmap_set(bitmap, first, last - first);

				extent_count++;
				nr++;
				path->slots[0]--;
			} else {
				ASSERT(0);
			}
		}

		ret = btrfs_del_items(trans, root, path, path->slots[0], nr);
		if (ret)
			goto out;
		btrfs_release_path(path);
	}

	info = search_free_space_info(trans, fs_info, block_group, path, 1);
	if (IS_ERR(info)) {
		ret = PTR_ERR(info);
		goto out;
	}
	leaf = path->nodes[0];
	flags = btrfs_free_space_flags(leaf, info);
	flags |= BTRFS_FREE_SPACE_USING_BITMAPS;
	btrfs_set_free_space_flags(leaf, info, flags);
	expected_extent_count = btrfs_free_space_extent_count(leaf, info);
	btrfs_mark_buffer_dirty(leaf);
	btrfs_release_path(path);

	if (extent_count != expected_extent_count) {
		btrfs_err(fs_info,
			  "incorrect extent count for %llu; counted %u, expected %u",
			  block_group->key.objectid, extent_count,
			  expected_extent_count);
		ASSERT(0);
		ret = -EIO;
		goto out;
	}

	bitmap_cursor = bitmap;
	bitmap_range = fs_info->sectorsize * BTRFS_FREE_SPACE_BITMAP_BITS;
	i = start;
	while (i < end) {
		unsigned long ptr;
		u64 extent_size;
		u32 data_size;

		extent_size = min(end - i, bitmap_range);
		data_size = free_space_bitmap_size(extent_size,
						   fs_info->sectorsize);

		key.objectid = i;
		key.type = BTRFS_FREE_SPACE_BITMAP_KEY;
		key.offset = extent_size;

		ret = btrfs_insert_empty_item(trans, root, path, &key,
					      data_size);
		if (ret)
			goto out;

		leaf = path->nodes[0];
		ptr = btrfs_item_ptr_offset(leaf, path->slots[0]);
		write_extent_buffer(leaf, bitmap_cursor, ptr,
				    data_size);
		btrfs_mark_buffer_dirty(leaf);
		btrfs_release_path(path);

		i += extent_size;
		bitmap_cursor += data_size;
	}

	ret = 0;
out:
	kvfree(bitmap);
	if (ret)
		btrfs_abort_transaction(trans, ret);
	return ret;
}
				  struct btrfs_block_group_cache *block_group,
				  struct btrfs_path *path)
{
	struct btrfs_root *root = fs_info->free_space_root;
	struct btrfs_free_space_info *info;
	struct btrfs_key key, found_key;
	struct extent_buffer *leaf;
	u8 *bitmap;
	u64 start, end;
	/* Initialize to silence GCC. */
	u64 extent_start = 0;
	u64 offset;
	u32 bitmap_size, flags, expected_extent_count;
	int prev_bit = 0, bit, bitnr;
	u32 extent_count = 0;
	int done = 0, nr;
	int ret;

	bitmap_size = free_space_bitmap_size(block_group->key.offset,
					     fs_info->sectorsize);
	bitmap = alloc_bitmap(bitmap_size);
	if (!bitmap) {
		ret = -ENOMEM;
		goto out;
	}

	start = block_group->key.objectid;
	end = block_group->key.objectid + block_group->key.offset;

	key.objectid = end - 1;
	key.type = (u8)-1;
	key.offset = (u64)-1;

	while (!done) {
		ret = btrfs_search_prev_slot(trans, root, &key, path, -1, 1);
		if (ret)
			goto out;

		leaf = path->nodes[0];
		nr = 0;
		path->slots[0]++;
		while (path->slots[0] > 0) {
			btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0] - 1);

			if (found_key.type == BTRFS_FREE_SPACE_INFO_KEY) {
				ASSERT(found_key.objectid == block_group->key.objectid);
				ASSERT(found_key.offset == block_group->key.offset);
				done = 1;
				break;
			} else if (found_key.type == BTRFS_FREE_SPACE_BITMAP_KEY) {
				unsigned long ptr;
				u8 *bitmap_cursor;
				u32 bitmap_pos, data_size;

				ASSERT(found_key.objectid >= start);
				ASSERT(found_key.objectid < end);
				ASSERT(found_key.objectid + found_key.offset <= end);

				bitmap_pos = div_u64(found_key.objectid - start,
						     fs_info->sectorsize *
						     BITS_PER_BYTE);
				bitmap_cursor = bitmap + bitmap_pos;
				data_size = free_space_bitmap_size(found_key.offset,
								   fs_info->sectorsize);

				ptr = btrfs_item_ptr_offset(leaf, path->slots[0] - 1);
				read_extent_buffer(leaf, bitmap_cursor, ptr,
						   data_size);

				nr++;
				path->slots[0]--;
			} else {
				ASSERT(0);
			}
		}

		ret = btrfs_del_items(trans, root, path, path->slots[0], nr);
		if (ret)
			goto out;
		btrfs_release_path(path);
	}

	info = search_free_space_info(trans, fs_info, block_group, path, 1);
	if (IS_ERR(info)) {
		ret = PTR_ERR(info);
		goto out;
	}
	leaf = path->nodes[0];
	flags = btrfs_free_space_flags(leaf, info);
	flags &= ~BTRFS_FREE_SPACE_USING_BITMAPS;
	btrfs_set_free_space_flags(leaf, info, flags);
	expected_extent_count = btrfs_free_space_extent_count(leaf, info);
	btrfs_mark_buffer_dirty(leaf);
	btrfs_release_path(path);

	offset = start;
	bitnr = 0;
	while (offset < end) {
		bit = !!le_test_bit(bitnr, bitmap);
		if (prev_bit == 0 && bit == 1) {
			extent_start = offset;
		} else if (prev_bit == 1 && bit == 0) {
			key.objectid = extent_start;
			key.type = BTRFS_FREE_SPACE_EXTENT_KEY;
			key.offset = offset - extent_start;

			ret = btrfs_insert_empty_item(trans, root, path, &key, 0);
			if (ret)
				goto out;
			btrfs_release_path(path);

			extent_count++;
		}
		prev_bit = bit;
		offset += fs_info->sectorsize;
		bitnr++;
	}
	if (prev_bit == 1) {
		key.objectid = extent_start;
		key.type = BTRFS_FREE_SPACE_EXTENT_KEY;
		key.offset = end - extent_start;

		ret = btrfs_insert_empty_item(trans, root, path, &key, 0);
		if (ret)
			goto out;
		btrfs_release_path(path);

		extent_count++;
	}

	if (extent_count != expected_extent_count) {
		btrfs_err(fs_info,
			  "incorrect extent count for %llu; counted %u, expected %u",
			  block_group->key.objectid, extent_count,
			  expected_extent_count);
		ASSERT(0);
		ret = -EIO;
		goto out;
	}

	ret = 0;
out:
	kvfree(bitmap);
	if (ret)
		btrfs_abort_transaction(trans, ret);
	return ret;
}
				    struct btrfs_path *path,
				    u64 start, u64 size, int remove)
{
	struct btrfs_root *root = fs_info->free_space_root;
	struct btrfs_key key;
	u64 end = start + size;
	u64 cur_start, cur_size;
	int prev_bit, next_bit;
	int new_extents;
	int ret;

	/*
	 * Read the bit for the block immediately before the extent of space if
	 * that block is within the block group.
	 */
	if (start > block_group->key.objectid) {
		u64 prev_block = start - block_group->fs_info->sectorsize;

		key.objectid = prev_block;
		key.type = (u8)-1;
		key.offset = (u64)-1;

		ret = btrfs_search_prev_slot(trans, root, &key, path, 0, 1);
		if (ret)
			goto out;

		prev_bit = free_space_test_bit(block_group, path, prev_block);

		/* The previous block may have been in the previous bitmap. */
		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);
		if (start >= key.objectid + key.offset) {
			ret = free_space_next_bitmap(trans, root, path);
			if (ret)
				goto out;
		}
	} else {
		key.objectid = start;
		key.type = (u8)-1;
		key.offset = (u64)-1;

		ret = btrfs_search_prev_slot(trans, root, &key, path, 0, 1);
		if (ret)
			goto out;

		prev_bit = -1;
	}

	/*
	 * Iterate over all of the bitmaps overlapped by the extent of space,
	 * clearing/setting bits as required.
	 */
	cur_start = start;
	cur_size = size;
	while (1) {
		free_space_set_bits(block_group, path, &cur_start, &cur_size,
				    !remove);
		if (cur_size == 0)
			break;
		ret = free_space_next_bitmap(trans, root, path);
		if (ret)
			goto out;
	}

	/*
	 * Read the bit for the block immediately after the extent of space if
	 * that block is within the block group.
	 */
	if (end < block_group->key.objectid + block_group->key.offset) {
		/* The next block may be in the next bitmap. */
		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);
		if (end >= key.objectid + key.offset) {
			ret = free_space_next_bitmap(trans, root, path);
			if (ret)
				goto out;
		}

		next_bit = free_space_test_bit(block_group, path, end);
	} else {
		next_bit = -1;
	}

	if (remove) {
		new_extents = -1;
		if (prev_bit == 1) {
			/* Leftover on the left. */
			new_extents++;
		}
		if (next_bit == 1) {
			/* Leftover on the right. */
			new_extents++;
		}
	} else {
		new_extents = 1;
		if (prev_bit == 1) {
			/* Merging with neighbor on the left. */
			new_extents--;
		}
		if (next_bit == 1) {
			/* Merging with neighbor on the right. */
			new_extents--;
		}
	}

	btrfs_release_path(path);
	ret = update_free_space_extent_count(trans, fs_info, block_group, path,
					     new_extents);

out:
	return ret;
}
				    struct btrfs_fs_info *fs_info,
				    struct btrfs_block_group_cache *block_group)
{
	struct btrfs_root *extent_root = fs_info->extent_root;
	struct btrfs_path *path, *path2;
	struct btrfs_key key;
	u64 start, end;
	int ret;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->reada = 1;

	path2 = btrfs_alloc_path();
	if (!path2) {
		btrfs_free_path(path);
		return -ENOMEM;
	}

	ret = add_new_free_space_info(trans, fs_info, block_group, path2);
	if (ret)
		goto out;

	mutex_lock(&block_group->free_space_lock);

	/*
	 * Iterate through all of the extent and metadata items in this block
	 * group, adding the free space between them and the free space at the
	 * end. Note that EXTENT_ITEM and METADATA_ITEM are less than
	 * BLOCK_GROUP_ITEM, so an extent may precede the block group that it's
	 * contained in.
	 */
	key.objectid = block_group->key.objectid;
	key.type = BTRFS_EXTENT_ITEM_KEY;
	key.offset = 0;

	ret = btrfs_search_slot_for_read(extent_root, &key, path, 1, 0);
	if (ret < 0)
		goto out_locked;
	ASSERT(ret == 0);

	start = block_group->key.objectid;
	end = block_group->key.objectid + block_group->key.offset;
	while (1) {
		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);

		if (key.type == BTRFS_EXTENT_ITEM_KEY ||
		    key.type == BTRFS_METADATA_ITEM_KEY) {
			if (key.objectid >= end)
				break;

			if (start < key.objectid) {
				ret = __add_to_free_space_tree(trans, fs_info,
							       block_group,
							       path2, start,
							       key.objectid -
							       start);
				if (ret)
					goto out_locked;
			}
			start = key.objectid;
			if (key.type == BTRFS_METADATA_ITEM_KEY)
				start += fs_info->nodesize;
			else
				start += key.offset;
		} else if (key.type == BTRFS_BLOCK_GROUP_ITEM_KEY) {
			if (key.objectid != block_group->key.objectid)
				break;
		}

		ret = btrfs_next_item(extent_root, path);
		if (ret < 0)
			goto out_locked;
		if (ret)
			break;
	}
	if (start < end) {
		ret = __add_to_free_space_tree(trans, fs_info, block_group,
					       path2, start, end - start);
		if (ret)
			goto out_locked;
	}

	ret = 0;
out_locked:
	mutex_unlock(&block_group->free_space_lock);
out:
	btrfs_free_path(path2);
	btrfs_free_path(path);
	return ret;
}

int btrfs_create_free_space_tree(struct btrfs_fs_info *fs_info)
{
	struct btrfs_trans_handle *trans;
	struct btrfs_root *tree_root = fs_info->tree_root;
	struct btrfs_root *free_space_root;
	struct btrfs_block_group_cache *block_group;
	struct rb_node *node;
	int ret;

	trans = btrfs_start_transaction(tree_root, 0);
	if (IS_ERR(trans))
		return PTR_ERR(trans);

	set_bit(BTRFS_FS_CREATING_FREE_SPACE_TREE, &fs_info->flags);
	free_space_root = btrfs_create_tree(trans, fs_info,
					    BTRFS_FREE_SPACE_TREE_OBJECTID);
	if (IS_ERR(free_space_root)) {
		ret = PTR_ERR(free_space_root);
		goto abort;
	}
	fs_info->free_space_root = free_space_root;

	node = rb_first(&fs_info->block_group_cache_tree);
	while (node) {
		block_group = rb_entry(node, struct btrfs_block_group_cache,
				       cache_node);
		ret = populate_free_space_tree(trans, fs_info, block_group);
		if (ret)
			goto abort;
		node = rb_next(node);
	}

	btrfs_set_fs_compat_ro(fs_info, FREE_SPACE_TREE);
	btrfs_set_fs_compat_ro(fs_info, FREE_SPACE_TREE_VALID);
	clear_bit(BTRFS_FS_CREATING_FREE_SPACE_TREE, &fs_info->flags);

	ret = btrfs_commit_transaction(trans);
	if (ret)
		return ret;

	return 0;

abort:
	clear_bit(BTRFS_FS_CREATING_FREE_SPACE_TREE, &fs_info->flags);
	btrfs_abort_transaction(trans, ret);
	btrfs_end_transaction(trans);
	return ret;
}
static int clear_free_space_tree(struct btrfs_trans_handle *trans,
				 struct btrfs_root *root)
{
	struct btrfs_path *path;
	struct btrfs_key key;
	int nr;
	int ret;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->leave_spinning = 1;

	key.objectid = 0;
	key.type = 0;
	key.offset = 0;

	while (1) {
		ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
		if (ret < 0)
			goto out;

		nr = btrfs_header_nritems(path->nodes[0]);
		if (!nr)
			break;

		path->slots[0] = 0;
		ret = btrfs_del_items(trans, root, path, 0, nr);
		if (ret)
			goto out;

		btrfs_release_path(path);
	}

	ret = 0;
out:
	btrfs_free_path(path);
	return ret;
}
				  struct btrfs_fs_info *fs_info,
				  struct btrfs_block_group_cache *block_group)
{
	struct btrfs_root *root = fs_info->free_space_root;
	struct btrfs_path *path;
	struct btrfs_key key, found_key;
	struct extent_buffer *leaf;
	u64 start, end;
	int done = 0, nr;
	int ret;

	if (!btrfs_fs_compat_ro(fs_info, FREE_SPACE_TREE))
		return 0;

	if (block_group->needs_free_space) {
		/* We never added this block group to the free space tree. */
		return 0;
	}

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	start = block_group->key.objectid;
	end = block_group->key.objectid + block_group->key.offset;

	key.objectid = end - 1;
	key.type = (u8)-1;
	key.offset = (u64)-1;

	while (!done) {
		ret = btrfs_search_prev_slot(trans, root, &key, path, -1, 1);
		if (ret)
			goto out;

		leaf = path->nodes[0];
		nr = 0;
		path->slots[0]++;
		while (path->slots[0] > 0) {
			btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0] - 1);

			if (found_key.type == BTRFS_FREE_SPACE_INFO_KEY) {
				ASSERT(found_key.objectid == block_group->key.objectid);
				ASSERT(found_key.offset == block_group->key.offset);
				done = 1;
				nr++;
				path->slots[0]--;
				break;
			} else if (found_key.type == BTRFS_FREE_SPACE_EXTENT_KEY ||
				   found_key.type == BTRFS_FREE_SPACE_BITMAP_KEY) {
				ASSERT(found_key.objectid >= start);
				ASSERT(found_key.objectid < end);
				ASSERT(found_key.objectid + found_key.offset <= end);
				nr++;
				path->slots[0]--;
			} else {
				ASSERT(0);
			}
		}

		ret = btrfs_del_items(trans, root, path, path->slots[0], nr);
		if (ret)
			goto out;
		btrfs_release_path(path);
	}

	ret = 0;
out:
	btrfs_free_path(path);
	if (ret)
		btrfs_abort_transaction(trans, ret);
	return ret;
}
				   struct btrfs_path *path,
				   u32 expected_extent_count)
{
	struct btrfs_block_group_cache *block_group;
	struct btrfs_fs_info *fs_info;
	struct btrfs_root *root;
	struct btrfs_key key;
	int prev_bit = 0, bit;
	/* Initialize to silence GCC. */
	u64 extent_start = 0;
	u64 end, offset;
	u64 total_found = 0;
	u32 extent_count = 0;
	int ret;

	block_group = caching_ctl->block_group;
	fs_info = block_group->fs_info;
	root = fs_info->free_space_root;

	end = block_group->key.objectid + block_group->key.offset;

	while (1) {
		ret = btrfs_next_item(root, path);
		if (ret < 0)
			goto out;
		if (ret)
			break;

		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);

		if (key.type == BTRFS_FREE_SPACE_INFO_KEY)
			break;

		ASSERT(key.type == BTRFS_FREE_SPACE_BITMAP_KEY);
		ASSERT(key.objectid < end && key.objectid + key.offset <= end);

		caching_ctl->progress = key.objectid;

		offset = key.objectid;
		while (offset < key.objectid + key.offset) {
			bit = free_space_test_bit(block_group, path, offset);
			if (prev_bit == 0 && bit == 1) {
				extent_start = offset;
			} else if (prev_bit == 1 && bit == 0) {
				total_found += add_new_free_space(block_group,
								  fs_info,
								  extent_start,
								  offset);
				if (total_found > CACHING_CTL_WAKE_UP) {
					total_found = 0;
					wake_up(&caching_ctl->wait);
				}
				extent_count++;
			}
			prev_bit = bit;
			offset += fs_info->sectorsize;
		}
	}
	if (prev_bit == 1) {
		total_found += add_new_free_space(block_group, fs_info,
						  extent_start, end);
		extent_count++;
	}

	if (extent_count != expected_extent_count) {
		btrfs_err(fs_info,
			  "incorrect extent count for %llu; counted %u, expected %u",
			  block_group->key.objectid, extent_count,
			  expected_extent_count);
		ASSERT(0);
		ret = -EIO;
		goto out;
	}

	caching_ctl->progress = (u64)-1;

	ret = 0;
out:
	return ret;
}
				   struct btrfs_path *path,
				   u32 expected_extent_count)
{
	struct btrfs_block_group_cache *block_group;
	struct btrfs_fs_info *fs_info;
	struct btrfs_root *root;
	struct btrfs_key key;
	u64 end;
	u64 total_found = 0;
	u32 extent_count = 0;
	int ret;

	block_group = caching_ctl->block_group;
	fs_info = block_group->fs_info;
	root = fs_info->free_space_root;

	end = block_group->key.objectid + block_group->key.offset;

	while (1) {
		ret = btrfs_next_item(root, path);
		if (ret < 0)
			goto out;
		if (ret)
			break;

		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);

		if (key.type == BTRFS_FREE_SPACE_INFO_KEY)
			break;

		ASSERT(key.type == BTRFS_FREE_SPACE_EXTENT_KEY);
		ASSERT(key.objectid < end && key.objectid + key.offset <= end);

		caching_ctl->progress = key.objectid;

		total_found += add_new_free_space(block_group, fs_info,
						  key.objectid,
						  key.objectid + key.offset);
		if (total_found > CACHING_CTL_WAKE_UP) {
			total_found = 0;
			wake_up(&caching_ctl->wait);
		}
		extent_count++;
	}

	if (extent_count != expected_extent_count) {
		btrfs_err(fs_info,
			  "incorrect extent count for %llu; counted %u, expected %u",
			  block_group->key.objectid, extent_count,
			  expected_extent_count);
		ASSERT(0);
		ret = -EIO;
		goto out;
	}

	caching_ctl->progress = (u64)-1;

	ret = 0;
out:
	return ret;
}
