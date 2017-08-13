static int btrfs_add_block_group_cache(struct btrfs_fs_info *info,
				struct btrfs_block_group_cache *block_group)
{
	struct rb_node **p;
	struct rb_node *parent = NULL;
	struct btrfs_block_group_cache *cache;

	spin_lock(&info->block_group_cache_lock);
	p = &info->block_group_cache_tree.rb_node;

	while (*p) {
		parent = *p;
		cache = rb_entry(parent, struct btrfs_block_group_cache,
				 cache_node);
		if (block_group->key.objectid < cache->key.objectid) {
			p = &(*p)->rb_left;
		} else if (block_group->key.objectid > cache->key.objectid) {
			p = &(*p)->rb_right;
		} else {
			spin_unlock(&info->block_group_cache_lock);
			return -EEXIST;
		}
	}

	rb_link_node(&block_group->cache_node, parent, p);
	rb_insert_color(&block_group->cache_node,
			&info->block_group_cache_tree);

	if (info->first_logical_byte > block_group->key.objectid)
		info->first_logical_byte = block_group->key.objectid;

	spin_unlock(&info->block_group_cache_lock);

	return 0;
}
block_group_cache_tree_search(struct btrfs_fs_info *info, u64 bytenr,
			      int contains)
{
	struct btrfs_block_group_cache *cache, *ret = NULL;
	struct rb_node *n;
	u64 end, start;

	spin_lock(&info->block_group_cache_lock);
	n = info->block_group_cache_tree.rb_node;

	while (n) {
		cache = rb_entry(n, struct btrfs_block_group_cache,
				 cache_node);
		end = cache->key.objectid + cache->key.offset - 1;
		start = cache->key.objectid;

		if (bytenr < start) {
			if (!contains && (!ret || start < ret->key.objectid))
				ret = cache;
			n = n->rb_left;
		} else if (bytenr > start) {
			if (contains && bytenr <= end) {
				ret = cache;
				break;
			}
			n = n->rb_right;
		} else {
			ret = cache;
			break;
		}
	}
	if (ret) {
		btrfs_get_block_group(ret);
		if (bytenr == 0 && info->first_logical_byte > ret->key.objectid)
			info->first_logical_byte = ret->key.objectid;
	}
	spin_unlock(&info->block_group_cache_lock);

	return ret;
}
static int exclude_super_stripes(struct btrfs_fs_info *fs_info,
				 struct btrfs_block_group_cache *cache)
{
	u64 bytenr;
	u64 *logical;
	int stripe_len;
	int i, nr, ret;

	if (cache->key.objectid < BTRFS_SUPER_INFO_OFFSET) {
		stripe_len = BTRFS_SUPER_INFO_OFFSET - cache->key.objectid;
		cache->bytes_super += stripe_len;
		ret = add_excluded_extent(fs_info, cache->key.objectid,
					  stripe_len);
		if (ret)
			return ret;
	}

	for (i = 0; i < BTRFS_SUPER_MIRROR_MAX; i++) {
		bytenr = btrfs_sb_offset(i);
		ret = btrfs_rmap_block(fs_info, cache->key.objectid,
				       bytenr, 0, &logical, &nr, &stripe_len);
		if (ret)
			return ret;

		while (nr--) {
			u64 start, len;

			if (logical[nr] > cache->key.objectid +
			    cache->key.offset)
				continue;

			if (logical[nr] + stripe_len <= cache->key.objectid)
				continue;

			start = logical[nr];
			if (start < cache->key.objectid) {
				start = cache->key.objectid;
				len = (logical[nr] + stripe_len) - start;
			} else {
				len = min_t(u64, stripe_len,
					    cache->key.objectid +
					    cache->key.offset - start);
			}

			cache->bytes_super += len;
			ret = add_excluded_extent(fs_info, start, len);
			if (ret) {
				kfree(logical);
				return ret;
			}
		}

		kfree(logical);
	}
	return 0;
}
#ifdef CONFIG_BTRFS_DEBUG
static void fragment_free_space(struct btrfs_block_group_cache *block_group)
{
	struct btrfs_fs_info *fs_info = block_group->fs_info;
	u64 start = block_group->key.objectid;
	u64 len = block_group->key.offset;
	u64 chunk = block_group->flags & BTRFS_BLOCK_GROUP_METADATA ?
		fs_info->nodesize : fs_info->sectorsize;
	u64 step = chunk << 1;

	while (len > chunk) {
		btrfs_remove_free_space(block_group, start, chunk);
		start += step;
		if (len < step)
			len = 0;
		else
			len -= step;
	}
}
u64 add_new_free_space(struct btrfs_block_group_cache *block_group,
		       struct btrfs_fs_info *info, u64 start, u64 end)
{
	u64 extent_start, extent_end, size, total_added = 0;
	int ret;

	while (start < end) {
		ret = find_first_extent_bit(info->pinned_extents, start,
					    &extent_start, &extent_end,
					    EXTENT_DIRTY | EXTENT_UPTODATE,
					    NULL);
		if (ret)
			break;

		if (extent_start <= start) {
			start = extent_end + 1;
		} else if (extent_start > start && extent_start < end) {
			size = extent_start - start;
			total_added += size;
			ret = btrfs_add_free_space(block_group, start,
						   size);
			BUG_ON(ret); /* -ENOMEM or logic error */
			start = extent_end + 1;
		} else {
			break;
		}
	}

	if (start < end) {
		size = end - start;
		total_added += size;
		ret = btrfs_add_free_space(block_group, start, size);
		BUG_ON(ret); /* -ENOMEM or logic error */
	}

	return total_added;
}

static int load_extent_tree_free(struct btrfs_caching_control *caching_ctl)
{
	struct btrfs_block_group_cache *block_group = caching_ctl->block_group;
	struct btrfs_fs_info *fs_info = block_group->fs_info;
	struct btrfs_root *extent_root = fs_info->extent_root;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	u64 total_found = 0;
	u64 last = 0;
	u32 nritems;
	int ret;
	bool wakeup = true;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	last = max_t(u64, block_group->key.objectid, BTRFS_SUPER_INFO_OFFSET);

#ifdef CONFIG_BTRFS_DEBUG
	/*
	 * If we're fragmenting we don't want to make anybody think we can
	 * allocate from this block group until we've had a chance to fragment
	 * the free space.
	 */
	if (btrfs_should_fragment_free_space(block_group))
		wakeup = false;
#endif
	/*
	 * We don't want to deadlock with somebody trying to allocate a new
	 * extent for the extent root while also trying to search the extent
	 * root to add free space.  So we skip locking and search the commit
	 * root, since its read-only
	 */
	path->skip_locking = 1;
	path->search_commit_root = 1;
	path->reada = READA_FORWARD;

	key.objectid = last;
	key.offset = 0;
	key.type = BTRFS_EXTENT_ITEM_KEY;

next:
	ret = btrfs_search_slot(NULL, extent_root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	leaf = path->nodes[0];
	nritems = btrfs_header_nritems(leaf);

	while (1) {
		if (btrfs_fs_closing(fs_info) > 1) {
			last = (u64)-1;
			break;
		}

		if (path->slots[0] < nritems) {
			btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
		} else {
			ret = find_next_key(path, 0, &key);
			if (ret)
				break;

			if (need_resched() ||
			    rwsem_is_contended(&fs_info->commit_root_sem)) {
				if (wakeup)
					caching_ctl->progress = last;
				btrfs_release_path(path);
				up_read(&fs_info->commit_root_sem);
				mutex_unlock(&caching_ctl->mutex);
				cond_resched();
				mutex_lock(&caching_ctl->mutex);
				down_read(&fs_info->commit_root_sem);
				goto next;
			}

			ret = btrfs_next_leaf(extent_root, path);
			if (ret < 0)
				goto out;
			if (ret)
				break;
			leaf = path->nodes[0];
			nritems = btrfs_header_nritems(leaf);
			continue;
		}

		if (key.objectid < last) {
			key.objectid = last;
			key.offset = 0;
			key.type = BTRFS_EXTENT_ITEM_KEY;

			if (wakeup)
				caching_ctl->progress = last;
			btrfs_release_path(path);
			goto next;
		}

		if (key.objectid < block_group->key.objectid) {
			path->slots[0]++;
			continue;
		}

		if (key.objectid >= block_group->key.objectid +
		    block_group->key.offset)
			break;

		if (key.type == BTRFS_EXTENT_ITEM_KEY ||
		    key.type == BTRFS_METADATA_ITEM_KEY) {
			total_found += add_new_free_space(block_group,
							  fs_info, last,
							  key.objectid);
			if (key.type == BTRFS_METADATA_ITEM_KEY)
				last = key.objectid +
					fs_info->nodesize;
			else
				last = key.objectid + key.offset;

			if (total_found > CACHING_CTL_WAKE_UP) {
				total_found = 0;
				if (wakeup)
					wake_up(&caching_ctl->wait);
			}
		}
		path->slots[0]++;
	}
	ret = 0;

	total_found += add_new_free_space(block_group, fs_info, last,
					  block_group->key.objectid +
					  block_group->key.offset);
	caching_ctl->progress = (u64)-1;

out:
	btrfs_free_path(path);
	return ret;
}
static int cache_block_group(struct btrfs_block_group_cache *cache,
			     int load_cache_only)
{
	DEFINE_WAIT(wait);
	struct btrfs_fs_info *fs_info = cache->fs_info;
	struct btrfs_caching_control *caching_ctl;
	int ret = 0;

	caching_ctl = kzalloc(sizeof(*caching_ctl), GFP_NOFS);
	if (!caching_ctl)
		return -ENOMEM;

	INIT_LIST_HEAD(&caching_ctl->list);
	mutex_init(&caching_ctl->mutex);
	init_waitqueue_head(&caching_ctl->wait);
	caching_ctl->block_group = cache;
	caching_ctl->progress = cache->key.objectid;
	refcount_set(&caching_ctl->count, 1);
	btrfs_init_work(&caching_ctl->work, btrfs_cache_helper,
			caching_thread, NULL, NULL);

	spin_lock(&cache->lock);
	/*
	 * This should be a rare occasion, but this could happen I think in the
	 * case where one thread starts to load the space cache info, and then
	 * some other thread starts a transaction commit which tries to do an
	 * allocation while the other thread is still loading the space cache
	 * info.  The previous loop should have kept us from choosing this block
	 * group, but if we've moved to the state where we will wait on caching
	 * block groups we need to first check if we're doing a fast load here,
	 * so we can wait for it to finish, otherwise we could end up allocating
	 * from a block group who's cache gets evicted for one reason or
	 * another.
	 */
	while (cache->cached == BTRFS_CACHE_FAST) {
		struct btrfs_caching_control *ctl;

		ctl = cache->caching_ctl;
		refcount_inc(&ctl->count);
		prepare_to_wait(&ctl->wait, &wait, TASK_UNINTERRUPTIBLE);
		spin_unlock(&cache->lock);

		schedule();

		finish_wait(&ctl->wait, &wait);
		put_caching_control(ctl);
		spin_lock(&cache->lock);
	}

	if (cache->cached != BTRFS_CACHE_NO) {
		spin_unlock(&cache->lock);
		kfree(caching_ctl);
		return 0;
	}
	WARN_ON(cache->caching_ctl);
	cache->caching_ctl = caching_ctl;
	cache->cached = BTRFS_CACHE_FAST;
	spin_unlock(&cache->lock);

	if (fs_info->mount_opt & BTRFS_MOUNT_SPACE_CACHE) {
		mutex_lock(&caching_ctl->mutex);
		ret = load_free_space_cache(fs_info, cache);

		spin_lock(&cache->lock);
		if (ret == 1) {
			cache->caching_ctl = NULL;
			cache->cached = BTRFS_CACHE_FINISHED;
			cache->last_byte_to_unpin = (u64)-1;
			caching_ctl->progress = (u64)-1;
		} else {
			if (load_cache_only) {
				cache->caching_ctl = NULL;
				cache->cached = BTRFS_CACHE_NO;
			} else {
				cache->cached = BTRFS_CACHE_STARTED;
				cache->has_caching_ctl = 1;
			}
		}
		spin_unlock(&cache->lock);
#ifdef CONFIG_BTRFS_DEBUG
		if (ret == 1 &&
		    btrfs_should_fragment_free_space(cache)) {
			u64 bytes_used;

			spin_lock(&cache->space_info->lock);
			spin_lock(&cache->lock);
			bytes_used = cache->key.offset -
				btrfs_block_group_used(&cache->item);
			cache->space_info->bytes_used += bytes_used >> 1;
			spin_unlock(&cache->lock);
			spin_unlock(&cache->space_info->lock);
			fragment_free_space(cache);
		}
#endif
		mutex_unlock(&caching_ctl->mutex);

		wake_up(&caching_ctl->wait);
		if (ret == 1) {
			put_caching_control(caching_ctl);
			free_excluded_extents(fs_info, cache);
			return 0;
		}
	} else {
		/*
		 * We're either using the free space tree or no caching at all.
		 * Set cached to the appropriate value and wakeup any waiters.
		 */
		spin_lock(&cache->lock);
		if (load_cache_only) {
			cache->caching_ctl = NULL;
			cache->cached = BTRFS_CACHE_NO;
		} else {
			cache->cached = BTRFS_CACHE_STARTED;
			cache->has_caching_ctl = 1;
		}
		spin_unlock(&cache->lock);
		wake_up(&caching_ctl->wait);
	}

	if (load_cache_only) {
		put_caching_control(caching_ctl);
		return 0;
	}

	down_write(&fs_info->commit_root_sem);
	refcount_inc(&caching_ctl->count);
	list_add_tail(&caching_ctl->list, &fs_info->caching_block_groups);
	up_write(&fs_info->commit_root_sem);

	btrfs_get_block_group(cache);

	btrfs_queue_work(fs_info->caching_workers, &caching_ctl->work);

	return ret;
}
				  struct btrfs_path *path,
				  u64 owner, u32 extra_size)
{
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_extent_item *item;
	struct btrfs_extent_item_v0 *ei0;
	struct btrfs_extent_ref_v0 *ref0;
	struct btrfs_tree_block_info *bi;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	struct btrfs_key found_key;
	u32 new_size = sizeof(*item);
	u64 refs;
	int ret;

	leaf = path->nodes[0];
	BUG_ON(btrfs_item_size_nr(leaf, path->slots[0]) != sizeof(*ei0));

	btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
	ei0 = btrfs_item_ptr(leaf, path->slots[0],
			     struct btrfs_extent_item_v0);
	refs = btrfs_extent_refs_v0(leaf, ei0);

	if (owner == (u64)-1) {
		while (1) {
			if (path->slots[0] >= btrfs_header_nritems(leaf)) {
				ret = btrfs_next_leaf(root, path);
				if (ret < 0)
					return ret;
				BUG_ON(ret > 0); /* Corruption */
				leaf = path->nodes[0];
			}
			btrfs_item_key_to_cpu(leaf, &found_key,
					      path->slots[0]);
			BUG_ON(key.objectid != found_key.objectid);
			if (found_key.type != BTRFS_EXTENT_REF_V0_KEY) {
				path->slots[0]++;
				continue;
			}
			ref0 = btrfs_item_ptr(leaf, path->slots[0],
					      struct btrfs_extent_ref_v0);
			owner = btrfs_ref_objectid_v0(leaf, ref0);
			break;
		}
	}
	btrfs_release_path(path);

	if (owner < BTRFS_FIRST_FREE_OBJECTID)
		new_size += sizeof(*bi);

	new_size -= sizeof(*ei0);
	ret = btrfs_search_slot(trans, root, &key, path,
				new_size + extra_size, 1);
	if (ret < 0)
		return ret;
	BUG_ON(ret); /* Corruption */

	btrfs_extend_item(fs_info, path, new_size);

	leaf = path->nodes[0];
	item = btrfs_item_ptr(leaf, path->slots[0], struct btrfs_extent_item);
	btrfs_set_extent_refs(leaf, item, refs);
	/* FIXME: get real generation */
	btrfs_set_extent_generation(leaf, item, 0);
	if (owner < BTRFS_FIRST_FREE_OBJECTID) {
		btrfs_set_extent_flags(leaf, item,
				       BTRFS_EXTENT_FLAG_TREE_BLOCK |
				       BTRFS_BLOCK_FLAG_FULL_BACKREF);
		bi = (struct btrfs_tree_block_info *)(item + 1);
		/* FIXME: get first key of the block */
		memzero_extent_buffer(leaf, (unsigned long)bi, sizeof(*bi));
		btrfs_set_tree_block_level(leaf, bi, (int)owner);
	} else {
		btrfs_set_extent_flags(leaf, item, BTRFS_EXTENT_FLAG_DATA);
	}
	btrfs_mark_buffer_dirty(leaf);
	return 0;
}
					   u64 root_objectid,
					   u64 owner, u64 offset)
{
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_key key;
	struct btrfs_extent_data_ref *ref;
	struct extent_buffer *leaf;
	u32 nritems;
	int ret;
	int recow;
	int err = -ENOENT;

	key.objectid = bytenr;
	if (parent) {
		key.type = BTRFS_SHARED_DATA_REF_KEY;
		key.offset = parent;
	} else {
		key.type = BTRFS_EXTENT_DATA_REF_KEY;
		key.offset = hash_extent_data_ref(root_objectid,
						  owner, offset);
	}
again:
	recow = 0;
	ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
	if (ret < 0) {
		err = ret;
		goto fail;
	}

	if (parent) {
		if (!ret)
			return 0;
#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
		key.type = BTRFS_EXTENT_REF_V0_KEY;
		btrfs_release_path(path);
		ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
		if (ret < 0) {
			err = ret;
			goto fail;
		}
		if (!ret)
			return 0;
#endif
		goto fail;
	}

	leaf = path->nodes[0];
	nritems = btrfs_header_nritems(leaf);
	while (1) {
		if (path->slots[0] >= nritems) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				err = ret;
			if (ret)
				goto fail;

			leaf = path->nodes[0];
			nritems = btrfs_header_nritems(leaf);
			recow = 1;
		}

		btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
		if (key.objectid != bytenr ||
		    key.type != BTRFS_EXTENT_DATA_REF_KEY)
			goto fail;

		ref = btrfs_item_ptr(leaf, path->slots[0],
				     struct btrfs_extent_data_ref);

		if (match_extent_data_ref(leaf, ref, root_objectid,
					  owner, offset)) {
			if (recow) {
				btrfs_release_path(path);
				goto again;
			}
			err = 0;
			break;
		}
		path->slots[0]++;
	}
fail:
	return err;
}
					   u64 root_objectid, u64 owner,
					   u64 offset, int refs_to_add)
{
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_key key;
	struct extent_buffer *leaf;
	u32 size;
	u32 num_refs;
	int ret;

	key.objectid = bytenr;
	if (parent) {
		key.type = BTRFS_SHARED_DATA_REF_KEY;
		key.offset = parent;
		size = sizeof(struct btrfs_shared_data_ref);
	} else {
		key.type = BTRFS_EXTENT_DATA_REF_KEY;
		key.offset = hash_extent_data_ref(root_objectid,
						  owner, offset);
		size = sizeof(struct btrfs_extent_data_ref);
	}

	ret = btrfs_insert_empty_item(trans, root, path, &key, size);
	if (ret && ret != -EEXIST)
		goto fail;

	leaf = path->nodes[0];
	if (parent) {
		struct btrfs_shared_data_ref *ref;
		ref = btrfs_item_ptr(leaf, path->slots[0],
				     struct btrfs_shared_data_ref);
		if (ret == 0) {
			btrfs_set_shared_data_ref_count(leaf, ref, refs_to_add);
		} else {
			num_refs = btrfs_shared_data_ref_count(leaf, ref);
			num_refs += refs_to_add;
			btrfs_set_shared_data_ref_count(leaf, ref, num_refs);
		}
	} else {
		struct btrfs_extent_data_ref *ref;
		while (ret == -EEXIST) {
			ref = btrfs_item_ptr(leaf, path->slots[0],
					     struct btrfs_extent_data_ref);
			if (match_extent_data_ref(leaf, ref, root_objectid,
						  owner, offset))
				break;
			btrfs_release_path(path);
			key.offset++;
			ret = btrfs_insert_empty_item(trans, root, path, &key,
						      size);
			if (ret && ret != -EEXIST)
				goto fail;

			leaf = path->nodes[0];
		}
		ref = btrfs_item_ptr(leaf, path->slots[0],
				     struct btrfs_extent_data_ref);
		if (ret == 0) {
			btrfs_set_extent_data_ref_root(leaf, ref,
						       root_objectid);
			btrfs_set_extent_data_ref_objectid(leaf, ref, owner);
			btrfs_set_extent_data_ref_offset(leaf, ref, offset);
			btrfs_set_extent_data_ref_count(leaf, ref, refs_to_add);
		} else {
			num_refs = btrfs_extent_data_ref_count(leaf, ref);
			num_refs += refs_to_add;
			btrfs_set_extent_data_ref_count(leaf, ref, num_refs);
		}
	}
	btrfs_mark_buffer_dirty(leaf);
	ret = 0;
fail:
	btrfs_release_path(path);
	return ret;
}
			 struct btrfs_key *key)

{
	for (; level < BTRFS_MAX_LEVEL; level++) {
		if (!path->nodes[level])
			break;
		if (path->slots[level] + 1 >=
		    btrfs_header_nritems(path->nodes[level]))
			continue;
		if (level == 0)
			btrfs_item_key_to_cpu(path->nodes[level], key,
					      path->slots[level] + 1);
		else
			btrfs_node_key_to_cpu(path->nodes[level], key,
					      path->slots[level] + 1);
		return 0;
	}
	return 1;
}
				 u64 parent, u64 root_objectid,
				 u64 owner, u64 offset, int insert)
{
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_key key;
	struct extent_buffer *leaf;
	struct btrfs_extent_item *ei;
	struct btrfs_extent_inline_ref *iref;
	u64 flags;
	u64 item_size;
	unsigned long ptr;
	unsigned long end;
	int extra_size;
	int type;
	int want;
	int ret;
	int err = 0;
	bool skinny_metadata = btrfs_fs_incompat(fs_info, SKINNY_METADATA);

	key.objectid = bytenr;
	key.type = BTRFS_EXTENT_ITEM_KEY;
	key.offset = num_bytes;

	want = extent_ref_type(parent, owner);
	if (insert) {
		extra_size = btrfs_extent_inline_ref_size(want);
		path->keep_locks = 1;
	} else
		extra_size = -1;

	/*
	 * Owner is our parent level, so we can just add one to get the level
	 * for the block we are interested in.
	 */
	if (skinny_metadata && owner < BTRFS_FIRST_FREE_OBJECTID) {
		key.type = BTRFS_METADATA_ITEM_KEY;
		key.offset = owner;
	}

again:
	ret = btrfs_search_slot(trans, root, &key, path, extra_size, 1);
	if (ret < 0) {
		err = ret;
		goto out;
	}

	/*
	 * We may be a newly converted file system which still has the old fat
	 * extent entries for metadata, so try and see if we have one of those.
	 */
	if (ret > 0 && skinny_metadata) {
		skinny_metadata = false;
		if (path->slots[0]) {
			path->slots[0]--;
			btrfs_item_key_to_cpu(path->nodes[0], &key,
					      path->slots[0]);
			if (key.objectid == bytenr &&
			    key.type == BTRFS_EXTENT_ITEM_KEY &&
			    key.offset == num_bytes)
				ret = 0;
		}
		if (ret) {
			key.objectid = bytenr;
			key.type = BTRFS_EXTENT_ITEM_KEY;
			key.offset = num_bytes;
			btrfs_release_path(path);
			goto again;
		}
	}

	if (ret && !insert) {
		err = -ENOENT;
		goto out;
	} else if (WARN_ON(ret)) {
		err = -EIO;
		goto out;
	}

	leaf = path->nodes[0];
	item_size = btrfs_item_size_nr(leaf, path->slots[0]);
#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
	if (item_size < sizeof(*ei)) {
		if (!insert) {
			err = -ENOENT;
			goto out;
		}
		ret = convert_extent_item_v0(trans, fs_info, path, owner,
					     extra_size);
		if (ret < 0) {
			err = ret;
			goto out;
		}
		leaf = path->nodes[0];
		item_size = btrfs_item_size_nr(leaf, path->slots[0]);
	}
#endif
	BUG_ON(item_size < sizeof(*ei));

	ei = btrfs_item_ptr(leaf, path->slots[0], struct btrfs_extent_item);
	flags = btrfs_extent_flags(leaf, ei);

	ptr = (unsigned long)(ei + 1);
	end = (unsigned long)ei + item_size;

	if (flags & BTRFS_EXTENT_FLAG_TREE_BLOCK && !skinny_metadata) {
		ptr += sizeof(struct btrfs_tree_block_info);
		BUG_ON(ptr > end);
	}

	err = -ENOENT;
	while (1) {
		if (ptr >= end) {
			WARN_ON(ptr > end);
			break;
		}
		iref = (struct btrfs_extent_inline_ref *)ptr;
		type = btrfs_extent_inline_ref_type(leaf, iref);
		if (want < type)
			break;
		if (want > type) {
			ptr += btrfs_extent_inline_ref_size(type);
			continue;
		}

		if (type == BTRFS_EXTENT_DATA_REF_KEY) {
			struct btrfs_extent_data_ref *dref;
			dref = (struct btrfs_extent_data_ref *)(&iref->offset);
			if (match_extent_data_ref(leaf, dref, root_objectid,
						  owner, offset)) {
				err = 0;
				break;
			}
			if (hash_extent_data_ref_item(leaf, dref) <
			    hash_extent_data_ref(root_objectid, owner, offset))
				break;
		} else {
			u64 ref_offset;
			ref_offset = btrfs_extent_inline_ref_offset(leaf, iref);
			if (parent > 0) {
				if (parent == ref_offset) {
					err = 0;
					break;
				}
				if (ref_offset < parent)
					break;
			} else {
				if (root_objectid == ref_offset) {
					err = 0;
					break;
				}
				if (ref_offset < root_objectid)
					break;
			}
		}
		ptr += btrfs_extent_inline_ref_size(type);
	}
	if (err == -ENOENT && insert) {
		if (item_size + extra_size >=
		    BTRFS_MAX_EXTENT_ITEM_SIZE(root)) {
			err = -EAGAIN;
			goto out;
		}
		/*
		 * To add new inline back ref, we have to make sure
		 * there is no corresponding back ref item.
		 * For simplicity, we just do not add new inline back
		 * ref if there is any kind of item for this block
		 */
		if (find_next_key(path, 0, &key) == 0 &&
		    key.objectid == bytenr &&
		    key.type < BTRFS_BLOCK_GROUP_ITEM_KEY) {
			err = -EAGAIN;
			goto out;
		}
	}
	*ref_ret = (struct btrfs_extent_inline_ref *)ptr;
out:
	if (insert) {
		path->keep_locks = 0;
		btrfs_unlock_up_safe(path, 1);
	}
	return err;
}
static int btrfs_issue_discard(struct block_device *bdev, u64 start, u64 len,
			       u64 *discarded_bytes)
{
	int j, ret = 0;
	u64 bytes_left, end;
	u64 aligned_start = ALIGN(start, 1 << 9);

	if (WARN_ON(start != aligned_start)) {
		len -= aligned_start - start;
		len = round_down(len, 1 << 9);
		start = aligned_start;
	}

	*discarded_bytes = 0;

	if (!len)
		return 0;

	end = start + len;
	bytes_left = len;

	/* Skip any superblocks on this device. */
	for (j = 0; j < BTRFS_SUPER_MIRROR_MAX; j++) {
		u64 sb_start = btrfs_sb_offset(j);
		u64 sb_end = sb_start + BTRFS_SUPER_INFO_SIZE;
		u64 size = sb_start - start;

		if (!in_range(sb_start, start, bytes_left) &&
		    !in_range(sb_end, start, bytes_left) &&
		    !in_range(start, sb_start, BTRFS_SUPER_INFO_SIZE))
			continue;

		/*
		 * Superblock spans beginning of range.  Adjust start and
		 * try again.
		 */
		if (sb_start <= start) {
			start += sb_end - start;
			if (start > end) {
				bytes_left = 0;
				break;
			}
			bytes_left = end - start;
			continue;
		}

		if (size) {
			ret = blkdev_issue_discard(bdev, start >> 9, size >> 9,
						   GFP_NOFS, 0);
			if (!ret)
				*discarded_bytes += size;
			else if (ret != -EOPNOTSUPP)
				return ret;
		}

		start = sb_end;
		if (start > end) {
			bytes_left = 0;
			break;
		}
		bytes_left = end - start;
	}

	if (bytes_left) {
		ret = blkdev_issue_discard(bdev, start >> 9, bytes_left >> 9,
					   GFP_NOFS, 0);
		if (!ret)
			*discarded_bytes += bytes_left;
	}
	return ret;
}
int btrfs_discard_extent(struct btrfs_fs_info *fs_info, u64 bytenr,
			 u64 num_bytes, u64 *actual_bytes)
{
	int ret;
	u64 discarded_bytes = 0;
	struct btrfs_bio *bbio = NULL;


	/*
	 * Avoid races with device replace and make sure our bbio has devices
	 * associated to its stripes that don't go away while we are discarding.
	 */
	btrfs_bio_counter_inc_blocked(fs_info);
	/* Tell the block device(s) that the sectors can be discarded */
	ret = btrfs_map_block(fs_info, BTRFS_MAP_DISCARD, bytenr, &num_bytes,
			      &bbio, 0);
	/* Error condition is -ENOMEM */
	if (!ret) {
		struct btrfs_bio_stripe *stripe = bbio->stripes;
		int i;


		for (i = 0; i < bbio->num_stripes; i++, stripe++) {
			u64 bytes;
			if (!stripe->dev->can_discard)
				continue;

			ret = btrfs_issue_discard(stripe->dev->bdev,
						  stripe->physical,
						  stripe->length,
						  &bytes);
			if (!ret)
				discarded_bytes += bytes;
			else if (ret != -EOPNOTSUPP)
				break; /* Logic errors or -ENOMEM, or -EIO but I don't know how that could happen JDM */

			/*
			 * Just in case we get back EOPNOTSUPP for some reason,
			 * just ignore the return value so we don't screw up
			 * people calling discard_extent.
			 */
			ret = 0;
		}
		btrfs_put_bbio(bbio);
	}
	btrfs_bio_counter_dec(fs_info);

	if (actual_bytes)
		*actual_bytes = discarded_bytes;


	if (ret == -EOPNOTSUPP)
		ret = 0;
	return ret;
}
					     struct btrfs_fs_info *fs_info,
					     unsigned long nr)
{
	struct btrfs_delayed_ref_root *delayed_refs;
	struct btrfs_delayed_ref_node *ref;
	struct btrfs_delayed_ref_head *locked_ref = NULL;
	struct btrfs_delayed_extent_op *extent_op;
	ktime_t start = ktime_get();
	int ret;
	unsigned long count = 0;
	unsigned long actual_count = 0;
	int must_insert_reserved = 0;

	delayed_refs = &trans->transaction->delayed_refs;
	while (1) {
		if (!locked_ref) {
			if (count >= nr)
				break;

			spin_lock(&delayed_refs->lock);
			locked_ref = btrfs_select_ref_head(trans);
			if (!locked_ref) {
				spin_unlock(&delayed_refs->lock);
				break;
			}

			/* grab the lock that says we are going to process
			 * all the refs for this head */
			ret = btrfs_delayed_ref_lock(trans, locked_ref);
			spin_unlock(&delayed_refs->lock);
			/*
			 * we may have dropped the spin lock to get the head
			 * mutex lock, and that might have given someone else
			 * time to free the head.  If that's true, it has been
			 * removed from our list and we can move on.
			 */
			if (ret == -EAGAIN) {
				locked_ref = NULL;
				count++;
				continue;
			}
		}

		/*
		 * We need to try and merge add/drops of the same ref since we
		 * can run into issues with relocate dropping the implicit ref
		 * and then it being added back again before the drop can
		 * finish.  If we merged anything we need to re-loop so we can
		 * get a good ref.
		 * Or we can get node references of the same type that weren't
		 * merged when created due to bumps in the tree mod seq, and
		 * we need to merge them to prevent adding an inline extent
		 * backref before dropping it (triggering a BUG_ON at
		 * insert_inline_extent_backref()).
		 */
		spin_lock(&locked_ref->lock);
		btrfs_merge_delayed_refs(trans, fs_info, delayed_refs,
					 locked_ref);

		/*
		 * locked_ref is the head node, so we have to go one
		 * node back for any delayed ref updates
		 */
		ref = select_delayed_ref(locked_ref);

		if (ref && ref->seq &&
		    btrfs_check_delayed_seq(fs_info, delayed_refs, ref->seq)) {
			spin_unlock(&locked_ref->lock);
			spin_lock(&delayed_refs->lock);
			locked_ref->processing = 0;
			delayed_refs->num_heads_ready++;
			spin_unlock(&delayed_refs->lock);
			btrfs_delayed_ref_unlock(locked_ref);
			locked_ref = NULL;
			cond_resched();
			count++;
			continue;
		}

		/*
		 * record the must insert reserved flag before we
		 * drop the spin lock.
		 */
		must_insert_reserved = locked_ref->must_insert_reserved;
		locked_ref->must_insert_reserved = 0;

		extent_op = locked_ref->extent_op;
		locked_ref->extent_op = NULL;

		if (!ref) {


			/* All delayed refs have been processed, Go ahead
			 * and send the head node to run_one_delayed_ref,
			 * so that any accounting fixes can happen
			 */
			ref = &locked_ref->node;

			if (extent_op && must_insert_reserved) {
				btrfs_free_delayed_extent_op(extent_op);
				extent_op = NULL;
			}

			if (extent_op) {
				spin_unlock(&locked_ref->lock);
				ret = run_delayed_extent_op(trans, fs_info,
							    ref, extent_op);
				btrfs_free_delayed_extent_op(extent_op);

				if (ret) {
					/*
					 * Need to reset must_insert_reserved if
					 * there was an error so the abort stuff
					 * can cleanup the reserved space
					 * properly.
					 */
					if (must_insert_reserved)
						locked_ref->must_insert_reserved = 1;
					spin_lock(&delayed_refs->lock);
					locked_ref->processing = 0;
					delayed_refs->num_heads_ready++;
					spin_unlock(&delayed_refs->lock);
					btrfs_debug(fs_info,
						    "run_delayed_extent_op returned %d",
						    ret);
					btrfs_delayed_ref_unlock(locked_ref);
					return ret;
				}
				continue;
			}

			/*
			 * Need to drop our head ref lock and re-acquire the
			 * delayed ref lock and then re-check to make sure
			 * nobody got added.
			 */
			spin_unlock(&locked_ref->lock);
			spin_lock(&delayed_refs->lock);
			spin_lock(&locked_ref->lock);
			if (!list_empty(&locked_ref->ref_list) ||
			    locked_ref->extent_op) {
				spin_unlock(&locked_ref->lock);
				spin_unlock(&delayed_refs->lock);
				continue;
			}
			ref->in_tree = 0;
			delayed_refs->num_heads--;
			rb_erase(&locked_ref->href_node,
				 &delayed_refs->href_root);
			spin_unlock(&delayed_refs->lock);
		} else {
			actual_count++;
			ref->in_tree = 0;
			list_del(&ref->list);
			if (!list_empty(&ref->add_list))
				list_del(&ref->add_list);
		}
		atomic_dec(&delayed_refs->num_entries);

		if (!btrfs_delayed_ref_is_head(ref)) {
			/*
			 * when we play the delayed ref, also correct the
			 * ref_mod on head
			 */
			switch (ref->action) {
			case BTRFS_ADD_DELAYED_REF:
			case BTRFS_ADD_DELAYED_EXTENT:
				locked_ref->node.ref_mod -= ref->ref_mod;
				break;
			case BTRFS_DROP_DELAYED_REF:
				locked_ref->node.ref_mod += ref->ref_mod;
				break;
			default:
				WARN_ON(1);
			}
		}
		spin_unlock(&locked_ref->lock);

		ret = run_one_delayed_ref(trans, fs_info, ref, extent_op,
					  must_insert_reserved);

		btrfs_free_delayed_extent_op(extent_op);
		if (ret) {
			spin_lock(&delayed_refs->lock);
			locked_ref->processing = 0;
			delayed_refs->num_heads_ready++;
			spin_unlock(&delayed_refs->lock);
			btrfs_delayed_ref_unlock(locked_ref);
			btrfs_put_delayed_ref(ref);
			btrfs_debug(fs_info, "run_one_delayed_ref returned %d",
				    ret);
			return ret;
		}

		/*
		 * If this node is a head, that means all the refs in this head
		 * have been dealt with, and we will pick the next head to deal
		 * with, so we must unlock the head and drop it from the cluster
		 * list before we release it.
		 */
		if (btrfs_delayed_ref_is_head(ref)) {
			if (locked_ref->is_data &&
			    locked_ref->total_ref_mod < 0) {
				spin_lock(&delayed_refs->lock);
				delayed_refs->pending_csums -= ref->num_bytes;
				spin_unlock(&delayed_refs->lock);
			}
			btrfs_delayed_ref_unlock(locked_ref);
			locked_ref = NULL;
		}
		btrfs_put_delayed_ref(ref);
		count++;
		cond_resched();
	}

	/*
	 * We don't want to include ref heads since we can have empty ref heads
	 * and those will drastically skew our runtime down since we just do
	 * accounting, no actual extent tree updates.
	 */
	if (actual_count > 0) {
		u64 runtime = ktime_to_ns(ktime_sub(ktime_get(), start));
		u64 avg;

		/*
		 * We weigh the current average higher than our current runtime
		 * to avoid large swings in the average.
		 */
		spin_lock(&delayed_refs->lock);
		avg = fs_info->avg_delayed_ref_runtime * 3 + runtime;
		fs_info->avg_delayed_ref_runtime = avg >> 2;	/* div by 4 */
		spin_unlock(&delayed_refs->lock);
	}
	return 0;
}
 */
static u64 find_middle(struct rb_root *root)
{
	struct rb_node *n = root->rb_node;
	struct btrfs_delayed_ref_node *entry;
	int alt = 1;
	u64 middle;
	u64 first = 0, last = 0;

	n = rb_first(root);
	if (n) {
		entry = rb_entry(n, struct btrfs_delayed_ref_node, rb_node);
		first = entry->bytenr;
	}
	n = rb_last(root);
	if (n) {
		entry = rb_entry(n, struct btrfs_delayed_ref_node, rb_node);
		last = entry->bytenr;
	}
	n = root->rb_node;

	while (n) {
		entry = rb_entry(n, struct btrfs_delayed_ref_node, rb_node);
		WARN_ON(!entry->in_tree);

		middle = entry->bytenr;

		if (alt)
			n = n->rb_left;
		else
			n = n->rb_right;

		alt = 1 - alt;
	}
	return middle;
}
int btrfs_run_delayed_refs(struct btrfs_trans_handle *trans,
			   struct btrfs_fs_info *fs_info, unsigned long count)
{
	struct rb_node *node;
	struct btrfs_delayed_ref_root *delayed_refs;
	struct btrfs_delayed_ref_head *head;
	int ret;
	int run_all = count == (unsigned long)-1;
	bool can_flush_pending_bgs = trans->can_flush_pending_bgs;

	/* We'll clean this up in btrfs_cleanup_transaction */
	if (trans->aborted)
		return 0;

	if (test_bit(BTRFS_FS_CREATING_FREE_SPACE_TREE, &fs_info->flags))
		return 0;

	delayed_refs = &trans->transaction->delayed_refs;
	if (count == 0)
		count = atomic_read(&delayed_refs->num_entries) * 2;

again:
#ifdef SCRAMBLE_DELAYED_REFS
	delayed_refs->run_delayed_start = find_middle(&delayed_refs->root);
#endif
	trans->can_flush_pending_bgs = false;
	ret = __btrfs_run_delayed_refs(trans, fs_info, count);
	if (ret < 0) {
		btrfs_abort_transaction(trans, ret);
		return ret;
	}

	if (run_all) {
		if (!list_empty(&trans->new_bgs))
			btrfs_create_pending_block_groups(trans, fs_info);

		spin_lock(&delayed_refs->lock);
		node = rb_first(&delayed_refs->href_root);
		if (!node) {
			spin_unlock(&delayed_refs->lock);
			goto out;
		}

		while (node) {
			head = rb_entry(node, struct btrfs_delayed_ref_head,
					href_node);
			if (btrfs_delayed_ref_is_head(&head->node)) {
				struct btrfs_delayed_ref_node *ref;

				ref = &head->node;
				refcount_inc(&ref->refs);

				spin_unlock(&delayed_refs->lock);
				/*
				 * Mutex was contended, block until it's
				 * released and try again
				 */
				mutex_lock(&head->mutex);
				mutex_unlock(&head->mutex);

				btrfs_put_delayed_ref(ref);
				cond_resched();
				goto again;
			} else {
				WARN_ON(1);
			}
			node = rb_next(node);
		}
		spin_unlock(&delayed_refs->lock);
		cond_resched();
		goto again;
	}
out:
	trans->can_flush_pending_bgs = can_flush_pending_bgs;
	return 0;
}
int btrfs_cross_ref_exist(struct btrfs_root *root, u64 objectid, u64 offset,
			  u64 bytenr)
{
	struct btrfs_path *path;
	int ret;
	int ret2;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOENT;

	do {
		ret = check_committed_ref(root, path, objectid,
					  offset, bytenr);
		if (ret && ret != -ENOENT)
			goto out;

		ret2 = check_delayed_ref(root, path, objectid,
					 offset, bytenr);
	} while (ret2 == -EAGAIN);

	if (ret2 && ret2 != -ENOENT) {
		ret = ret2;
		goto out;
	}

	if (ret != -ENOENT || ret2 != -ENOENT)
		ret = 0;
out:
	btrfs_free_path(path);
	if (root->root_key.objectid == BTRFS_DATA_RELOC_TREE_OBJECTID)
		WARN_ON(ret > 0);
	return ret;
}
			   struct extent_buffer *buf,
			   int full_backref, int inc)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 bytenr;
	u64 num_bytes;
	u64 parent;
	u64 ref_root;
	u32 nritems;
	struct btrfs_key key;
	struct btrfs_file_extent_item *fi;
	int i;
	int level;
	int ret = 0;
	int (*process_func)(struct btrfs_trans_handle *,
			    struct btrfs_fs_info *,
			    u64, u64, u64, u64, u64, u64);


	if (btrfs_is_testing(fs_info))
		return 0;

	ref_root = btrfs_header_owner(buf);
	nritems = btrfs_header_nritems(buf);
	level = btrfs_header_level(buf);

	if (!test_bit(BTRFS_ROOT_REF_COWS, &root->state) && level == 0)
		return 0;

	if (inc)
		process_func = btrfs_inc_extent_ref;
	else
		process_func = btrfs_free_extent;

	if (full_backref)
		parent = buf->start;
	else
		parent = 0;

	for (i = 0; i < nritems; i++) {
		if (level == 0) {
			btrfs_item_key_to_cpu(buf, &key, i);
			if (key.type != BTRFS_EXTENT_DATA_KEY)
				continue;
			fi = btrfs_item_ptr(buf, i,
					    struct btrfs_file_extent_item);
			if (btrfs_file_extent_type(buf, fi) ==
			    BTRFS_FILE_EXTENT_INLINE)
				continue;
			bytenr = btrfs_file_extent_disk_bytenr(buf, fi);
			if (bytenr == 0)
				continue;

			num_bytes = btrfs_file_extent_disk_num_bytes(buf, fi);
			key.offset -= btrfs_file_extent_offset(buf, fi);
			ret = process_func(trans, fs_info, bytenr, num_bytes,
					   parent, ref_root, key.objectid,
					   key.offset);
			if (ret)
				goto fail;
		} else {
			bytenr = btrfs_node_blockptr(buf, i);
			num_bytes = fs_info->nodesize;
			ret = process_func(trans, fs_info, bytenr, num_bytes,
					   parent, ref_root, level - 1, 0);
			if (ret)
				goto fail;
		}
	}
	return 0;
fail:
	return ret;
}
int btrfs_start_dirty_block_groups(struct btrfs_trans_handle *trans,
				   struct btrfs_fs_info *fs_info)
{
	struct btrfs_block_group_cache *cache;
	struct btrfs_transaction *cur_trans = trans->transaction;
	int ret = 0;
	int should_put;
	struct btrfs_path *path = NULL;
	LIST_HEAD(dirty);
	struct list_head *io = &cur_trans->io_bgs;
	int num_started = 0;
	int loops = 0;

	spin_lock(&cur_trans->dirty_bgs_lock);
	if (list_empty(&cur_trans->dirty_bgs)) {
		spin_unlock(&cur_trans->dirty_bgs_lock);
		return 0;
	}
	list_splice_init(&cur_trans->dirty_bgs, &dirty);
	spin_unlock(&cur_trans->dirty_bgs_lock);

again:
	/*
	 * make sure all the block groups on our dirty list actually
	 * exist
	 */
	btrfs_create_pending_block_groups(trans, fs_info);

	if (!path) {
		path = btrfs_alloc_path();
		if (!path)
			return -ENOMEM;
	}

	/*
	 * cache_write_mutex is here only to save us from balance or automatic
	 * removal of empty block groups deleting this block group while we are
	 * writing out the cache
	 */
	mutex_lock(&trans->transaction->cache_write_mutex);
	while (!list_empty(&dirty)) {
		cache = list_first_entry(&dirty,
					 struct btrfs_block_group_cache,
					 dirty_list);
		/*
		 * this can happen if something re-dirties a block
		 * group that is already under IO.  Just wait for it to
		 * finish and then do it all again
		 */
		if (!list_empty(&cache->io_list)) {
			list_del_init(&cache->io_list);
			btrfs_wait_cache_io(trans, cache, path);
			btrfs_put_block_group(cache);
		}


		/*
		 * btrfs_wait_cache_io uses the cache->dirty_list to decide
		 * if it should update the cache_state.  Don't delete
		 * until after we wait.
		 *
		 * Since we're not running in the commit critical section
		 * we need the dirty_bgs_lock to protect from update_block_group
		 */
		spin_lock(&cur_trans->dirty_bgs_lock);
		list_del_init(&cache->dirty_list);
		spin_unlock(&cur_trans->dirty_bgs_lock);

		should_put = 1;

		cache_save_setup(cache, trans, path);

		if (cache->disk_cache_state == BTRFS_DC_SETUP) {
			cache->io_ctl.inode = NULL;
			ret = btrfs_write_out_cache(fs_info, trans,
						    cache, path);
			if (ret == 0 && cache->io_ctl.inode) {
				num_started++;
				should_put = 0;

				/*
				 * the cache_write_mutex is protecting
				 * the io_list
				 */
				list_add_tail(&cache->io_list, io);
			} else {
				/*
				 * if we failed to write the cache, the
				 * generation will be bad and life goes on
				 */
				ret = 0;
			}
		}
		if (!ret) {
			ret = write_one_cache_group(trans, fs_info,
						    path, cache);
			/*
			 * Our block group might still be attached to the list
			 * of new block groups in the transaction handle of some
			 * other task (struct btrfs_trans_handle->new_bgs). This
			 * means its block group item isn't yet in the extent
			 * tree. If this happens ignore the error, as we will
			 * try again later in the critical section of the
			 * transaction commit.
			 */
			if (ret == -ENOENT) {
				ret = 0;
				spin_lock(&cur_trans->dirty_bgs_lock);
				if (list_empty(&cache->dirty_list)) {
					list_add_tail(&cache->dirty_list,
						      &cur_trans->dirty_bgs);
					btrfs_get_block_group(cache);
				}
				spin_unlock(&cur_trans->dirty_bgs_lock);
			} else if (ret) {
				btrfs_abort_transaction(trans, ret);
			}
		}

		/* if its not on the io list, we need to put the block group */
		if (should_put)
			btrfs_put_block_group(cache);

		if (ret)
			break;

		/*
		 * Avoid blocking other tasks for too long. It might even save
		 * us from writing caches for block groups that are going to be
		 * removed.
		 */
		mutex_unlock(&trans->transaction->cache_write_mutex);
		mutex_lock(&trans->transaction->cache_write_mutex);
	}
	mutex_unlock(&trans->transaction->cache_write_mutex);

	/*
	 * go through delayed refs for all the stuff we've just kicked off
	 * and then loop back (just once)
	 */
	ret = btrfs_run_delayed_refs(trans, fs_info, 0);
	if (!ret && loops == 0) {
		loops++;
		spin_lock(&cur_trans->dirty_bgs_lock);
		list_splice_init(&cur_trans->dirty_bgs, &dirty);
		/*
		 * dirty_bgs_lock protects us from concurrent block group
		 * deletes too (not just cache_write_mutex).
		 */
		if (!list_empty(&dirty)) {
			spin_unlock(&cur_trans->dirty_bgs_lock);
			goto again;
		}
		spin_unlock(&cur_trans->dirty_bgs_lock);
	} else if (ret < 0) {
		btrfs_cleanup_dirty_bgs(cur_trans, fs_info);
	}

	btrfs_free_path(path);
	return ret;
}
int btrfs_write_dirty_block_groups(struct btrfs_trans_handle *trans,
				   struct btrfs_fs_info *fs_info)
{
	struct btrfs_block_group_cache *cache;
	struct btrfs_transaction *cur_trans = trans->transaction;
	int ret = 0;
	int should_put;
	struct btrfs_path *path;
	struct list_head *io = &cur_trans->io_bgs;
	int num_started = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	/*
	 * Even though we are in the critical section of the transaction commit,
	 * we can still have concurrent tasks adding elements to this
	 * transaction's list of dirty block groups. These tasks correspond to
	 * endio free space workers started when writeback finishes for a
	 * space cache, which run inode.c:btrfs_finish_ordered_io(), and can
	 * allocate new block groups as a result of COWing nodes of the root
	 * tree when updating the free space inode. The writeback for the space
	 * caches is triggered by an earlier call to
	 * btrfs_start_dirty_block_groups() and iterations of the following
	 * loop.
	 * Also we want to do the cache_save_setup first and then run the
	 * delayed refs to make sure we have the best chance at doing this all
	 * in one shot.
	 */
	spin_lock(&cur_trans->dirty_bgs_lock);
	while (!list_empty(&cur_trans->dirty_bgs)) {
		cache = list_first_entry(&cur_trans->dirty_bgs,
					 struct btrfs_block_group_cache,
					 dirty_list);

		/*
		 * this can happen if cache_save_setup re-dirties a block
		 * group that is already under IO.  Just wait for it to
		 * finish and then do it all again
		 */
		if (!list_empty(&cache->io_list)) {
			spin_unlock(&cur_trans->dirty_bgs_lock);
			list_del_init(&cache->io_list);
			btrfs_wait_cache_io(trans, cache, path);
			btrfs_put_block_group(cache);
			spin_lock(&cur_trans->dirty_bgs_lock);
		}

		/*
		 * don't remove from the dirty list until after we've waited
		 * on any pending IO
		 */
		list_del_init(&cache->dirty_list);
		spin_unlock(&cur_trans->dirty_bgs_lock);
		should_put = 1;

		cache_save_setup(cache, trans, path);

		if (!ret)
			ret = btrfs_run_delayed_refs(trans, fs_info,
						     (unsigned long) -1);

		if (!ret && cache->disk_cache_state == BTRFS_DC_SETUP) {
			cache->io_ctl.inode = NULL;
			ret = btrfs_write_out_cache(fs_info, trans,
						    cache, path);
			if (ret == 0 && cache->io_ctl.inode) {
				num_started++;
				should_put = 0;
				list_add_tail(&cache->io_list, io);
			} else {
				/*
				 * if we failed to write the cache, the
				 * generation will be bad and life goes on
				 */
				ret = 0;
			}
		}
		if (!ret) {
			ret = write_one_cache_group(trans, fs_info,
						    path, cache);
			/*
			 * One of the free space endio workers might have
			 * created a new block group while updating a free space
			 * cache's inode (at inode.c:btrfs_finish_ordered_io())
			 * and hasn't released its transaction handle yet, in
			 * which case the new block group is still attached to
			 * its transaction handle and its creation has not
			 * finished yet (no block group item in the extent tree
			 * yet, etc). If this is the case, wait for all free
			 * space endio workers to finish and retry. This is a
			 * a very rare case so no need for a more efficient and
			 * complex approach.
			 */
			if (ret == -ENOENT) {
				wait_event(cur_trans->writer_wait,
				   atomic_read(&cur_trans->num_writers) == 1);
				ret = write_one_cache_group(trans, fs_info,
							    path, cache);
			}
			if (ret)
				btrfs_abort_transaction(trans, ret);
		}

		/* if its not on the io list, we need to put the block group */
		if (should_put)
			btrfs_put_block_group(cache);
		spin_lock(&cur_trans->dirty_bgs_lock);
	}
	spin_unlock(&cur_trans->dirty_bgs_lock);

	while (!list_empty(io)) {
		cache = list_first_entry(io, struct btrfs_block_group_cache,
					 io_list);
		list_del_init(&cache->io_list);
		btrfs_wait_cache_io(trans, cache, path);
		btrfs_put_block_group(cache);
	}

	btrfs_free_path(path);
	return ret;
}
			     u64 bytes_readonly,
			     struct btrfs_space_info **space_info)
{
	struct btrfs_space_info *found;
	int i;
	int factor;
	int ret;

	if (flags & (BTRFS_BLOCK_GROUP_DUP | BTRFS_BLOCK_GROUP_RAID1 |
		     BTRFS_BLOCK_GROUP_RAID10))
		factor = 2;
	else
		factor = 1;

	found = __find_space_info(info, flags);
	if (found) {
		spin_lock(&found->lock);
		found->total_bytes += total_bytes;
		found->disk_total += total_bytes * factor;
		found->bytes_used += bytes_used;
		found->disk_used += bytes_used * factor;
		found->bytes_readonly += bytes_readonly;
		if (total_bytes > 0)
			found->full = 0;
		space_info_add_new_bytes(info, found, total_bytes -
					 bytes_used - bytes_readonly);
		spin_unlock(&found->lock);
		*space_info = found;
		return 0;
	}
	found = kzalloc(sizeof(*found), GFP_NOFS);
	if (!found)
		return -ENOMEM;

	ret = percpu_counter_init(&found->total_bytes_pinned, 0, GFP_KERNEL);
	if (ret) {
		kfree(found);
		return ret;
	}

	for (i = 0; i < BTRFS_NR_RAID_TYPES; i++)
		INIT_LIST_HEAD(&found->block_groups[i]);
	init_rwsem(&found->groups_sem);
	spin_lock_init(&found->lock);
	found->flags = flags & BTRFS_BLOCK_GROUP_TYPE_MASK;
	found->total_bytes = total_bytes;
	found->disk_total = total_bytes * factor;
	found->bytes_used = bytes_used;
	found->disk_used = bytes_used * factor;
	found->bytes_pinned = 0;
	found->bytes_reserved = 0;
	found->bytes_readonly = bytes_readonly;
	found->bytes_may_use = 0;
	found->full = 0;
	found->max_extent_size = 0;
	found->force_alloc = CHUNK_ALLOC_NO_FORCE;
	found->chunk_alloc = 0;
	found->flush = 0;
	init_waitqueue_head(&found->wait);
	INIT_LIST_HEAD(&found->ro_bgs);
	INIT_LIST_HEAD(&found->tickets);
	INIT_LIST_HEAD(&found->priority_tickets);

	ret = kobject_init_and_add(&found->kobj, &space_info_ktype,
				    info->space_info_kobj, "%s",
				    alloc_name(found->flags));
	if (ret) {
		percpu_counter_destroy(&found->total_bytes_pinned);
		kfree(found);
		return ret;
	}

	*space_info = found;
	list_add_rcu(&found->list, &info->space_info);
	if (flags & BTRFS_BLOCK_GROUP_DATA)
		info->data_sinfo = found;

	return ret;
}
 */
static u64 btrfs_reduce_alloc_profile(struct btrfs_fs_info *fs_info, u64 flags)
{
	u64 num_devices = fs_info->fs_devices->rw_devices;
	u64 target;
	u64 raid_type;
	u64 allowed = 0;

	/*
	 * see if restripe for this chunk_type is in progress, if so
	 * try to reduce to the target profile
	 */
	spin_lock(&fs_info->balance_lock);
	target = get_restripe_target(fs_info, flags);
	if (target) {
		/* pick target profile only if it's already available */
		if ((flags & target) & BTRFS_EXTENDED_PROFILE_MASK) {
			spin_unlock(&fs_info->balance_lock);
			return extended_to_chunk(target);
		}
	}
	spin_unlock(&fs_info->balance_lock);

	/* First, mask out the RAID levels which aren't possible */
	for (raid_type = 0; raid_type < BTRFS_NR_RAID_TYPES; raid_type++) {
		if (num_devices >= btrfs_raid_array[raid_type].devs_min)
			allowed |= btrfs_raid_group[raid_type];
	}
	allowed &= flags;

	if (allowed & BTRFS_BLOCK_GROUP_RAID6)
		allowed = BTRFS_BLOCK_GROUP_RAID6;
	else if (allowed & BTRFS_BLOCK_GROUP_RAID5)
		allowed = BTRFS_BLOCK_GROUP_RAID5;
	else if (allowed & BTRFS_BLOCK_GROUP_RAID10)
		allowed = BTRFS_BLOCK_GROUP_RAID10;
	else if (allowed & BTRFS_BLOCK_GROUP_RAID1)
		allowed = BTRFS_BLOCK_GROUP_RAID1;
	else if (allowed & BTRFS_BLOCK_GROUP_RAID0)
		allowed = BTRFS_BLOCK_GROUP_RAID0;

	flags &= ~BTRFS_BLOCK_GROUP_PROFILE_MASK;

	return extended_to_chunk(flags | allowed);
}

static u64 get_alloc_profile(struct btrfs_fs_info *fs_info, u64 orig_flags)
{
	unsigned seq;
	u64 flags;

	do {
		flags = orig_flags;
		seq = read_seqbegin(&fs_info->profiles_lock);

		if (flags & BTRFS_BLOCK_GROUP_DATA)
			flags |= fs_info->avail_data_alloc_bits;
		else if (flags & BTRFS_BLOCK_GROUP_SYSTEM)
			flags |= fs_info->avail_system_alloc_bits;
		else if (flags & BTRFS_BLOCK_GROUP_METADATA)
			flags |= fs_info->avail_metadata_alloc_bits;
	} while (read_seqretry(&fs_info->profiles_lock, seq));

	return btrfs_reduce_alloc_profile(fs_info, flags);
}
static void shrink_delalloc(struct btrfs_root *root, u64 to_reclaim, u64 orig,
			    bool wait_ordered)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_block_rsv *block_rsv;
	struct btrfs_space_info *space_info;
	struct btrfs_trans_handle *trans;
	u64 delalloc_bytes;
	u64 max_reclaim;
	long time_left;
	unsigned long nr_pages;
	int loops;
	int items;
	enum btrfs_reserve_flush_enum flush;

	/* Calc the number of the pages we need flush for space reservation */
	items = calc_reclaim_items_nr(fs_info, to_reclaim);
	to_reclaim = (u64)items * EXTENT_SIZE_PER_ITEM;

	trans = (struct btrfs_trans_handle *)current->journal_info;
	block_rsv = &fs_info->delalloc_block_rsv;
	space_info = block_rsv->space_info;

	delalloc_bytes = percpu_counter_sum_positive(
						&fs_info->delalloc_bytes);
	if (delalloc_bytes == 0) {
		if (trans)
			return;
		if (wait_ordered)
			btrfs_wait_ordered_roots(fs_info, items, 0, (u64)-1);
		return;
	}

	loops = 0;
	while (delalloc_bytes && loops < 3) {
		max_reclaim = min(delalloc_bytes, to_reclaim);
		nr_pages = max_reclaim >> PAGE_SHIFT;
		btrfs_writeback_inodes_sb_nr(fs_info, nr_pages, items);
		/*
		 * We need to wait for the async pages to actually start before
		 * we do anything.
		 */
		max_reclaim = atomic_read(&fs_info->async_delalloc_pages);
		if (!max_reclaim)
			goto skip_async;

		if (max_reclaim <= nr_pages)
			max_reclaim = 0;
		else
			max_reclaim -= nr_pages;

		wait_event(fs_info->async_submit_wait,
			   atomic_read(&fs_info->async_delalloc_pages) <=
			   (int)max_reclaim);
skip_async:
		if (!trans)
			flush = BTRFS_RESERVE_FLUSH_ALL;
		else
			flush = BTRFS_RESERVE_NO_FLUSH;
		spin_lock(&space_info->lock);
		if (can_overcommit(root, space_info, orig, flush)) {
			spin_unlock(&space_info->lock);
			break;
		}
		if (list_empty(&space_info->tickets) &&
		    list_empty(&space_info->priority_tickets)) {
			spin_unlock(&space_info->lock);
			break;
		}
		spin_unlock(&space_info->lock);

		loops++;
		if (wait_ordered && !trans) {
			btrfs_wait_ordered_roots(fs_info, items, 0, (u64)-1);
		} else {
			time_left = schedule_timeout_killable(1);
			if (time_left)
				break;
		}
		delalloc_bytes = percpu_counter_sum_positive(
						&fs_info->delalloc_bytes);
	}
}

static void wake_all_tickets(struct list_head *head)
{
	struct reserve_ticket *ticket;

	while (!list_empty(head)) {
		ticket = list_first_entry(head, struct reserve_ticket, list);
		list_del_init(&ticket->list);
		ticket->error = -ENOSPC;
		wake_up(&ticket->wait);
	}
}
 */
static void btrfs_async_reclaim_metadata_space(struct work_struct *work)
{
	struct btrfs_fs_info *fs_info;
	struct btrfs_space_info *space_info;
	u64 to_reclaim;
	int flush_state;
	int commit_cycles = 0;
	u64 last_tickets_id;

	fs_info = container_of(work, struct btrfs_fs_info, async_reclaim_work);
	space_info = __find_space_info(fs_info, BTRFS_BLOCK_GROUP_METADATA);

	spin_lock(&space_info->lock);
	to_reclaim = btrfs_calc_reclaim_metadata_size(fs_info->fs_root,
						      space_info);
	if (!to_reclaim) {
		space_info->flush = 0;
		spin_unlock(&space_info->lock);
		return;
	}
	last_tickets_id = space_info->tickets_id;
	spin_unlock(&space_info->lock);

	flush_state = FLUSH_DELAYED_ITEMS_NR;
	do {
		struct reserve_ticket *ticket;
		int ret;

		ret = flush_space(fs_info, space_info, to_reclaim, to_reclaim,
				  flush_state);
		spin_lock(&space_info->lock);
		if (list_empty(&space_info->tickets)) {
			space_info->flush = 0;
			spin_unlock(&space_info->lock);
			return;
		}
		to_reclaim = btrfs_calc_reclaim_metadata_size(fs_info->fs_root,
							      space_info);
		ticket = list_first_entry(&space_info->tickets,
					  struct reserve_ticket, list);
		if (last_tickets_id == space_info->tickets_id) {
			flush_state++;
		} else {
			last_tickets_id = space_info->tickets_id;
			flush_state = FLUSH_DELAYED_ITEMS_NR;
			if (commit_cycles)
				commit_cycles--;
		}

		if (flush_state > COMMIT_TRANS) {
			commit_cycles++;
			if (commit_cycles > 2) {
				wake_all_tickets(&space_info->tickets);
				space_info->flush = 0;
			} else {
				flush_state = FLUSH_DELAYED_ITEMS_NR;
			}
		}
		spin_unlock(&space_info->lock);
	} while (flush_state <= COMMIT_TRANS);
}
					    struct btrfs_space_info *space_info,
					    struct reserve_ticket *ticket)
{
	u64 to_reclaim;
	int flush_state = FLUSH_DELAYED_ITEMS_NR;

	spin_lock(&space_info->lock);
	to_reclaim = btrfs_calc_reclaim_metadata_size(fs_info->extent_root,
						      space_info);
	if (!to_reclaim) {
		spin_unlock(&space_info->lock);
		return;
	}
	spin_unlock(&space_info->lock);

	do {
		flush_space(fs_info, space_info, to_reclaim, to_reclaim,
			    flush_state);
		flush_state++;
		spin_lock(&space_info->lock);
		if (ticket->bytes == 0) {
			spin_unlock(&space_info->lock);
			return;
		}
		spin_unlock(&space_info->lock);

		/*
		 * Priority flushers can't wait on delalloc without
		 * deadlocking.
		 */
		if (flush_state == FLUSH_DELALLOC ||
		    flush_state == FLUSH_DELALLOC_WAIT)
			flush_state = ALLOC_CHUNK;
	} while (flush_state < COMMIT_TRANS);
}
			       struct reserve_ticket *ticket, u64 orig_bytes)

{
	DEFINE_WAIT(wait);
	int ret = 0;

	spin_lock(&space_info->lock);
	while (ticket->bytes > 0 && ticket->error == 0) {
		ret = prepare_to_wait_event(&ticket->wait, &wait, TASK_KILLABLE);
		if (ret) {
			ret = -EINTR;
			break;
		}
		spin_unlock(&space_info->lock);

		schedule();

		finish_wait(&ticket->wait, &wait);
		spin_lock(&space_info->lock);
	}
	if (!ret)
		ret = ticket->error;
	if (!list_empty(&ticket->list))
		list_del_init(&ticket->list);
	if (ticket->bytes && ticket->bytes < orig_bytes) {
		u64 num_bytes = orig_bytes - ticket->bytes;
		space_info->bytes_may_use -= num_bytes;
		trace_btrfs_space_reservation(fs_info, "space_info",
					      space_info->flags, num_bytes, 0);
	}
	spin_unlock(&space_info->lock);

	return ret;
}
				     struct btrfs_space_info *space_info,
				     u64 num_bytes)
{
	struct reserve_ticket *ticket;
	struct list_head *head;
	u64 used;
	enum btrfs_reserve_flush_enum flush = BTRFS_RESERVE_NO_FLUSH;
	bool check_overcommit = false;

	spin_lock(&space_info->lock);
	head = &space_info->priority_tickets;

	/*
	 * If we are over our limit then we need to check and see if we can
	 * overcommit, and if we can't then we just need to free up our space
	 * and not satisfy any requests.
	 */
	used = space_info->bytes_used + space_info->bytes_reserved +
		space_info->bytes_pinned + space_info->bytes_readonly +
		space_info->bytes_may_use;
	if (used - num_bytes >= space_info->total_bytes)
		check_overcommit = true;
again:
	while (!list_empty(head) && num_bytes) {
		ticket = list_first_entry(head, struct reserve_ticket,
					  list);
		/*
		 * We use 0 bytes because this space is already reserved, so
		 * adding the ticket space would be a double count.
		 */
		if (check_overcommit &&
		    !can_overcommit(fs_info->extent_root, space_info, 0,
				    flush))
			break;
		if (num_bytes >= ticket->bytes) {
			list_del_init(&ticket->list);
			num_bytes -= ticket->bytes;
			ticket->bytes = 0;
			space_info->tickets_id++;
			wake_up(&ticket->wait);
		} else {
			ticket->bytes -= num_bytes;
			num_bytes = 0;
		}
	}

	if (num_bytes && head == &space_info->priority_tickets) {
		head = &space_info->tickets;
		flush = BTRFS_RESERVE_FLUSH_ALL;
		goto again;
	}
	space_info->bytes_may_use -= num_bytes;
	trace_btrfs_space_reservation(fs_info, "space_info",
				      space_info->flags, num_bytes, 0);
	spin_unlock(&space_info->lock);
}
				     struct btrfs_space_info *space_info,
				     u64 num_bytes)
{
	struct reserve_ticket *ticket;
	struct list_head *head = &space_info->priority_tickets;

again:
	while (!list_empty(head) && num_bytes) {
		ticket = list_first_entry(head, struct reserve_ticket,
					  list);
		if (num_bytes >= ticket->bytes) {
			trace_btrfs_space_reservation(fs_info, "space_info",
						      space_info->flags,
						      ticket->bytes, 1);
			list_del_init(&ticket->list);
			num_bytes -= ticket->bytes;
			space_info->bytes_may_use += ticket->bytes;
			ticket->bytes = 0;
			space_info->tickets_id++;
			wake_up(&ticket->wait);
		} else {
			trace_btrfs_space_reservation(fs_info, "space_info",
						      space_info->flags,
						      num_bytes, 1);
			space_info->bytes_may_use += num_bytes;
			ticket->bytes -= num_bytes;
			num_bytes = 0;
		}
	}

	if (num_bytes && head == &space_info->priority_tickets) {
		head = &space_info->tickets;
		goto again;
	}
}
			      struct btrfs_fs_info *info, u64 bytenr,
			      u64 num_bytes, int alloc)
{
	struct btrfs_block_group_cache *cache = NULL;
	u64 total = num_bytes;
	u64 old_val;
	u64 byte_in_group;
	int factor;

	/* block accounting for super block */
	spin_lock(&info->delalloc_root_lock);
	old_val = btrfs_super_bytes_used(info->super_copy);
	if (alloc)
		old_val += num_bytes;
	else
		old_val -= num_bytes;
	btrfs_set_super_bytes_used(info->super_copy, old_val);
	spin_unlock(&info->delalloc_root_lock);

	while (total) {
		cache = btrfs_lookup_block_group(info, bytenr);
		if (!cache)
			return -ENOENT;
		if (cache->flags & (BTRFS_BLOCK_GROUP_DUP |
				    BTRFS_BLOCK_GROUP_RAID1 |
				    BTRFS_BLOCK_GROUP_RAID10))
			factor = 2;
		else
			factor = 1;
		/*
		 * If this block group has free space cache written out, we
		 * need to make sure to load it if we are removing space.  This
		 * is because we need the unpinning stage to actually add the
		 * space back to the block group, otherwise we will leak space.
		 */
		if (!alloc && cache->cached == BTRFS_CACHE_NO)
			cache_block_group(cache, 1);

		byte_in_group = bytenr - cache->key.objectid;
		WARN_ON(byte_in_group > cache->key.offset);

		spin_lock(&cache->space_info->lock);
		spin_lock(&cache->lock);

		if (btrfs_test_opt(info, SPACE_CACHE) &&
		    cache->disk_cache_state < BTRFS_DC_CLEAR)
			cache->disk_cache_state = BTRFS_DC_CLEAR;

		old_val = btrfs_block_group_used(&cache->item);
		num_bytes = min(total, cache->key.offset - byte_in_group);
		if (alloc) {
			old_val += num_bytes;
			btrfs_set_block_group_used(&cache->item, old_val);
			cache->reserved -= num_bytes;
			cache->space_info->bytes_reserved -= num_bytes;
			cache->space_info->bytes_used += num_bytes;
			cache->space_info->disk_used += num_bytes * factor;
			spin_unlock(&cache->lock);
			spin_unlock(&cache->space_info->lock);
		} else {
			old_val -= num_bytes;
			btrfs_set_block_group_used(&cache->item, old_val);
			cache->pinned += num_bytes;
			cache->space_info->bytes_pinned += num_bytes;
			cache->space_info->bytes_used -= num_bytes;
			cache->space_info->disk_used -= num_bytes * factor;
			spin_unlock(&cache->lock);
			spin_unlock(&cache->space_info->lock);

			trace_btrfs_space_reservation(info, "pinned",
						      cache->space_info->flags,
						      num_bytes, 1);
			set_extent_dirty(info->pinned_extents,
					 bytenr, bytenr + num_bytes - 1,
					 GFP_NOFS | __GFP_NOFAIL);
		}

		spin_lock(&trans->transaction->dirty_bgs_lock);
		if (list_empty(&cache->dirty_list)) {
			list_add_tail(&cache->dirty_list,
				      &trans->transaction->dirty_bgs);
				trans->transaction->num_dirty_bgs++;
			btrfs_get_block_group(cache);
		}
		spin_unlock(&trans->transaction->dirty_bgs_lock);

		/*
		 * No longer have used bytes in this block group, queue it for
		 * deletion. We do this after adding the block group to the
		 * dirty list to avoid races between cleaner kthread and space
		 * cache writeout.
		 */
		if (!alloc && old_val == 0) {
			spin_lock(&info->unused_bgs_lock);
			if (list_empty(&cache->bg_list)) {
				btrfs_get_block_group(cache);
				list_add_tail(&cache->bg_list,
					      &info->unused_bgs);
			}
			spin_unlock(&info->unused_bgs_lock);
		}

		btrfs_put_block_group(cache);
		total -= num_bytes;
		bytenr += num_bytes;
	}
	return 0;
}
int btrfs_exclude_logged_extents(struct btrfs_fs_info *fs_info,
				 struct extent_buffer *eb)
{
	struct btrfs_file_extent_item *item;
	struct btrfs_key key;
	int found_type;
	int i;

	if (!btrfs_fs_incompat(fs_info, MIXED_GROUPS))
		return 0;

	for (i = 0; i < btrfs_header_nritems(eb); i++) {
		btrfs_item_key_to_cpu(eb, &key, i);
		if (key.type != BTRFS_EXTENT_DATA_KEY)
			continue;
		item = btrfs_item_ptr(eb, i, struct btrfs_file_extent_item);
		found_type = btrfs_file_extent_type(eb, item);
		if (found_type == BTRFS_FILE_EXTENT_INLINE)
			continue;
		if (btrfs_file_extent_disk_bytenr(eb, item) == 0)
			continue;
		key.objectid = btrfs_file_extent_disk_bytenr(eb, item);
		key.offset = btrfs_file_extent_disk_num_bytes(eb, item);
		__exclude_logged_extent(fs_info, key.objectid, key.offset);
	}

	return 0;
}
			      u64 start, u64 end,
			      const bool return_free_space)
{
	struct btrfs_block_group_cache *cache = NULL;
	struct btrfs_space_info *space_info;
	struct btrfs_block_rsv *global_rsv = &fs_info->global_block_rsv;
	struct btrfs_free_cluster *cluster = NULL;
	u64 len;
	u64 total_unpinned = 0;
	u64 empty_cluster = 0;
	bool readonly;

	while (start <= end) {
		readonly = false;
		if (!cache ||
		    start >= cache->key.objectid + cache->key.offset) {
			if (cache)
				btrfs_put_block_group(cache);
			total_unpinned = 0;
			cache = btrfs_lookup_block_group(fs_info, start);
			BUG_ON(!cache); /* Logic error */

			cluster = fetch_cluster_info(fs_info,
						     cache->space_info,
						     &empty_cluster);
			empty_cluster <<= 1;
		}

		len = cache->key.objectid + cache->key.offset - start;
		len = min(len, end + 1 - start);

		if (start < cache->last_byte_to_unpin) {
			len = min(len, cache->last_byte_to_unpin - start);
			if (return_free_space)
				btrfs_add_free_space(cache, start, len);
		}

		start += len;
		total_unpinned += len;
		space_info = cache->space_info;

		/*
		 * If this space cluster has been marked as fragmented and we've
		 * unpinned enough in this block group to potentially allow a
		 * cluster to be created inside of it go ahead and clear the
		 * fragmented check.
		 */
		if (cluster && cluster->fragmented &&
		    total_unpinned > empty_cluster) {
			spin_lock(&cluster->lock);
			cluster->fragmented = 0;
			spin_unlock(&cluster->lock);
		}

		spin_lock(&space_info->lock);
		spin_lock(&cache->lock);
		cache->pinned -= len;
		space_info->bytes_pinned -= len;

		trace_btrfs_space_reservation(fs_info, "pinned",
					      space_info->flags, len, 0);
		space_info->max_extent_size = 0;
		percpu_counter_add(&space_info->total_bytes_pinned, -len);
		if (cache->ro) {
			space_info->bytes_readonly += len;
			readonly = true;
		}
		spin_unlock(&cache->lock);
		if (!readonly && return_free_space &&
		    global_rsv->space_info == space_info) {
			u64 to_add = len;
			WARN_ON(!return_free_space);
			spin_lock(&global_rsv->lock);
			if (!global_rsv->full) {
				to_add = min(len, global_rsv->size -
					     global_rsv->reserved);
				global_rsv->reserved += to_add;
				space_info->bytes_may_use += to_add;
				if (global_rsv->reserved >= global_rsv->size)
					global_rsv->full = 1;
				trace_btrfs_space_reservation(fs_info,
							      "space_info",
							      space_info->flags,
							      to_add, 1);
				len -= to_add;
			}
			spin_unlock(&global_rsv->lock);
			/* Add to any tickets we may have */
			if (len)
				space_info_add_new_bytes(fs_info, space_info,
							 len);
		}
		spin_unlock(&space_info->lock);
	}

	if (cache)
		btrfs_put_block_group(cache);
	return 0;
}
int btrfs_finish_extent_commit(struct btrfs_trans_handle *trans,
			       struct btrfs_fs_info *fs_info)
{
	struct btrfs_block_group_cache *block_group, *tmp;
	struct list_head *deleted_bgs;
	struct extent_io_tree *unpin;
	u64 start;
	u64 end;
	int ret;

	if (fs_info->pinned_extents == &fs_info->freed_extents[0])
		unpin = &fs_info->freed_extents[1];
	else
		unpin = &fs_info->freed_extents[0];

	while (!trans->aborted) {
		mutex_lock(&fs_info->unused_bg_unpin_mutex);
		ret = find_first_extent_bit(unpin, 0, &start, &end,
					    EXTENT_DIRTY, NULL);
		if (ret) {
			mutex_unlock(&fs_info->unused_bg_unpin_mutex);
			break;
		}

		if (btrfs_test_opt(fs_info, DISCARD))
			ret = btrfs_discard_extent(fs_info, start,
						   end + 1 - start, NULL);

		clear_extent_dirty(unpin, start, end);
		unpin_extent_range(fs_info, start, end, true);
		mutex_unlock(&fs_info->unused_bg_unpin_mutex);
		cond_resched();
	}

	/*
	 * Transaction is finished.  We don't need the lock anymore.  We
	 * do need to clean up the block groups in case of a transaction
	 * abort.
	 */
	deleted_bgs = &trans->transaction->deleted_bgs;
	list_for_each_entry_safe(block_group, tmp, deleted_bgs, bg_list) {
		u64 trimmed = 0;

		ret = -EROFS;
		if (!trans->aborted)
			ret = btrfs_discard_extent(fs_info,
						   block_group->key.objectid,
						   block_group->key.offset,
						   &trimmed);

		list_del_init(&block_group->bg_list);
		btrfs_put_block_group_trimming(block_group);
		btrfs_put_block_group(block_group);

		if (ret) {
			const char *errstr = btrfs_decode_error(ret);
			btrfs_warn(fs_info,
				   "Discard failed while removing blockgroup: errno=%d %s\n",
				   ret, errstr);
		}
	}

	return 0;
}
				u64 owner_offset, int refs_to_drop,
				struct btrfs_delayed_extent_op *extent_op)
{
	struct btrfs_key key;
	struct btrfs_path *path;
	struct btrfs_root *extent_root = info->extent_root;
	struct extent_buffer *leaf;
	struct btrfs_extent_item *ei;
	struct btrfs_extent_inline_ref *iref;
	int ret;
	int is_data;
	int extent_slot = 0;
	int found_extent = 0;
	int num_to_del = 1;
	u32 item_size;
	u64 refs;
	u64 bytenr = node->bytenr;
	u64 num_bytes = node->num_bytes;
	int last_ref = 0;
	bool skinny_metadata = btrfs_fs_incompat(info, SKINNY_METADATA);

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->reada = READA_FORWARD;
	path->leave_spinning = 1;

	is_data = owner_objectid >= BTRFS_FIRST_FREE_OBJECTID;
	BUG_ON(!is_data && refs_to_drop != 1);

	if (is_data)
		skinny_metadata = 0;

	ret = lookup_extent_backref(trans, info, path, &iref,
				    bytenr, num_bytes, parent,
				    root_objectid, owner_objectid,
				    owner_offset);
	if (ret == 0) {
		extent_slot = path->slots[0];
		while (extent_slot >= 0) {
			btrfs_item_key_to_cpu(path->nodes[0], &key,
					      extent_slot);
			if (key.objectid != bytenr)
				break;
			if (key.type == BTRFS_EXTENT_ITEM_KEY &&
			    key.offset == num_bytes) {
				found_extent = 1;
				break;
			}
			if (key.type == BTRFS_METADATA_ITEM_KEY &&
			    key.offset == owner_objectid) {
				found_extent = 1;
				break;
			}
			if (path->slots[0] - extent_slot > 5)
				break;
			extent_slot--;
		}
#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
		item_size = btrfs_item_size_nr(path->nodes[0], extent_slot);
		if (found_extent && item_size < sizeof(*ei))
			found_extent = 0;
#endif
		if (!found_extent) {
			BUG_ON(iref);
			ret = remove_extent_backref(trans, info, path, NULL,
						    refs_to_drop,
						    is_data, &last_ref);
			if (ret) {
				btrfs_abort_transaction(trans, ret);
				goto out;
			}
			btrfs_release_path(path);
			path->leave_spinning = 1;

			key.objectid = bytenr;
			key.type = BTRFS_EXTENT_ITEM_KEY;
			key.offset = num_bytes;

			if (!is_data && skinny_metadata) {
				key.type = BTRFS_METADATA_ITEM_KEY;
				key.offset = owner_objectid;
			}

			ret = btrfs_search_slot(trans, extent_root,
						&key, path, -1, 1);
			if (ret > 0 && skinny_metadata && path->slots[0]) {
				/*
				 * Couldn't find our skinny metadata item,
				 * see if we have ye olde extent item.
				 */
				path->slots[0]--;
				btrfs_item_key_to_cpu(path->nodes[0], &key,
						      path->slots[0]);
				if (key.objectid == bytenr &&
				    key.type == BTRFS_EXTENT_ITEM_KEY &&
				    key.offset == num_bytes)
					ret = 0;
			}

			if (ret > 0 && skinny_metadata) {
				skinny_metadata = false;
				key.objectid = bytenr;
				key.type = BTRFS_EXTENT_ITEM_KEY;
				key.offset = num_bytes;
				btrfs_release_path(path);
				ret = btrfs_search_slot(trans, extent_root,
							&key, path, -1, 1);
			}

			if (ret) {
				btrfs_err(info,
					  "umm, got %d back from search, was looking for %llu",
					  ret, bytenr);
				if (ret > 0)
					btrfs_print_leaf(info, path->nodes[0]);
			}
			if (ret < 0) {
				btrfs_abort_transaction(trans, ret);
				goto out;
			}
			extent_slot = path->slots[0];
		}
	} else if (WARN_ON(ret == -ENOENT)) {
		btrfs_print_leaf(info, path->nodes[0]);
		btrfs_err(info,
			"unable to find ref byte nr %llu parent %llu root %llu  owner %llu offset %llu",
			bytenr, parent, root_objectid, owner_objectid,
			owner_offset);
		btrfs_abort_transaction(trans, ret);
		goto out;
	} else {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

	leaf = path->nodes[0];
	item_size = btrfs_item_size_nr(leaf, extent_slot);
#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
	if (item_size < sizeof(*ei)) {
		BUG_ON(found_extent || extent_slot != path->slots[0]);
		ret = convert_extent_item_v0(trans, info, path, owner_objectid,
					     0);
		if (ret < 0) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}

		btrfs_release_path(path);
		path->leave_spinning = 1;

		key.objectid = bytenr;
		key.type = BTRFS_EXTENT_ITEM_KEY;
		key.offset = num_bytes;

		ret = btrfs_search_slot(trans, extent_root, &key, path,
					-1, 1);
		if (ret) {
			btrfs_err(info,
				  "umm, got %d back from search, was looking for %llu",
				ret, bytenr);
			btrfs_print_leaf(info, path->nodes[0]);
		}
		if (ret < 0) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}

		extent_slot = path->slots[0];
		leaf = path->nodes[0];
		item_size = btrfs_item_size_nr(leaf, extent_slot);
	}
#endif
	BUG_ON(item_size < sizeof(*ei));
	ei = btrfs_item_ptr(leaf, extent_slot,
			    struct btrfs_extent_item);
	if (owner_objectid < BTRFS_FIRST_FREE_OBJECTID &&
	    key.type == BTRFS_EXTENT_ITEM_KEY) {
		struct btrfs_tree_block_info *bi;
		BUG_ON(item_size < sizeof(*ei) + sizeof(*bi));
		bi = (struct btrfs_tree_block_info *)(ei + 1);
		WARN_ON(owner_objectid != btrfs_tree_block_level(leaf, bi));
	}

	refs = btrfs_extent_refs(leaf, ei);
	if (refs < refs_to_drop) {
		btrfs_err(info,
			  "trying to drop %d refs but we only have %Lu for bytenr %Lu",
			  refs_to_drop, refs, bytenr);
		ret = -EINVAL;
		btrfs_abort_transaction(trans, ret);
		goto out;
	}
	refs -= refs_to_drop;

	if (refs > 0) {
		if (extent_op)
			__run_delayed_extent_op(extent_op, leaf, ei);
		/*
		 * In the case of inline back ref, reference count will
		 * be updated by remove_extent_backref
		 */
		if (iref) {
			BUG_ON(!found_extent);
		} else {
			btrfs_set_extent_refs(leaf, ei, refs);
			btrfs_mark_buffer_dirty(leaf);
		}
		if (found_extent) {
			ret = remove_extent_backref(trans, info, path,
						    iref, refs_to_drop,
						    is_data, &last_ref);
			if (ret) {
				btrfs_abort_transaction(trans, ret);
				goto out;
			}
		}
		add_pinned_bytes(info, -num_bytes, owner_objectid,
				 root_objectid);
	} else {
		if (found_extent) {
			BUG_ON(is_data && refs_to_drop !=
			       extent_data_ref_count(path, iref));
			if (iref) {
				BUG_ON(path->slots[0] != extent_slot);
			} else {
				BUG_ON(path->slots[0] != extent_slot + 1);
				path->slots[0] = extent_slot;
				num_to_del = 2;
			}
		}

		last_ref = 1;
		ret = btrfs_del_items(trans, extent_root, path, path->slots[0],
				      num_to_del);
		if (ret) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}
		btrfs_release_path(path);

		if (is_data) {
			ret = btrfs_del_csums(trans, info, bytenr, num_bytes);
			if (ret) {
				btrfs_abort_transaction(trans, ret);
				goto out;
			}
		}

		ret = add_to_free_space_tree(trans, info, bytenr, num_bytes);
		if (ret) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}

		ret = update_block_group(trans, info, bytenr, num_bytes, 0);
		if (ret) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}
	}
	btrfs_release_path(path);

out:
	btrfs_free_path(path);
	return ret;
}
		   struct btrfs_free_cluster *cluster,
		   int delalloc)
{
	struct btrfs_block_group_cache *used_bg = NULL;

	spin_lock(&cluster->refill_lock);
	while (1) {
		used_bg = cluster->block_group;
		if (!used_bg)
			return NULL;

		if (used_bg == block_group)
			return used_bg;

		btrfs_get_block_group(used_bg);

		if (!delalloc)
			return used_bg;

		if (down_read_trylock(&used_bg->data_rwsem))
			return used_bg;

		spin_unlock(&cluster->refill_lock);

		/* We should only have one-level nested. */
		down_read_nested(&used_bg->data_rwsem, SINGLE_DEPTH_NESTING);

		spin_lock(&cluster->refill_lock);
		if (used_bg == cluster->block_group)
			return used_bg;

		up_read(&used_bg->data_rwsem);
		btrfs_put_block_group(used_bg);
	}
}
				     struct walk_control *wc,
				     struct btrfs_path *path)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 bytenr;
	u64 generation;
	u64 refs;
	u64 flags;
	u32 nritems;
	struct btrfs_key key;
	struct extent_buffer *eb;
	int ret;
	int slot;
	int nread = 0;

	if (path->slots[wc->level] < wc->reada_slot) {
		wc->reada_count = wc->reada_count * 2 / 3;
		wc->reada_count = max(wc->reada_count, 2);
	} else {
		wc->reada_count = wc->reada_count * 3 / 2;
		wc->reada_count = min_t(int, wc->reada_count,
					BTRFS_NODEPTRS_PER_BLOCK(fs_info));
	}

	eb = path->nodes[wc->level];
	nritems = btrfs_header_nritems(eb);

	for (slot = path->slots[wc->level]; slot < nritems; slot++) {
		if (nread >= wc->reada_count)
			break;

		cond_resched();
		bytenr = btrfs_node_blockptr(eb, slot);
		generation = btrfs_node_ptr_generation(eb, slot);

		if (slot == path->slots[wc->level])
			goto reada;

		if (wc->stage == UPDATE_BACKREF &&
		    generation <= root->root_key.offset)
			continue;

		/* We don't lock the tree block, it's OK to be racy here */
		ret = btrfs_lookup_extent_info(trans, fs_info, bytenr,
					       wc->level - 1, 1, &refs,
					       &flags);
		/* We don't care about errors in readahead. */
		if (ret < 0)
			continue;
		BUG_ON(refs == 0);

		if (wc->stage == DROP_REFERENCE) {
			if (refs == 1)
				goto reada;

			if (wc->level == 1 &&
			    (flags & BTRFS_BLOCK_FLAG_FULL_BACKREF))
				continue;
			if (!wc->update_ref ||
			    generation <= root->root_key.offset)
				continue;
			btrfs_node_key_to_cpu(eb, &key, slot);
			ret = btrfs_comp_cpu_keys(&key,
						  &wc->update_progress);
			if (ret < 0)
				continue;
		} else {
			if (wc->level == 1 &&
			    (flags & BTRFS_BLOCK_FLAG_FULL_BACKREF))
				continue;
		}
reada:
		readahead_tree_block(fs_info, bytenr);
		nread++;
	}
	wc->reada_slot = slot;
}
				   struct btrfs_path *path,
				   struct walk_control *wc)
{
	int level = wc->level;
	int lookup_info = 1;
	int ret;

	while (level >= 0) {
		ret = walk_down_proc(trans, root, path, wc, lookup_info);
		if (ret > 0)
			break;

		if (level == 0)
			break;

		if (path->slots[level] >=
		    btrfs_header_nritems(path->nodes[level]))
			break;

		ret = do_walk_down(trans, root, path, wc, &lookup_info);
		if (ret > 0) {
			path->slots[level]++;
			continue;
		} else if (ret < 0)
			return ret;
		level = wc->level;
	}
	return 0;
}
				 struct btrfs_path *path,
				 struct walk_control *wc, int max_level)
{
	int level = wc->level;
	int ret;

	path->slots[level] = btrfs_header_nritems(path->nodes[level]);
	while (level < max_level && path->nodes[level]) {
		wc->level = level;
		if (path->slots[level] + 1 <
		    btrfs_header_nritems(path->nodes[level])) {
			path->slots[level]++;
			return 0;
		} else {
			ret = walk_up_proc(trans, root, path, wc);
			if (ret > 0)
				return 0;

			if (path->locks[level]) {
				btrfs_tree_unlock_rw(path->nodes[level],
						     path->locks[level]);
				path->locks[level] = 0;
			}
			free_extent_buffer(path->nodes[level]);
			path->nodes[level] = NULL;
			level++;
		}
	}
	return 1;
}
			 struct btrfs_block_rsv *block_rsv, int update_ref,
			 int for_reloc)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_path *path;
	struct btrfs_trans_handle *trans;
	struct btrfs_root *tree_root = fs_info->tree_root;
	struct btrfs_root_item *root_item = &root->root_item;
	struct walk_control *wc;
	struct btrfs_key key;
	int err = 0;
	int ret;
	int level;
	bool root_dropped = false;

	btrfs_debug(fs_info, "Drop subvolume %llu", root->objectid);

	path = btrfs_alloc_path();
	if (!path) {
		err = -ENOMEM;
		goto out;
	}

	wc = kzalloc(sizeof(*wc), GFP_NOFS);
	if (!wc) {
		btrfs_free_path(path);
		err = -ENOMEM;
		goto out;
	}

	trans = btrfs_start_transaction(tree_root, 0);
	if (IS_ERR(trans)) {
		err = PTR_ERR(trans);
		goto out_free;
	}

	if (block_rsv)
		trans->block_rsv = block_rsv;

	if (btrfs_disk_key_objectid(&root_item->drop_progress) == 0) {
		level = btrfs_header_level(root->node);
		path->nodes[level] = btrfs_lock_root_node(root);
		btrfs_set_lock_blocking(path->nodes[level]);
		path->slots[level] = 0;
		path->locks[level] = BTRFS_WRITE_LOCK_BLOCKING;
		memset(&wc->update_progress, 0,
		       sizeof(wc->update_progress));
	} else {
		btrfs_disk_key_to_cpu(&key, &root_item->drop_progress);
		memcpy(&wc->update_progress, &key,
		       sizeof(wc->update_progress));

		level = root_item->drop_level;
		BUG_ON(level == 0);
		path->lowest_level = level;
		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		path->lowest_level = 0;
		if (ret < 0) {
			err = ret;
			goto out_end_trans;
		}
		WARN_ON(ret > 0);

		/*
		 * unlock our path, this is safe because only this
		 * function is allowed to delete this snapshot
		 */
		btrfs_unlock_up_safe(path, 0);

		level = btrfs_header_level(root->node);
		while (1) {
			btrfs_tree_lock(path->nodes[level]);
			btrfs_set_lock_blocking(path->nodes[level]);
			path->locks[level] = BTRFS_WRITE_LOCK_BLOCKING;

			ret = btrfs_lookup_extent_info(trans, fs_info,
						path->nodes[level]->start,
						level, 1, &wc->refs[level],
						&wc->flags[level]);
			if (ret < 0) {
				err = ret;
				goto out_end_trans;
			}
			BUG_ON(wc->refs[level] == 0);

			if (level == root_item->drop_level)
				break;

			btrfs_tree_unlock(path->nodes[level]);
			path->locks[level] = 0;
			WARN_ON(wc->refs[level] != 1);
			level--;
		}
	}

	wc->level = level;
	wc->shared_level = -1;
	wc->stage = DROP_REFERENCE;
	wc->update_ref = update_ref;
	wc->keep_locks = 0;
	wc->for_reloc = for_reloc;
	wc->reada_count = BTRFS_NODEPTRS_PER_BLOCK(fs_info);

	while (1) {

		ret = walk_down_tree(trans, root, path, wc);
		if (ret < 0) {
			err = ret;
			break;
		}

		ret = walk_up_tree(trans, root, path, wc, BTRFS_MAX_LEVEL);
		if (ret < 0) {
			err = ret;
			break;
		}

		if (ret > 0) {
			BUG_ON(wc->stage != DROP_REFERENCE);
			break;
		}

		if (wc->stage == DROP_REFERENCE) {
			level = wc->level;
			btrfs_node_key(path->nodes[level],
				       &root_item->drop_progress,
				       path->slots[level]);
			root_item->drop_level = level;
		}

		BUG_ON(wc->level == 0);
		if (btrfs_should_end_transaction(trans) ||
		    (!for_reloc && btrfs_need_cleaner_sleep(fs_info))) {
			ret = btrfs_update_root(trans, tree_root,
						&root->root_key,
						root_item);
			if (ret) {
				btrfs_abort_transaction(trans, ret);
				err = ret;
				goto out_end_trans;
			}

			btrfs_end_transaction_throttle(trans);
			if (!for_reloc && btrfs_need_cleaner_sleep(fs_info)) {
				btrfs_debug(fs_info,
					    "drop snapshot early exit");
				err = -EAGAIN;
				goto out_free;
			}

			trans = btrfs_start_transaction(tree_root, 0);
			if (IS_ERR(trans)) {
				err = PTR_ERR(trans);
				goto out_free;
			}
			if (block_rsv)
				trans->block_rsv = block_rsv;
		}
	}
	btrfs_release_path(path);
	if (err)
		goto out_end_trans;

	ret = btrfs_del_root(trans, tree_root, &root->root_key);
	if (ret) {
		btrfs_abort_transaction(trans, ret);
		goto out_end_trans;
	}

	if (root->root_key.objectid != BTRFS_TREE_RELOC_OBJECTID) {
		ret = btrfs_find_root(tree_root, &root->root_key, path,
				      NULL, NULL);
		if (ret < 0) {
			btrfs_abort_transaction(trans, ret);
			err = ret;
			goto out_end_trans;
		} else if (ret > 0) {
			/* if we fail to delete the orphan item this time
			 * around, it'll get picked up the next time.
			 *
			 * The most common failure here is just -ENOENT.
			 */
			btrfs_del_orphan_item(trans, tree_root,
					      root->root_key.objectid);
		}
	}

	if (test_bit(BTRFS_ROOT_IN_RADIX, &root->state)) {
		btrfs_add_dropped_root(trans, root);
	} else {
		free_extent_buffer(root->node);
		free_extent_buffer(root->commit_root);
		btrfs_put_fs_root(root);
	}
	root_dropped = true;
out_end_trans:
	btrfs_end_transaction_throttle(trans);
out_free:
	kfree(wc);
	btrfs_free_path(path);
out:
	/*
	 * So if we need to stop dropping the snapshot for whatever reason we
	 * need to make sure to add it back to the dead root list so that we
	 * keep trying to do the work later.  This also cleans up roots if we
	 * don't have it in the radix (like when we recover after a power fail
	 * or unmount) so we don't leak memory.
	 */
	if (!for_reloc && root_dropped == false)
		btrfs_add_dead_root(root);
	if (err && err != -EAGAIN)
		btrfs_handle_fs_error(fs_info, err, NULL);
	return err;
}
			struct extent_buffer *node,
			struct extent_buffer *parent)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_path *path;
	struct walk_control *wc;
	int level;
	int parent_level;
	int ret = 0;
	int wret;

	BUG_ON(root->root_key.objectid != BTRFS_TREE_RELOC_OBJECTID);

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	wc = kzalloc(sizeof(*wc), GFP_NOFS);
	if (!wc) {
		btrfs_free_path(path);
		return -ENOMEM;
	}

	btrfs_assert_tree_locked(parent);
	parent_level = btrfs_header_level(parent);
	extent_buffer_get(parent);
	path->nodes[parent_level] = parent;
	path->slots[parent_level] = btrfs_header_nritems(parent);

	btrfs_assert_tree_locked(node);
	level = btrfs_header_level(node);
	path->nodes[level] = node;
	path->slots[level] = 0;
	path->locks[level] = BTRFS_WRITE_LOCK_BLOCKING;

	wc->refs[parent_level] = 1;
	wc->flags[parent_level] = BTRFS_BLOCK_FLAG_FULL_BACKREF;
	wc->level = level;
	wc->shared_level = -1;
	wc->stage = DROP_REFERENCE;
	wc->update_ref = 0;
	wc->keep_locks = 1;
	wc->for_reloc = 1;
	wc->reada_count = BTRFS_NODEPTRS_PER_BLOCK(fs_info);

	while (1) {
		wret = walk_down_tree(trans, root, path, wc);
		if (wret < 0) {
			ret = wret;
			break;
		}

		wret = walk_up_tree(trans, root, path, wc, parent_level);
		if (wret < 0)
			ret = wret;
		if (wret != 0)
			break;
	}

	kfree(wc);
	btrfs_free_path(path);
	return ret;
}
				  struct btrfs_path *path,
				  struct btrfs_key *key)
{
	struct btrfs_root *root = fs_info->extent_root;
	int ret = 0;
	struct btrfs_key found_key;
	struct extent_buffer *leaf;
	int slot;

	ret = btrfs_search_slot(NULL, root, key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		slot = path->slots[0];
		leaf = path->nodes[0];
		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret == 0)
				continue;
			if (ret < 0)
				goto out;
			break;
		}
		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		if (found_key.objectid >= key->objectid &&
		    found_key.type == BTRFS_BLOCK_GROUP_ITEM_KEY) {
			struct extent_map_tree *em_tree;
			struct extent_map *em;

			em_tree = &root->fs_info->mapping_tree.map_tree;
			read_lock(&em_tree->lock);
			em = lookup_extent_mapping(em_tree, found_key.objectid,
						   found_key.offset);
			read_unlock(&em_tree->lock);
			if (!em) {
				btrfs_err(fs_info,
			"logical %llu len %llu found bg but no related chunk",
					  found_key.objectid, found_key.offset);
				ret = -ENOENT;
			} else {
				ret = 0;
			}
			free_extent_map(em);
			goto out;
		}
		path->slots[0]++;
	}
out:
	return ret;
}

void btrfs_put_block_group_cache(struct btrfs_fs_info *info)
{
	struct btrfs_block_group_cache *block_group;
	u64 last = 0;

	while (1) {
		struct inode *inode;

		block_group = btrfs_lookup_first_block_group(info, last);
		while (block_group) {
			spin_lock(&block_group->lock);
			if (block_group->iref)
				break;
			spin_unlock(&block_group->lock);
			block_group = next_block_group(info, block_group);
		}
		if (!block_group) {
			if (last == 0)
				break;
			last = 0;
			continue;
		}

		inode = block_group->inode;
		block_group->iref = 0;
		block_group->inode = NULL;
		spin_unlock(&block_group->lock);
		ASSERT(block_group->io_ctl.inode == NULL);
		iput(inode);
		last = block_group->key.objectid + block_group->key.offset;
		btrfs_put_block_group(block_group);
	}
}
 */
int btrfs_free_block_groups(struct btrfs_fs_info *info)
{
	struct btrfs_block_group_cache *block_group;
	struct btrfs_space_info *space_info;
	struct btrfs_caching_control *caching_ctl;
	struct rb_node *n;

	down_write(&info->commit_root_sem);
	while (!list_empty(&info->caching_block_groups)) {
		caching_ctl = list_entry(info->caching_block_groups.next,
					 struct btrfs_caching_control, list);
		list_del(&caching_ctl->list);
		put_caching_control(caching_ctl);
	}
	up_write(&info->commit_root_sem);

	spin_lock(&info->unused_bgs_lock);
	while (!list_empty(&info->unused_bgs)) {
		block_group = list_first_entry(&info->unused_bgs,
					       struct btrfs_block_group_cache,
					       bg_list);
		list_del_init(&block_group->bg_list);
		btrfs_put_block_group(block_group);
	}
	spin_unlock(&info->unused_bgs_lock);

	spin_lock(&info->block_group_cache_lock);
	while ((n = rb_last(&info->block_group_cache_tree)) != NULL) {
		block_group = rb_entry(n, struct btrfs_block_group_cache,
				       cache_node);
		rb_erase(&block_group->cache_node,
			 &info->block_group_cache_tree);
		RB_CLEAR_NODE(&block_group->cache_node);
		spin_unlock(&info->block_group_cache_lock);

		down_write(&block_group->space_info->groups_sem);
		list_del(&block_group->list);
		up_write(&block_group->space_info->groups_sem);

		/*
		 * We haven't cached this block group, which means we could
		 * possibly have excluded extents on this block group.
		 */
		if (block_group->cached == BTRFS_CACHE_NO ||
		    block_group->cached == BTRFS_CACHE_ERROR)
			free_excluded_extents(info, block_group);

		btrfs_remove_free_space_cache(block_group);
		ASSERT(block_group->cached != BTRFS_CACHE_STARTED);
		ASSERT(list_empty(&block_group->dirty_list));
		ASSERT(list_empty(&block_group->io_list));
		ASSERT(list_empty(&block_group->bg_list));
		ASSERT(atomic_read(&block_group->count) == 1);
		btrfs_put_block_group(block_group);

		spin_lock(&info->block_group_cache_lock);
	}
	spin_unlock(&info->block_group_cache_lock);

	/* now that all the block groups are freed, go through and
	 * free all the space_info structs.  This is only called during
	 * the final stages of unmount, and so we know nobody is
	 * using them.  We call synchronize_rcu() once before we start,
	 * just to be on the safe side.
	 */
	synchronize_rcu();

	release_global_block_rsv(info);

	while (!list_empty(&info->space_info)) {
		int i;

		space_info = list_entry(info->space_info.next,
					struct btrfs_space_info,
					list);

		/*
		 * Do not hide this behind enospc_debug, this is actually
		 * important and indicates a real bug if this happens.
		 */
		if (WARN_ON(space_info->bytes_pinned > 0 ||
			    space_info->bytes_reserved > 0 ||
			    space_info->bytes_may_use > 0))
			dump_space_info(info, space_info, 0, 0);
		list_del(&space_info->list);
		for (i = 0; i < BTRFS_NR_RAID_TYPES; i++) {
			struct kobject *kobj;
			kobj = space_info->block_group_kobjs[i];
			space_info->block_group_kobjs[i] = NULL;
			if (kobj) {
				kobject_del(kobj);
				kobject_put(kobj);
			}
		}
		kobject_del(&space_info->kobj);
		kobject_put(&space_info->kobj);
	}
	return 0;
}

int btrfs_read_block_groups(struct btrfs_fs_info *info)
{
	struct btrfs_path *path;
	int ret;
	struct btrfs_block_group_cache *cache;
	struct btrfs_space_info *space_info;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct extent_buffer *leaf;
	int need_clear = 0;
	u64 cache_gen;
	u64 feature;
	int mixed;

	feature = btrfs_super_incompat_flags(info->super_copy);
	mixed = !!(feature & BTRFS_FEATURE_INCOMPAT_MIXED_GROUPS);

	key.objectid = 0;
	key.offset = 0;
	key.type = BTRFS_BLOCK_GROUP_ITEM_KEY;
	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->reada = READA_FORWARD;

	cache_gen = btrfs_super_cache_generation(info->super_copy);
	if (btrfs_test_opt(info, SPACE_CACHE) &&
	    btrfs_super_generation(info->super_copy) != cache_gen)
		need_clear = 1;
	if (btrfs_test_opt(info, CLEAR_CACHE))
		need_clear = 1;

	while (1) {
		ret = find_first_block_group(info, path, &key);
		if (ret > 0)
			break;
		if (ret != 0)
			goto error;

		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);

		cache = btrfs_create_block_group_cache(info, found_key.objectid,
						       found_key.offset);
		if (!cache) {
			ret = -ENOMEM;
			goto error;
		}

		if (need_clear) {
			/*
			 * When we mount with old space cache, we need to
			 * set BTRFS_DC_CLEAR and set dirty flag.
			 *
			 * a) Setting 'BTRFS_DC_CLEAR' makes sure that we
			 *    truncate the old free space cache inode and
			 *    setup a new one.
			 * b) Setting 'dirty flag' makes sure that we flush
			 *    the new space cache info onto disk.
			 */
			if (btrfs_test_opt(info, SPACE_CACHE))
				cache->disk_cache_state = BTRFS_DC_CLEAR;
		}

		read_extent_buffer(leaf, &cache->item,
				   btrfs_item_ptr_offset(leaf, path->slots[0]),
				   sizeof(cache->item));
		cache->flags = btrfs_block_group_flags(&cache->item);
		if (!mixed &&
		    ((cache->flags & BTRFS_BLOCK_GROUP_METADATA) &&
		    (cache->flags & BTRFS_BLOCK_GROUP_DATA))) {
			btrfs_err(info,
"bg %llu is a mixed block group but filesystem hasn't enabled mixed block groups",
				  cache->key.objectid);
			ret = -EINVAL;
			goto error;
		}

		key.objectid = found_key.objectid + found_key.offset;
		btrfs_release_path(path);

		/*
		 * We need to exclude the super stripes now so that the space
		 * info has super bytes accounted for, otherwise we'll think
		 * we have more space than we actually do.
		 */
		ret = exclude_super_stripes(info, cache);
		if (ret) {
			/*
			 * We may have excluded something, so call this just in
			 * case.
			 */
			free_excluded_extents(info, cache);
			btrfs_put_block_group(cache);
			goto error;
		}

		/*
		 * check for two cases, either we are full, and therefore
		 * don't need to bother with the caching work since we won't
		 * find any space, or we are empty, and we can just add all
		 * the space in and be done with it.  This saves us _alot_ of
		 * time, particularly in the full case.
		 */
		if (found_key.offset == btrfs_block_group_used(&cache->item)) {
			cache->last_byte_to_unpin = (u64)-1;
			cache->cached = BTRFS_CACHE_FINISHED;
			free_excluded_extents(info, cache);
		} else if (btrfs_block_group_used(&cache->item) == 0) {
			cache->last_byte_to_unpin = (u64)-1;
			cache->cached = BTRFS_CACHE_FINISHED;
			add_new_free_space(cache, info,
					   found_key.objectid,
					   found_key.objectid +
					   found_key.offset);
			free_excluded_extents(info, cache);
		}

		ret = btrfs_add_block_group_cache(info, cache);
		if (ret) {
			btrfs_remove_free_space_cache(cache);
			btrfs_put_block_group(cache);
			goto error;
		}

		trace_btrfs_add_block_group(info, cache, 0);
		ret = update_space_info(info, cache->flags, found_key.offset,
					btrfs_block_group_used(&cache->item),
					cache->bytes_super, &space_info);
		if (ret) {
			btrfs_remove_free_space_cache(cache);
			spin_lock(&info->block_group_cache_lock);
			rb_erase(&cache->cache_node,
				 &info->block_group_cache_tree);
			RB_CLEAR_NODE(&cache->cache_node);
			spin_unlock(&info->block_group_cache_lock);
			btrfs_put_block_group(cache);
			goto error;
		}

		cache->space_info = space_info;

		__link_block_group(space_info, cache);

		set_avail_alloc_bits(info, cache->flags);
		if (btrfs_chunk_readonly(info, cache->key.objectid)) {
			inc_block_group_ro(cache, 1);
		} else if (btrfs_block_group_used(&cache->item) == 0) {
			spin_lock(&info->unused_bgs_lock);
			/* Should always be true but just in case. */
			if (list_empty(&cache->bg_list)) {
				btrfs_get_block_group(cache);
				list_add_tail(&cache->bg_list,
					      &info->unused_bgs);
			}
			spin_unlock(&info->unused_bgs_lock);
		}
	}

	list_for_each_entry_rcu(space_info, &info->space_info, list) {
		if (!(get_alloc_profile(info, space_info->flags) &
		      (BTRFS_BLOCK_GROUP_RAID10 |
		       BTRFS_BLOCK_GROUP_RAID1 |
		       BTRFS_BLOCK_GROUP_RAID5 |
		       BTRFS_BLOCK_GROUP_RAID6 |
		       BTRFS_BLOCK_GROUP_DUP)))
			continue;
		/*
		 * avoid allocating from un-mirrored block group if there are
		 * mirrored block groups.
		 */
		list_for_each_entry(cache,
				&space_info->block_groups[BTRFS_RAID_RAID0],
				list)
			inc_block_group_ro(cache, 1);
		list_for_each_entry(cache,
				&space_info->block_groups[BTRFS_RAID_SINGLE],
				list)
			inc_block_group_ro(cache, 1);
	}

	init_global_block_rsv(info);
	ret = 0;
error:
	btrfs_free_path(path);
	return ret;
}
 */
void btrfs_delete_unused_bgs(struct btrfs_fs_info *fs_info)
{
	struct btrfs_block_group_cache *block_group;
	struct btrfs_space_info *space_info;
	struct btrfs_trans_handle *trans;
	int ret = 0;

	if (!test_bit(BTRFS_FS_OPEN, &fs_info->flags))
		return;

	spin_lock(&fs_info->unused_bgs_lock);
	while (!list_empty(&fs_info->unused_bgs)) {
		u64 start, end;
		int trimming;

		block_group = list_first_entry(&fs_info->unused_bgs,
					       struct btrfs_block_group_cache,
					       bg_list);
		list_del_init(&block_group->bg_list);

		space_info = block_group->space_info;

		if (ret || btrfs_mixed_space_info(space_info)) {
			btrfs_put_block_group(block_group);
			continue;
		}
		spin_unlock(&fs_info->unused_bgs_lock);

		mutex_lock(&fs_info->delete_unused_bgs_mutex);

		/* Don't want to race with allocators so take the groups_sem */
		down_write(&space_info->groups_sem);
		spin_lock(&block_group->lock);
		if (block_group->reserved ||
		    btrfs_block_group_used(&block_group->item) ||
		    block_group->ro ||
		    list_is_singular(&block_group->list)) {
			/*
			 * We want to bail if we made new allocations or have
			 * outstanding allocations in this block group.  We do
			 * the ro check in case balance is currently acting on
			 * this block group.
			 */
			spin_unlock(&block_group->lock);
			up_write(&space_info->groups_sem);
			goto next;
		}
		spin_unlock(&block_group->lock);

		/* We don't want to force the issue, only flip if it's ok. */
		ret = inc_block_group_ro(block_group, 0);
		up_write(&space_info->groups_sem);
		if (ret < 0) {
			ret = 0;
			goto next;
		}

		/*
		 * Want to do this before we do anything else so we can recover
		 * properly if we fail to join the transaction.
		 */
		trans = btrfs_start_trans_remove_block_group(fs_info,
						     block_group->key.objectid);
		if (IS_ERR(trans)) {
			btrfs_dec_block_group_ro(block_group);
			ret = PTR_ERR(trans);
			goto next;
		}

		/*
		 * We could have pending pinned extents for this block group,
		 * just delete them, we don't care about them anymore.
		 */
		start = block_group->key.objectid;
		end = start + block_group->key.offset - 1;
		/*
		 * Hold the unused_bg_unpin_mutex lock to avoid racing with
		 * btrfs_finish_extent_commit(). If we are at transaction N,
		 * another task might be running finish_extent_commit() for the
		 * previous transaction N - 1, and have seen a range belonging
		 * to the block group in freed_extents[] before we were able to
		 * clear the whole block group range from freed_extents[]. This
		 * means that task can lookup for the block group after we
		 * unpinned it from freed_extents[] and removed it, leading to
		 * a BUG_ON() at btrfs_unpin_extent_range().
		 */
		mutex_lock(&fs_info->unused_bg_unpin_mutex);
		ret = clear_extent_bits(&fs_info->freed_extents[0], start, end,
				  EXTENT_DIRTY);
		if (ret) {
			mutex_unlock(&fs_info->unused_bg_unpin_mutex);
			btrfs_dec_block_group_ro(block_group);
			goto end_trans;
		}
		ret = clear_extent_bits(&fs_info->freed_extents[1], start, end,
				  EXTENT_DIRTY);
		if (ret) {
			mutex_unlock(&fs_info->unused_bg_unpin_mutex);
			btrfs_dec_block_group_ro(block_group);
			goto end_trans;
		}
		mutex_unlock(&fs_info->unused_bg_unpin_mutex);

		/* Reset pinned so btrfs_put_block_group doesn't complain */
		spin_lock(&space_info->lock);
		spin_lock(&block_group->lock);

		space_info->bytes_pinned -= block_group->pinned;
		space_info->bytes_readonly += block_group->pinned;
		percpu_counter_add(&space_info->total_bytes_pinned,
				   -block_group->pinned);
		block_group->pinned = 0;

		spin_unlock(&block_group->lock);
		spin_unlock(&space_info->lock);

		/* DISCARD can flip during remount */
		trimming = btrfs_test_opt(fs_info, DISCARD);

		/* Implicit trim during transaction commit. */
		if (trimming)
			btrfs_get_block_group_trimming(block_group);

		/*
		 * Btrfs_remove_chunk will abort the transaction if things go
		 * horribly wrong.
		 */
		ret = btrfs_remove_chunk(trans, fs_info,
					 block_group->key.objectid);

		if (ret) {
			if (trimming)
				btrfs_put_block_group_trimming(block_group);
			goto end_trans;
		}

		/*
		 * If we're not mounted with -odiscard, we can just forget
		 * about this block group. Otherwise we'll need to wait
		 * until transaction commit to do the actual discard.
		 */
		if (trimming) {
			spin_lock(&fs_info->unused_bgs_lock);
			/*
			 * A concurrent scrub might have added us to the list
			 * fs_info->unused_bgs, so use a list_move operation
			 * to add the block group to the deleted_bgs list.
			 */
			list_move(&block_group->bg_list,
				  &trans->transaction->deleted_bgs);
			spin_unlock(&fs_info->unused_bgs_lock);
			btrfs_get_block_group(block_group);
		}
end_trans:
		btrfs_end_transaction(trans);
next:
		mutex_unlock(&fs_info->delete_unused_bgs_mutex);
		btrfs_put_block_group(block_group);
		spin_lock(&fs_info->unused_bgs_lock);
	}
	spin_unlock(&fs_info->unused_bgs_lock);
}
static int btrfs_trim_free_extents(struct btrfs_device *device,
				   u64 minlen, u64 *trimmed)
{
	u64 start = 0, len = 0;
	int ret;

	*trimmed = 0;

	/* Not writeable = nothing to do. */
	if (!device->writeable)
		return 0;

	/* No free space = nothing to do. */
	if (device->total_bytes <= device->bytes_used)
		return 0;

	ret = 0;

	while (1) {
		struct btrfs_fs_info *fs_info = device->fs_info;
		struct btrfs_transaction *trans;
		u64 bytes;

		ret = mutex_lock_interruptible(&fs_info->chunk_mutex);
		if (ret)
			return ret;

		down_read(&fs_info->commit_root_sem);

		spin_lock(&fs_info->trans_lock);
		trans = fs_info->running_transaction;
		if (trans)
			refcount_inc(&trans->use_count);
		spin_unlock(&fs_info->trans_lock);

		ret = find_free_dev_extent_start(trans, device, minlen, start,
						 &start, &len);
		if (trans)
			btrfs_put_transaction(trans);

		if (ret) {
			up_read(&fs_info->commit_root_sem);
			mutex_unlock(&fs_info->chunk_mutex);
			if (ret == -ENOSPC)
				ret = 0;
			break;
		}

		ret = btrfs_issue_discard(device->bdev, start, len, &bytes);
		up_read(&fs_info->commit_root_sem);
		mutex_unlock(&fs_info->chunk_mutex);

		if (ret)
			break;

		start += len;
		*trimmed += bytes;

		if (fatal_signal_pending(current)) {
			ret = -ERESTARTSYS;
			break;
		}

		cond_resched();
	}

	return ret;
}

int btrfs_trim_fs(struct btrfs_fs_info *fs_info, struct fstrim_range *range)
{
	struct btrfs_block_group_cache *cache = NULL;
	struct btrfs_device *device;
	struct list_head *devices;
	u64 group_trimmed;
	u64 start;
	u64 end;
	u64 trimmed = 0;
	u64 total_bytes = btrfs_super_total_bytes(fs_info->super_copy);
	int ret = 0;

	/*
	 * try to trim all FS space, our block group may start from non-zero.
	 */
	if (range->len == total_bytes)
		cache = btrfs_lookup_first_block_group(fs_info, range->start);
	else
		cache = btrfs_lookup_block_group(fs_info, range->start);

	while (cache) {
		if (cache->key.objectid >= (range->start + range->len)) {
			btrfs_put_block_group(cache);
			break;
		}

		start = max(range->start, cache->key.objectid);
		end = min(range->start + range->len,
				cache->key.objectid + cache->key.offset);

		if (end - start >= range->minlen) {
			if (!block_group_cache_done(cache)) {
				ret = cache_block_group(cache, 0);
				if (ret) {
					btrfs_put_block_group(cache);
					break;
				}
				ret = wait_block_group_cache_done(cache);
				if (ret) {
					btrfs_put_block_group(cache);
					break;
				}
			}
			ret = btrfs_trim_block_group(cache,
						     &group_trimmed,
						     start,
						     end,
						     range->minlen);

			trimmed += group_trimmed;
			if (ret) {
				btrfs_put_block_group(cache);
				break;
			}
		}

		cache = next_block_group(fs_info, cache);
	}

	mutex_lock(&fs_info->fs_devices->device_list_mutex);
	devices = &fs_info->fs_devices->alloc_list;
	list_for_each_entry(device, devices, dev_alloc_list) {
		ret = btrfs_trim_free_extents(device, range->minlen,
					      &group_trimmed);
		if (ret)
			break;

		trimmed += group_trimmed;
	}
	mutex_unlock(&fs_info->fs_devices->device_list_mutex);

	range->len = trimmed;
	return ret;
}

void btrfs_wait_for_snapshot_creation(struct btrfs_root *root)
{
	while (true) {
		int ret;

		ret = btrfs_start_write_no_snapshoting(root);
		if (ret)
			break;
		wait_on_atomic_t(&root->will_be_snapshoted,
				 wait_snapshoting_atomic_t,
				 TASK_UNINTERRUPTIBLE);
	}
}
