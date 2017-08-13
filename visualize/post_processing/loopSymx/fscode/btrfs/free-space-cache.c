
static void io_ctl_drop_pages(struct btrfs_io_ctl *io_ctl)
{
	int i;

	io_ctl_unmap_page(io_ctl);

	for (i = 0; i < io_ctl->num_pages; i++) {
		if (io_ctl->pages[i]) {
			ClearPageChecked(io_ctl->pages[i]);
			unlock_page(io_ctl->pages[i]);
			put_page(io_ctl->pages[i]);
		}
	}
}
static int io_ctl_prepare_pages(struct btrfs_io_ctl *io_ctl, struct inode *inode,
				int uptodate)
{
	struct page *page;
	gfp_t mask = btrfs_alloc_write_mask(inode->i_mapping);
	int i;

	for (i = 0; i < io_ctl->num_pages; i++) {
		page = find_or_create_page(inode->i_mapping, i, mask);
		if (!page) {
			io_ctl_drop_pages(io_ctl);
			return -ENOMEM;
		}
		io_ctl->pages[i] = page;
		if (uptodate && !PageUptodate(page)) {
			btrfs_readpage(NULL, page);
			lock_page(page);
			if (!PageUptodate(page)) {
				btrfs_err(BTRFS_I(inode)->root->fs_info,
					   "error reading free space cache");
				io_ctl_drop_pages(io_ctl);
				return -EIO;
			}
		}
	}

	for (i = 0; i < io_ctl->num_pages; i++) {
		clear_page_dirty_for_io(io_ctl->pages[i]);
		set_page_extent_mapped(io_ctl->pages[i]);
	}

	return 0;
}

static void io_ctl_zero_remaining_pages(struct btrfs_io_ctl *io_ctl)
{
	/*
	 * If we're not on the boundary we know we've modified the page and we
	 * need to crc the page.
	 */
	if (io_ctl->cur != io_ctl->orig)
		io_ctl_set_crc(io_ctl, io_ctl->index - 1);
	else
		io_ctl_unmap_page(io_ctl);

	while (io_ctl->index < io_ctl->num_pages) {
		io_ctl_map_page(io_ctl, 1);
		io_ctl_set_crc(io_ctl, io_ctl->index - 1);
	}
}
 */
static void merge_space_tree(struct btrfs_free_space_ctl *ctl)
{
	struct btrfs_free_space *e, *prev = NULL;
	struct rb_node *n;

again:
	spin_lock(&ctl->tree_lock);
	for (n = rb_first(&ctl->free_space_offset); n; n = rb_next(n)) {
		e = rb_entry(n, struct btrfs_free_space, offset_index);
		if (!prev)
			goto next;
		if (e->bitmap || prev->bitmap)
			goto next;
		if (prev->offset + prev->bytes == e->offset) {
			unlink_free_space(ctl, prev);
			unlink_free_space(ctl, e);
			prev->bytes += e->bytes;
			kmem_cache_free(btrfs_free_space_cachep, e);
			link_free_space(ctl, prev);
			prev = NULL;
			spin_unlock(&ctl->tree_lock);
			goto again;
		}
next:
		prev = e;
	}
	spin_unlock(&ctl->tree_lock);
}
				   struct btrfs_free_space_ctl *ctl,
				   struct btrfs_path *path, u64 offset)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_free_space_header *header;
	struct extent_buffer *leaf;
	struct btrfs_io_ctl io_ctl;
	struct btrfs_key key;
	struct btrfs_free_space *e, *n;
	LIST_HEAD(bitmaps);
	u64 num_entries;
	u64 num_bitmaps;
	u64 generation;
	u8 type;
	int ret = 0;

	/* Nothing in the space cache, goodbye */
	if (!i_size_read(inode))
		return 0;

	key.objectid = BTRFS_FREE_SPACE_OBJECTID;
	key.offset = offset;
	key.type = 0;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		return 0;
	else if (ret > 0) {
		btrfs_release_path(path);
		return 0;
	}

	ret = -1;

	leaf = path->nodes[0];
	header = btrfs_item_ptr(leaf, path->slots[0],
				struct btrfs_free_space_header);
	num_entries = btrfs_free_space_entries(leaf, header);
	num_bitmaps = btrfs_free_space_bitmaps(leaf, header);
	generation = btrfs_free_space_generation(leaf, header);
	btrfs_release_path(path);

	if (!BTRFS_I(inode)->generation) {
		btrfs_info(fs_info,
			   "The free space cache file (%llu) is invalid. skip it\n",
			   offset);
		return 0;
	}

	if (BTRFS_I(inode)->generation != generation) {
		btrfs_err(fs_info,
			  "free space inode generation (%llu) did not match free space cache generation (%llu)",
			  BTRFS_I(inode)->generation, generation);
		return 0;
	}

	if (!num_entries)
		return 0;

	ret = io_ctl_init(&io_ctl, inode, 0);
	if (ret)
		return ret;

	readahead_cache(inode);

	ret = io_ctl_prepare_pages(&io_ctl, inode, 1);
	if (ret)
		goto out;

	ret = io_ctl_check_crc(&io_ctl, 0);
	if (ret)
		goto free_cache;

	ret = io_ctl_check_generation(&io_ctl, generation);
	if (ret)
		goto free_cache;

	while (num_entries) {
		e = kmem_cache_zalloc(btrfs_free_space_cachep,
				      GFP_NOFS);
		if (!e)
			goto free_cache;

		ret = io_ctl_read_entry(&io_ctl, e, &type);
		if (ret) {
			kmem_cache_free(btrfs_free_space_cachep, e);
			goto free_cache;
		}

		if (!e->bytes) {
			kmem_cache_free(btrfs_free_space_cachep, e);
			goto free_cache;
		}

		if (type == BTRFS_FREE_SPACE_EXTENT) {
			spin_lock(&ctl->tree_lock);
			ret = link_free_space(ctl, e);
			spin_unlock(&ctl->tree_lock);
			if (ret) {
				btrfs_err(fs_info,
					"Duplicate entries in free space cache, dumping");
				kmem_cache_free(btrfs_free_space_cachep, e);
				goto free_cache;
			}
		} else {
			ASSERT(num_bitmaps);
			num_bitmaps--;
			e->bitmap = kzalloc(PAGE_SIZE, GFP_NOFS);
			if (!e->bitmap) {
				kmem_cache_free(
					btrfs_free_space_cachep, e);
				goto free_cache;
			}
			spin_lock(&ctl->tree_lock);
			ret = link_free_space(ctl, e);
			ctl->total_bitmaps++;
			ctl->op->recalc_thresholds(ctl);
			spin_unlock(&ctl->tree_lock);
			if (ret) {
				btrfs_err(fs_info,
					"Duplicate entries in free space cache, dumping");
				kmem_cache_free(btrfs_free_space_cachep, e);
				goto free_cache;
			}
			list_add_tail(&e->list, &bitmaps);
		}

		num_entries--;
	}

	io_ctl_unmap_page(&io_ctl);

	/*
	 * We add the bitmaps at the end of the entries in order that
	 * the bitmap entries are added to the cache.
	 */
	list_for_each_entry_safe(e, n, &bitmaps, list) {
		list_del_init(&e->list);
		ret = io_ctl_read_bitmap(&io_ctl, e);
		if (ret)
			goto free_cache;
	}

	io_ctl_drop_pages(&io_ctl);
	merge_space_tree(ctl);
	ret = 1;
out:
	io_ctl_free(&io_ctl);
	return ret;
free_cache:
	io_ctl_drop_pages(&io_ctl);
	__btrfs_remove_free_space_cache(ctl);
	goto out;
}
			      int *entries, int *bitmaps,
			      struct list_head *bitmap_list)
{
	int ret;
	struct btrfs_free_cluster *cluster = NULL;
	struct btrfs_free_cluster *cluster_locked = NULL;
	struct rb_node *node = rb_first(&ctl->free_space_offset);
	struct btrfs_trim_range *trim_entry;

	/* Get the cluster for this block_group if it exists */
	if (block_group && !list_empty(&block_group->cluster_list)) {
		cluster = list_entry(block_group->cluster_list.next,
				     struct btrfs_free_cluster,
				     block_group_list);
	}

	if (!node && cluster) {
		cluster_locked = cluster;
		spin_lock(&cluster_locked->lock);
		node = rb_first(&cluster->root);
		cluster = NULL;
	}

	/* Write out the extent entries */
	while (node) {
		struct btrfs_free_space *e;

		e = rb_entry(node, struct btrfs_free_space, offset_index);
		*entries += 1;

		ret = io_ctl_add_entry(io_ctl, e->offset, e->bytes,
				       e->bitmap);
		if (ret)
			goto fail;

		if (e->bitmap) {
			list_add_tail(&e->list, bitmap_list);
			*bitmaps += 1;
		}
		node = rb_next(node);
		if (!node && cluster) {
			node = rb_first(&cluster->root);
			cluster_locked = cluster;
			spin_lock(&cluster_locked->lock);
			cluster = NULL;
		}
	}
	if (cluster_locked) {
		spin_unlock(&cluster_locked->lock);
		cluster_locked = NULL;
	}

	/*
	 * Make sure we don't miss any range that was removed from our rbtree
	 * because trimming is running. Otherwise after a umount+mount (or crash
	 * after committing the transaction) we would leak free space and get
	 * an inconsistent free space cache report from fsck.
	 */
	list_for_each_entry(trim_entry, &ctl->trimming_ranges, list) {
		ret = io_ctl_add_entry(io_ctl, trim_entry->start,
				       trim_entry->bytes, NULL);
		if (ret)
			goto fail;
		*entries += 1;
	}

	return 0;
fail:
	if (cluster_locked)
		spin_unlock(&cluster_locked->lock);
	return -ENOSPC;
}
			    struct btrfs_io_ctl *io_ctl,
			    int *entries)
{
	u64 start, extent_start, extent_end, len;
	struct extent_io_tree *unpin = NULL;
	int ret;

	if (!block_group)
		return 0;

	/*
	 * We want to add any pinned extents to our free space cache
	 * so we don't leak the space
	 *
	 * We shouldn't have switched the pinned extents yet so this is the
	 * right one
	 */
	unpin = fs_info->pinned_extents;

	start = block_group->key.objectid;

	while (start < block_group->key.objectid + block_group->key.offset) {
		ret = find_first_extent_bit(unpin, start,
					    &extent_start, &extent_end,
					    EXTENT_DIRTY, NULL);
		if (ret)
			return 0;

		/* This pinned extent is out of our range */
		if (extent_start >= block_group->key.objectid +
		    block_group->key.offset)
			return 0;

		extent_start = max(extent_start, start);
		extent_end = min(block_group->key.objectid +
				 block_group->key.offset, extent_end + 1);
		len = extent_end - extent_start;

		*entries += 1;
		ret = io_ctl_add_entry(io_ctl, extent_start, len, NULL);
		if (ret)
			return -ENOSPC;

		start = extent_end;
	}

	return 0;
}
static int tree_insert_offset(struct rb_root *root, u64 offset,
			      struct rb_node *node, int bitmap)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent = NULL;
	struct btrfs_free_space *info;

	while (*p) {
		parent = *p;
		info = rb_entry(parent, struct btrfs_free_space, offset_index);

		if (offset < info->offset) {
			p = &(*p)->rb_left;
		} else if (offset > info->offset) {
			p = &(*p)->rb_right;
		} else {
			/*
			 * we could have a bitmap entry and an extent entry
			 * share the same offset.  If this is the case, we want
			 * the extent entry to always be found first if we do a
			 * linear search through the tree, since we want to have
			 * the quickest allocation time, and allocating from an
			 * extent is faster than allocating from a bitmap.  So
			 * if we're inserting a bitmap and we find an entry at
			 * this offset, we want to go right, or after this entry
			 * logically.  If we are inserting an extent and we've
			 * found a bitmap, we want to go left, or before
			 * logically.
			 */
			if (bitmap) {
				if (info->bitmap) {
					WARN_ON_ONCE(1);
					return -EEXIST;
				}
				p = &(*p)->rb_right;
			} else {
				if (!info->bitmap) {
					WARN_ON_ONCE(1);
					return -EEXIST;
				}
				p = &(*p)->rb_left;
			}
		}
	}

	rb_link_node(node, parent, p);
	rb_insert_color(node, root);

	return 0;
}
tree_search_offset(struct btrfs_free_space_ctl *ctl,
		   u64 offset, int bitmap_only, int fuzzy)
{
	struct rb_node *n = ctl->free_space_offset.rb_node;
	struct btrfs_free_space *entry, *prev = NULL;

	/* find entry that is closest to the 'offset' */
	while (1) {
		if (!n) {
			entry = NULL;
			break;
		}

		entry = rb_entry(n, struct btrfs_free_space, offset_index);
		prev = entry;

		if (offset < entry->offset)
			n = n->rb_left;
		else if (offset > entry->offset)
			n = n->rb_right;
		else
			break;
	}

	if (bitmap_only) {
		if (!entry)
			return NULL;
		if (entry->bitmap)
			return entry;

		/*
		 * bitmap entry and extent entry may share same offset,
		 * in that case, bitmap entry comes after extent entry.
		 */
		n = rb_next(n);
		if (!n)
			return NULL;
		entry = rb_entry(n, struct btrfs_free_space, offset_index);
		if (entry->offset != offset)
			return NULL;

		WARN_ON(!entry->bitmap);
		return entry;
	} else if (entry) {
		if (entry->bitmap) {
			/*
			 * if previous extent entry covers the offset,
			 * we should return it instead of the bitmap entry
			 */
			n = rb_prev(&entry->offset_index);
			if (n) {
				prev = rb_entry(n, struct btrfs_free_space,
						offset_index);
				if (!prev->bitmap &&
				    prev->offset + prev->bytes > offset)
					entry = prev;
			}
		}
		return entry;
	}

	if (!prev)
		return NULL;

	/* find last entry before the 'offset' */
	entry = prev;
	if (entry->offset > offset) {
		n = rb_prev(&entry->offset_index);
		if (n) {
			entry = rb_entry(n, struct btrfs_free_space,
					offset_index);
			ASSERT(entry->offset <= offset);
		} else {
			if (fuzzy)
				return entry;
			else
				return NULL;
		}
	}

	if (entry->bitmap) {
		n = rb_prev(&entry->offset_index);
		if (n) {
			prev = rb_entry(n, struct btrfs_free_space,
					offset_index);
			if (!prev->bitmap &&
			    prev->offset + prev->bytes > offset)
				return prev;
		}
		if (entry->offset + BITS_PER_BITMAP * ctl->unit > offset)
			return entry;
	} else if (entry->offset + entry->bytes > offset)
		return entry;

	if (!fuzzy)
		return NULL;

	while (1) {
		if (entry->bitmap) {
			if (entry->offset + BITS_PER_BITMAP *
			    ctl->unit > offset)
				break;
		} else {
			if (entry->offset + entry->bytes > offset)
				break;
		}

		n = rb_next(&entry->offset_index);
		if (!n)
			return NULL;
		entry = rb_entry(n, struct btrfs_free_space, offset_index);
	}
	return entry;
}
find_free_space(struct btrfs_free_space_ctl *ctl, u64 *offset, u64 *bytes,
		unsigned long align, u64 *max_extent_size)
{
	struct btrfs_free_space *entry;
	struct rb_node *node;
	u64 tmp;
	u64 align_off;
	int ret;

	if (!ctl->free_space_offset.rb_node)
		goto out;

	entry = tree_search_offset(ctl, offset_to_bitmap(ctl, *offset), 0, 1);
	if (!entry)
		goto out;

	for (node = &entry->offset_index; node; node = rb_next(node)) {
		entry = rb_entry(node, struct btrfs_free_space, offset_index);
		if (entry->bytes < *bytes) {
			if (entry->bytes > *max_extent_size)
				*max_extent_size = entry->bytes;
			continue;
		}

		/* make sure the space returned is big enough
		 * to match our requested alignment
		 */
		if (*bytes >= align) {
			tmp = entry->offset - ctl->start + align - 1;
			tmp = div64_u64(tmp, align);
			tmp = tmp * align + ctl->start;
			align_off = tmp - entry->offset;
		} else {
			align_off = 0;
			tmp = entry->offset;
		}

		if (entry->bytes < *bytes + align_off) {
			if (entry->bytes > *max_extent_size)
				*max_extent_size = entry->bytes;
			continue;
		}

		if (entry->bitmap) {
			u64 size = *bytes;

			ret = search_bitmap(ctl, entry, &tmp, &size, true);
			if (!ret) {
				*offset = tmp;
				*bytes = size;
				return entry;
			} else if (size > *max_extent_size) {
				*max_extent_size = size;
			}
			continue;
		}

		*offset = tmp;
		*bytes = entry->bytes - align_off;
		return entry;
	}
out:
	return NULL;
}
void btrfs_dump_free_space(struct btrfs_block_group_cache *block_group,
			   u64 bytes)
{
	struct btrfs_fs_info *fs_info = block_group->fs_info;
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *info;
	struct rb_node *n;
	int count = 0;

	for (n = rb_first(&ctl->free_space_offset); n; n = rb_next(n)) {
		info = rb_entry(n, struct btrfs_free_space, offset_index);
		if (info->bytes >= bytes && !block_group->ro)
			count++;
		btrfs_crit(fs_info, "entry offset %llu, bytes %llu, bitmap %s",
			   info->offset, info->bytes,
		       (info->bitmap) ? "yes" : "no");
	}
	btrfs_info(fs_info, "block group has cluster?: %s",
	       list_empty(&block_group->cluster_list) ? "no" : "yes");
	btrfs_info(fs_info,
		   "%d blocks of free space at or bigger than bytes is", count);
}
			     struct btrfs_block_group_cache *block_group,
			     struct btrfs_free_cluster *cluster)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *entry;
	struct rb_node *node;

	spin_lock(&cluster->lock);
	if (cluster->block_group != block_group)
		goto out;

	cluster->block_group = NULL;
	cluster->window_start = 0;
	list_del_init(&cluster->block_group_list);

	node = rb_first(&cluster->root);
	while (node) {
		bool bitmap;

		entry = rb_entry(node, struct btrfs_free_space, offset_index);
		node = rb_next(&entry->offset_index);
		rb_erase(&entry->offset_index, &cluster->root);
		RB_CLEAR_NODE(&entry->offset_index);

		bitmap = (entry->bitmap != NULL);
		if (!bitmap) {
			try_merge_free_space(ctl, entry, false);
			steal_from_bitmap(ctl, entry, false);
		}
		tree_insert_offset(&ctl->free_space_offset,
				   entry->offset, &entry->offset_index, bitmap);
	}
	cluster->root = RB_ROOT;

out:
	spin_unlock(&cluster->lock);
	btrfs_put_block_group(block_group);
	return 0;
}
static void __btrfs_remove_free_space_cache_locked(
				struct btrfs_free_space_ctl *ctl)
{
	struct btrfs_free_space *info;
	struct rb_node *node;

	while ((node = rb_last(&ctl->free_space_offset)) != NULL) {
		info = rb_entry(node, struct btrfs_free_space, offset_index);
		if (!info->bitmap) {
			unlink_free_space(ctl, info);
			kmem_cache_free(btrfs_free_space_cachep, info);
		} else {
			free_bitmap(ctl, info);
		}

		cond_resched_lock(&ctl->tree_lock);
	}
}

void btrfs_remove_free_space_cache(struct btrfs_block_group_cache *block_group)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_cluster *cluster;
	struct list_head *head;

	spin_lock(&ctl->tree_lock);
	while ((head = block_group->cluster_list.next) !=
	       &block_group->cluster_list) {
		cluster = list_entry(head, struct btrfs_free_cluster,
				     block_group_list);

		WARN_ON(cluster->block_group != block_group);
		__btrfs_return_cluster_to_free_space(block_group, cluster);

		cond_resched_lock(&ctl->tree_lock);
	}
	__btrfs_remove_free_space_cache_locked(ctl);
	spin_unlock(&ctl->tree_lock);

}
			     struct btrfs_free_cluster *cluster, u64 bytes,
			     u64 min_start, u64 *max_extent_size)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *entry = NULL;
	struct rb_node *node;
	u64 ret = 0;

	spin_lock(&cluster->lock);
	if (bytes > cluster->max_size)
		goto out;

	if (cluster->block_group != block_group)
		goto out;

	node = rb_first(&cluster->root);
	if (!node)
		goto out;

	entry = rb_entry(node, struct btrfs_free_space, offset_index);
	while (1) {
		if (entry->bytes < bytes && entry->bytes > *max_extent_size)
			*max_extent_size = entry->bytes;

		if (entry->bytes < bytes ||
		    (!entry->bitmap && entry->offset < min_start)) {
			node = rb_next(&entry->offset_index);
			if (!node)
				break;
			entry = rb_entry(node, struct btrfs_free_space,
					 offset_index);
			continue;
		}

		if (entry->bitmap) {
			ret = btrfs_alloc_from_bitmap(block_group,
						      cluster, entry, bytes,
						      cluster->window_start,
						      max_extent_size);
			if (ret == 0) {
				node = rb_next(&entry->offset_index);
				if (!node)
					break;
				entry = rb_entry(node, struct btrfs_free_space,
						 offset_index);
				continue;
			}
			cluster->window_start += bytes;
		} else {
			ret = entry->offset;

			entry->offset += bytes;
			entry->bytes -= bytes;
		}

		if (entry->bytes == 0)
			rb_erase(&entry->offset_index, &cluster->root);
		break;
	}
out:
	spin_unlock(&cluster->lock);

	if (!ret)
		return 0;

	spin_lock(&ctl->tree_lock);

	ctl->free_space -= bytes;
	if (entry->bytes == 0) {
		ctl->free_extents--;
		if (entry->bitmap) {
			kfree(entry->bitmap);
			ctl->total_bitmaps--;
			ctl->op->recalc_thresholds(ctl);
		}
		kmem_cache_free(btrfs_free_space_cachep, entry);
	}

	spin_unlock(&ctl->tree_lock);

	return ret;
}
			struct list_head *bitmaps, u64 offset, u64 bytes,
			u64 cont1_bytes, u64 min_bytes)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *first = NULL;
	struct btrfs_free_space *entry = NULL;
	struct btrfs_free_space *last;
	struct rb_node *node;
	u64 window_free;
	u64 max_extent;
	u64 total_size = 0;

	entry = tree_search_offset(ctl, offset, 0, 1);
	if (!entry)
		return -ENOSPC;

	/*
	 * We don't want bitmaps, so just move along until we find a normal
	 * extent entry.
	 */
	while (entry->bitmap || entry->bytes < min_bytes) {
		if (entry->bitmap && list_empty(&entry->list))
			list_add_tail(&entry->list, bitmaps);
		node = rb_next(&entry->offset_index);
		if (!node)
			return -ENOSPC;
		entry = rb_entry(node, struct btrfs_free_space, offset_index);
	}

	window_free = entry->bytes;
	max_extent = entry->bytes;
	first = entry;
	last = entry;

	for (node = rb_next(&entry->offset_index); node;
	     node = rb_next(&entry->offset_index)) {
		entry = rb_entry(node, struct btrfs_free_space, offset_index);

		if (entry->bitmap) {
			if (list_empty(&entry->list))
				list_add_tail(&entry->list, bitmaps);
			continue;
		}

		if (entry->bytes < min_bytes)
			continue;

		last = entry;
		window_free += entry->bytes;
		if (entry->bytes > max_extent)
			max_extent = entry->bytes;
	}

	if (window_free < bytes || max_extent < cont1_bytes)
		return -ENOSPC;

	cluster->window_start = first->offset;

	node = &first->offset_index;

	/*
	 * now we've found our entries, pull them out of the free space
	 * cache and put them into the cluster rbtree
	 */
	do {
		int ret;

		entry = rb_entry(node, struct btrfs_free_space, offset_index);
		node = rb_next(&entry->offset_index);
		if (entry->bitmap || entry->bytes < min_bytes)
			continue;

		rb_erase(&entry->offset_index, &ctl->free_space_offset);
		ret = tree_insert_offset(&cluster->root, entry->offset,
					 &entry->offset_index, 0);
		total_size += entry->bytes;
		ASSERT(!ret); /* -EEXIST; Logic error */
	} while (node && entry != last);

	cluster->max_size = max_extent;
	trace_btrfs_setup_cluster(block_group, cluster, total_size, 0);
	return 0;
}
static int trim_no_bitmap(struct btrfs_block_group_cache *block_group,
			  u64 *total_trimmed, u64 start, u64 end, u64 minlen)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *entry;
	struct rb_node *node;
	int ret = 0;
	u64 extent_start;
	u64 extent_bytes;
	u64 bytes;

	while (start < end) {
		struct btrfs_trim_range trim_entry;

		mutex_lock(&ctl->cache_writeout_mutex);
		spin_lock(&ctl->tree_lock);

		if (ctl->free_space < minlen) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			break;
		}

		entry = tree_search_offset(ctl, start, 0, 1);
		if (!entry) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			break;
		}

		/* skip bitmaps */
		while (entry->bitmap) {
			node = rb_next(&entry->offset_index);
			if (!node) {
				spin_unlock(&ctl->tree_lock);
				mutex_unlock(&ctl->cache_writeout_mutex);
				goto out;
			}
			entry = rb_entry(node, struct btrfs_free_space,
					 offset_index);
		}

		if (entry->offset >= end) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			break;
		}

		extent_start = entry->offset;
		extent_bytes = entry->bytes;
		start = max(start, extent_start);
		bytes = min(extent_start + extent_bytes, end) - start;
		if (bytes < minlen) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			goto next;
		}

		unlink_free_space(ctl, entry);
		kmem_cache_free(btrfs_free_space_cachep, entry);

		spin_unlock(&ctl->tree_lock);
		trim_entry.start = extent_start;
		trim_entry.bytes = extent_bytes;
		list_add_tail(&trim_entry.list, &ctl->trimming_ranges);
		mutex_unlock(&ctl->cache_writeout_mutex);

		ret = do_trimming(block_group, total_trimmed, start, bytes,
				  extent_start, extent_bytes, &trim_entry);
		if (ret)
			break;
next:
		start += bytes;

		if (fatal_signal_pending(current)) {
			ret = -ERESTARTSYS;
			break;
		}

		cond_resched();
	}
out:
	return ret;
}
static int trim_bitmaps(struct btrfs_block_group_cache *block_group,
			u64 *total_trimmed, u64 start, u64 end, u64 minlen)
{
	struct btrfs_free_space_ctl *ctl = block_group->free_space_ctl;
	struct btrfs_free_space *entry;
	int ret = 0;
	int ret2;
	u64 bytes;
	u64 offset = offset_to_bitmap(ctl, start);

	while (offset < end) {
		bool next_bitmap = false;
		struct btrfs_trim_range trim_entry;

		mutex_lock(&ctl->cache_writeout_mutex);
		spin_lock(&ctl->tree_lock);

		if (ctl->free_space < minlen) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			break;
		}

		entry = tree_search_offset(ctl, offset, 1, 0);
		if (!entry) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			next_bitmap = true;
			goto next;
		}

		bytes = minlen;
		ret2 = search_bitmap(ctl, entry, &start, &bytes, false);
		if (ret2 || start >= end) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			next_bitmap = true;
			goto next;
		}

		bytes = min(bytes, end - start);
		if (bytes < minlen) {
			spin_unlock(&ctl->tree_lock);
			mutex_unlock(&ctl->cache_writeout_mutex);
			goto next;
		}

		bitmap_clear_bits(ctl, entry, start, bytes);
		if (entry->bytes == 0)
			free_bitmap(ctl, entry);

		spin_unlock(&ctl->tree_lock);
		trim_entry.start = start;
		trim_entry.bytes = bytes;
		list_add_tail(&trim_entry.list, &ctl->trimming_ranges);
		mutex_unlock(&ctl->cache_writeout_mutex);

		ret = do_trimming(block_group, total_trimmed, start, bytes,
				  start, bytes, &trim_entry);
		if (ret)
			break;
next:
		if (next_bitmap) {
			offset += BITS_PER_BITMAP * ctl->unit;
		} else {
			start += bytes;
			if (start >= offset + BITS_PER_BITMAP * ctl->unit)
				offset += BITS_PER_BITMAP * ctl->unit;
		}

		if (fatal_signal_pending(current)) {
			ret = -ERESTARTSYS;
			break;
		}

		cond_resched();
	}

	return ret;
}
int test_check_exists(struct btrfs_block_group_cache *cache,
		      u64 offset, u64 bytes)
{
	struct btrfs_free_space_ctl *ctl = cache->free_space_ctl;
	struct btrfs_free_space *info;
	int ret = 0;

	spin_lock(&ctl->tree_lock);
	info = tree_search_offset(ctl, offset, 0, 0);
	if (!info) {
		info = tree_search_offset(ctl, offset_to_bitmap(ctl, offset),
					  1, 0);
		if (!info)
			goto out;
	}

have_info:
	if (info->bitmap) {
		u64 bit_off, bit_bytes;
		struct rb_node *n;
		struct btrfs_free_space *tmp;

		bit_off = offset;
		bit_bytes = ctl->unit;
		ret = search_bitmap(ctl, info, &bit_off, &bit_bytes, false);
		if (!ret) {
			if (bit_off == offset) {
				ret = 1;
				goto out;
			} else if (bit_off > offset &&
				   offset + bytes > bit_off) {
				ret = 1;
				goto out;
			}
		}

		n = rb_prev(&info->offset_index);
		while (n) {
			tmp = rb_entry(n, struct btrfs_free_space,
				       offset_index);
			if (tmp->offset + tmp->bytes < offset)
				break;
			if (offset + bytes < tmp->offset) {
				n = rb_prev(&tmp->offset_index);
				continue;
			}
			info = tmp;
			goto have_info;
		}

		n = rb_next(&info->offset_index);
		while (n) {
			tmp = rb_entry(n, struct btrfs_free_space,
				       offset_index);
			if (offset + bytes < tmp->offset)
				break;
			if (tmp->offset + tmp->bytes < offset) {
				n = rb_next(&tmp->offset_index);
				continue;
			}
			info = tmp;
			goto have_info;
		}

		ret = 0;
		goto out;
	}

	if (info->offset == offset) {
		ret = 1;
		goto out;
	}

	if (offset > info->offset && offset < info->offset + info->bytes)
		ret = 1;
out:
	spin_unlock(&ctl->tree_lock);
	return ret;
}
