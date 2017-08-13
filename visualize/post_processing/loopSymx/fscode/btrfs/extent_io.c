static inline
void btrfs_leak_debug_check(void)
{
	struct extent_state *state;
	struct extent_buffer *eb;

	while (!list_empty(&states)) {
		state = list_entry(states.next, struct extent_state, leak_list);
		pr_err("BTRFS: state leak: start %llu end %llu state %u in tree %d refs %d\n",
		       state->start, state->end, state->state,
		       extent_state_in_tree(state),
		       refcount_read(&state->refs));
		list_del(&state->leak_list);
		kmem_cache_free(extent_state_cache, state);
	}

	while (!list_empty(&buffers)) {
		eb = list_entry(buffers.next, struct extent_buffer, leak_list);
		pr_err("BTRFS: buffer leak start %llu len %lu refs %d\n",
		       eb->start, eb->len, atomic_read(&eb->refs));
		list_del(&eb->leak_list);
		kmem_cache_free(extent_buffer_cache, eb);
	}
}
				 struct extent_changeset *changeset,
				 int set)
{
	int ret;

	if (!changeset)
		return;
	if (set && (state->state & bits) == bits)
		return;
	if (!set && (state->state & bits) == 0)
		return;
	changeset->bytes_changed += state->end - state->start + 1;
	ret = ulist_add(&changeset->range_changed, state->start, state->end,
			GFP_ATOMIC);
	/* ENOMEM */
	BUG_ON(ret < 0);
}
				   struct rb_node ***p_in,
				   struct rb_node **parent_in)
{
	struct rb_node **p;
	struct rb_node *parent = NULL;
	struct tree_entry *entry;

	if (p_in && parent_in) {
		p = *p_in;
		parent = *parent_in;
		goto do_insert;
	}

	p = search_start ? &search_start : &root->rb_node;
	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct tree_entry, rb_node);

		if (offset < entry->start)
			p = &(*p)->rb_left;
		else if (offset > entry->end)
			p = &(*p)->rb_right;
		else
			return parent;
	}

do_insert:
	rb_link_node(node, parent, p);
	rb_insert_color(node, root);
	return NULL;
}
				      struct rb_node ***p_ret,
				      struct rb_node **parent_ret)
{
	struct rb_root *root = &tree->state;
	struct rb_node **n = &root->rb_node;
	struct rb_node *prev = NULL;
	struct rb_node *orig_prev = NULL;
	struct tree_entry *entry;
	struct tree_entry *prev_entry = NULL;

	while (*n) {
		prev = *n;
		entry = rb_entry(prev, struct tree_entry, rb_node);
		prev_entry = entry;

		if (offset < entry->start)
			n = &(*n)->rb_left;
		else if (offset > entry->end)
			n = &(*n)->rb_right;
		else
			return *n;
	}

	if (p_ret)
		*p_ret = n;
	if (parent_ret)
		*parent_ret = prev;

	if (prev_ret) {
		orig_prev = prev;
		while (prev && offset > prev_entry->end) {
			prev = rb_next(prev);
			prev_entry = rb_entry(prev, struct tree_entry, rb_node);
		}
		*prev_ret = prev;
		prev = orig_prev;
	}

	if (next_ret) {
		prev_entry = rb_entry(prev, struct tree_entry, rb_node);
		while (prev && offset < prev_entry->start) {
			prev = rb_prev(prev);
			prev_entry = rb_entry(prev, struct tree_entry, rb_node);
		}
		*next_ret = prev;
	}
	return NULL;
}
static void wait_extent_bit(struct extent_io_tree *tree, u64 start, u64 end,
			    unsigned long bits)
{
	struct extent_state *state;
	struct rb_node *node;

	btrfs_debug_check_extent_io_range(tree, start, end);

	spin_lock(&tree->lock);
again:
	while (1) {
		/*
		 * this search will find all the extents that end after
		 * our range starts
		 */
		node = tree_search(tree, start);
process_node:
		if (!node)
			break;

		state = rb_entry(node, struct extent_state, rb_node);

		if (state->start > end)
			goto out;

		if (state->state & bits) {
			start = state->start;
			refcount_inc(&state->refs);
			wait_on_state(tree, state);
			free_extent_state(state);
			goto again;
		}
		start = state->end + 1;

		if (start > end)
			break;

		if (!cond_resched_lock(&tree->lock)) {
			node = rb_next(node);
			goto process_node;
		}
	}
out:
	spin_unlock(&tree->lock);
}
int lock_extent_bits(struct extent_io_tree *tree, u64 start, u64 end,
		     struct extent_state **cached_state)
{
	int err;
	u64 failed_start;

	while (1) {
		err = __set_extent_bit(tree, start, end, EXTENT_LOCKED,
				       EXTENT_LOCKED, &failed_start,
				       cached_state, GFP_NOFS, NULL);
		if (err == -EEXIST) {
			wait_extent_bit(tree, failed_start, end, EXTENT_LOCKED);
			start = failed_start;
		} else
			break;
		WARN_ON(start > end);
	}
	return err;
}

void extent_range_clear_dirty_for_io(struct inode *inode, u64 start, u64 end)
{
	unsigned long index = start >> PAGE_SHIFT;
	unsigned long end_index = end >> PAGE_SHIFT;
	struct page *page;

	while (index <= end_index) {
		page = find_get_page(inode->i_mapping, index);
		BUG_ON(!page); /* Pages should be in the extent_io_tree */
		clear_page_dirty_for_io(page);
		put_page(page);
		index++;
	}
}

void extent_range_redirty_for_io(struct inode *inode, u64 start, u64 end)
{
	unsigned long index = start >> PAGE_SHIFT;
	unsigned long end_index = end >> PAGE_SHIFT;
	struct page *page;

	while (index <= end_index) {
		page = find_get_page(inode->i_mapping, index);
		BUG_ON(!page); /* Pages should be in the extent_io_tree */
		__set_page_dirty_nobuffers(page);
		account_page_redirty(page);
		put_page(page);
		index++;
	}
}
 */
static void set_range_writeback(struct extent_io_tree *tree, u64 start, u64 end)
{
	unsigned long index = start >> PAGE_SHIFT;
	unsigned long end_index = end >> PAGE_SHIFT;
	struct page *page;

	while (index <= end_index) {
		page = find_get_page(tree->mapping, index);
		BUG_ON(!page); /* Pages should be in the extent_io_tree */
		set_page_writeback(page);
		put_page(page);
		index++;
	}
}
find_first_extent_bit_state(struct extent_io_tree *tree,
			    u64 start, unsigned bits)
{
	struct rb_node *node;
	struct extent_state *state;

	/*
	 * this search will find all the extents that end after
	 * our range starts.
	 */
	node = tree_search(tree, start);
	if (!node)
		goto out;

	while (1) {
		state = rb_entry(node, struct extent_state, rb_node);
		if (state->end >= start && (state->state & bits))
			return state;

		node = rb_next(node);
		if (!node)
			break;
	}
out:
	return NULL;
}
			  u64 *start_ret, u64 *end_ret, unsigned bits,
			  struct extent_state **cached_state)
{
	struct extent_state *state;
	struct rb_node *n;
	int ret = 1;

	spin_lock(&tree->lock);
	if (cached_state && *cached_state) {
		state = *cached_state;
		if (state->end == start - 1 && extent_state_in_tree(state)) {
			n = rb_next(&state->rb_node);
			while (n) {
				state = rb_entry(n, struct extent_state,
						 rb_node);
				if (state->state & bits)
					goto got_it;
				n = rb_next(n);
			}
			free_extent_state(*cached_state);
			*cached_state = NULL;
			goto out;
		}
		free_extent_state(*cached_state);
		*cached_state = NULL;
	}

	state = find_first_extent_bit_state(tree, start, bits);
got_it:
	if (state) {
		cache_state_if_flags(state, cached_state, 0);
		*start_ret = state->start;
		*end_ret = state->end;
		ret = 0;
	}
out:
	spin_unlock(&tree->lock);
	return ret;
}
					u64 *start, u64 *end, u64 max_bytes,
					struct extent_state **cached_state)
{
	struct rb_node *node;
	struct extent_state *state;
	u64 cur_start = *start;
	u64 found = 0;
	u64 total_bytes = 0;

	spin_lock(&tree->lock);

	/*
	 * this search will find all the extents that end after
	 * our range starts.
	 */
	node = tree_search(tree, cur_start);
	if (!node) {
		if (!found)
			*end = (u64)-1;
		goto out;
	}

	while (1) {
		state = rb_entry(node, struct extent_state, rb_node);
		if (found && (state->start != cur_start ||
			      (state->state & EXTENT_BOUNDARY))) {
			goto out;
		}
		if (!(state->state & EXTENT_DELALLOC)) {
			if (!found)
				*end = state->end;
			goto out;
		}
		if (!found) {
			*start = state->start;
			*cached_state = state;
			refcount_inc(&state->refs);
		}
		found++;
		*end = state->end;
		cur_start = state->end + 1;
		node = rb_next(node);
		total_bytes += state->end - state->start + 1;
		if (total_bytes >= max_bytes)
			break;
		if (!node)
			break;
	}
out:
	spin_unlock(&tree->lock);
	return found;
}
				  pgoff_t start_index, pgoff_t end_index,
				  unsigned long page_ops, pgoff_t *index_ret)
{
	unsigned long nr_pages = end_index - start_index + 1;
	unsigned long pages_locked = 0;
	pgoff_t index = start_index;
	struct page *pages[16];
	unsigned ret;
	int err = 0;
	int i;

	if (page_ops & PAGE_LOCK) {
		ASSERT(page_ops == PAGE_LOCK);
		ASSERT(index_ret && *index_ret == start_index);
	}

	if ((page_ops & PAGE_SET_ERROR) && nr_pages > 0)
		mapping_set_error(mapping, -EIO);

	while (nr_pages > 0) {
		ret = find_get_pages_contig(mapping, index,
				     min_t(unsigned long,
				     nr_pages, ARRAY_SIZE(pages)), pages);
		if (ret == 0) {
			/*
			 * Only if we're going to lock these pages,
			 * can we find nothing at @index.
			 */
			ASSERT(page_ops & PAGE_LOCK);
			err = -EAGAIN;
			goto out;
		}

		for (i = 0; i < ret; i++) {
			if (page_ops & PAGE_SET_PRIVATE2)
				SetPagePrivate2(pages[i]);

			if (pages[i] == locked_page) {
				put_page(pages[i]);
				pages_locked++;
				continue;
			}
			if (page_ops & PAGE_CLEAR_DIRTY)
				clear_page_dirty_for_io(pages[i]);
			if (page_ops & PAGE_SET_WRITEBACK)
				set_page_writeback(pages[i]);
			if (page_ops & PAGE_SET_ERROR)
				SetPageError(pages[i]);
			if (page_ops & PAGE_END_WRITEBACK)
				end_page_writeback(pages[i]);
			if (page_ops & PAGE_UNLOCK)
				unlock_page(pages[i]);
			if (page_ops & PAGE_LOCK) {
				lock_page(pages[i]);
				if (!PageDirty(pages[i]) ||
				    pages[i]->mapping != mapping) {
					unlock_page(pages[i]);
					put_page(pages[i]);
					err = -EAGAIN;
					goto out;
				}
			}
			put_page(pages[i]);
			pages_locked++;
		}
		nr_pages -= ret;
		index += ret;
		cond_resched();
	}
out:
	if (err && index_ret)
		*index_ret = start_index + pages_locked - 1;
	return err;
}
		     u64 *start, u64 search_end, u64 max_bytes,
		     unsigned bits, int contig)
{
	struct rb_node *node;
	struct extent_state *state;
	u64 cur_start = *start;
	u64 total_bytes = 0;
	u64 last = 0;
	int found = 0;

	if (WARN_ON(search_end <= cur_start))
		return 0;

	spin_lock(&tree->lock);
	if (cur_start == 0 && bits == EXTENT_DIRTY) {
		total_bytes = tree->dirty_bytes;
		goto out;
	}
	/*
	 * this search will find all the extents that end after
	 * our range starts.
	 */
	node = tree_search(tree, cur_start);
	if (!node)
		goto out;

	while (1) {
		state = rb_entry(node, struct extent_state, rb_node);
		if (state->start > search_end)
			break;
		if (contig && found && state->start > last + 1)
			break;
		if (state->end >= cur_start && (state->state & bits) == bits) {
			total_bytes += min(search_end, state->end) + 1 -
				       max(cur_start, state->start);
			if (total_bytes >= max_bytes)
				break;
			if (!found) {
				*start = max(cur_start, state->start);
				found = 1;
			}
			last = state->end;
		} else if (contig && found) {
			break;
		}
		node = rb_next(node);
		if (!node)
			break;
	}
out:
	spin_unlock(&tree->lock);
	return total_bytes;
}
int test_range_bit(struct extent_io_tree *tree, u64 start, u64 end,
		   unsigned bits, int filled, struct extent_state *cached)
{
	struct extent_state *state = NULL;
	struct rb_node *node;
	int bitset = 0;

	spin_lock(&tree->lock);
	if (cached && extent_state_in_tree(cached) && cached->start <= start &&
	    cached->end > start)
		node = &cached->rb_node;
	else
		node = tree_search(tree, start);
	while (node && start <= end) {
		state = rb_entry(node, struct extent_state, rb_node);

		if (filled && state->start > start) {
			bitset = 0;
			break;
		}

		if (state->start > end)
			break;

		if (state->state & bits) {
			bitset = 1;
			if (!filled)
				break;
		} else if (filled) {
			bitset = 0;
			break;
		}

		if (state->end == (u64)-1)
			break;

		start = state->end + 1;
		if (start > end)
			break;
		node = rb_next(node);
		if (!node) {
			if (filled)
				bitset = 0;
			break;
		}
	}
	spin_unlock(&tree->lock);
	return bitset;
}
int repair_eb_io_failure(struct btrfs_fs_info *fs_info,
			 struct extent_buffer *eb, int mirror_num)
{
	u64 start = eb->start;
	unsigned long i, num_pages = num_extent_pages(eb->start, eb->len);
	int ret = 0;

	if (fs_info->sb->s_flags & MS_RDONLY)
		return -EROFS;

	for (i = 0; i < num_pages; i++) {
		struct page *p = eb->pages[i];

		ret = repair_io_failure(BTRFS_I(fs_info->btree_inode), start,
					PAGE_SIZE, start, p,
					start - page_offset(p), mirror_num);
		if (ret)
			break;
		start += PAGE_SIZE;
	}

	return ret;
}
 */
void btrfs_free_io_failure_record(struct btrfs_inode *inode, u64 start, u64 end)
{
	struct extent_io_tree *failure_tree = &inode->io_failure_tree;
	struct io_failure_record *failrec;
	struct extent_state *state, *next;

	if (RB_EMPTY_ROOT(&failure_tree->state))
		return;

	spin_lock(&failure_tree->lock);
	state = find_first_extent_bit_state(failure_tree, start, EXTENT_DIRTY);
	while (state) {
		if (state->start > end)
			break;

		ASSERT(state->end <= end);

		next = next_state(state);

		failrec = state->failrec;
		free_extent_state(state);
		kfree(failrec);

		state = next;
	}
	spin_unlock(&failure_tree->lock);
}
btrfs_bio_alloc(struct block_device *bdev, u64 first_sector, int nr_vecs,
		gfp_t gfp_flags)
{
	struct btrfs_io_bio *btrfs_bio;
	struct bio *bio;

	bio = bio_alloc_bioset(gfp_flags, nr_vecs, btrfs_bioset);

	if (bio == NULL && (current->flags & PF_MEMALLOC)) {
		while (!bio && (nr_vecs /= 2)) {
			bio = bio_alloc_bioset(gfp_flags,
					       nr_vecs, btrfs_bioset);
		}
	}

	if (bio) {
		bio->bi_bdev = bdev;
		bio->bi_iter.bi_sector = first_sector;
		btrfs_bio = btrfs_io_bio(bio);
		btrfs_bio->csum = NULL;
		btrfs_bio->csum_allocated = NULL;
		btrfs_bio->end_io = NULL;
	}
	return bio;
}
			 unsigned long *bio_flags, int read_flags,
			 u64 *prev_em_start)
{
	struct inode *inode = page->mapping->host;
	u64 start = page_offset(page);
	u64 page_end = start + PAGE_SIZE - 1;
	u64 end;
	u64 cur = start;
	u64 extent_offset;
	u64 last_byte = i_size_read(inode);
	u64 block_start;
	u64 cur_end;
	sector_t sector;
	struct extent_map *em;
	struct block_device *bdev;
	int ret = 0;
	int nr = 0;
	size_t pg_offset = 0;
	size_t iosize;
	size_t disk_io_size;
	size_t blocksize = inode->i_sb->s_blocksize;
	unsigned long this_bio_flag = 0;

	set_page_extent_mapped(page);

	end = page_end;
	if (!PageUptodate(page)) {
		if (cleancache_get_page(page) == 0) {
			BUG_ON(blocksize != PAGE_SIZE);
			unlock_extent(tree, start, end);
			goto out;
		}
	}

	if (page->index == last_byte >> PAGE_SHIFT) {
		char *userpage;
		size_t zero_offset = last_byte & (PAGE_SIZE - 1);

		if (zero_offset) {
			iosize = PAGE_SIZE - zero_offset;
			userpage = kmap_atomic(page);
			memset(userpage + zero_offset, 0, iosize);
			flush_dcache_page(page);
			kunmap_atomic(userpage);
		}
	}
	while (cur <= end) {
		bool force_bio_submit = false;

		if (cur >= last_byte) {
			char *userpage;
			struct extent_state *cached = NULL;

			iosize = PAGE_SIZE - pg_offset;
			userpage = kmap_atomic(page);
			memset(userpage + pg_offset, 0, iosize);
			flush_dcache_page(page);
			kunmap_atomic(userpage);
			set_extent_uptodate(tree, cur, cur + iosize - 1,
					    &cached, GFP_NOFS);
			unlock_extent_cached(tree, cur,
					     cur + iosize - 1,
					     &cached, GFP_NOFS);
			break;
		}
		em = __get_extent_map(inode, page, pg_offset, cur,
				      end - cur + 1, get_extent, em_cached);
		if (IS_ERR_OR_NULL(em)) {
			SetPageError(page);
			unlock_extent(tree, cur, end);
			break;
		}
		extent_offset = cur - em->start;
		BUG_ON(extent_map_end(em) <= cur);
		BUG_ON(end < cur);

		if (test_bit(EXTENT_FLAG_COMPRESSED, &em->flags)) {
			this_bio_flag |= EXTENT_BIO_COMPRESSED;
			extent_set_compress_type(&this_bio_flag,
						 em->compress_type);
		}

		iosize = min(extent_map_end(em) - cur, end - cur + 1);
		cur_end = min(extent_map_end(em) - 1, end);
		iosize = ALIGN(iosize, blocksize);
		if (this_bio_flag & EXTENT_BIO_COMPRESSED) {
			disk_io_size = em->block_len;
			sector = em->block_start >> 9;
		} else {
			sector = (em->block_start + extent_offset) >> 9;
			disk_io_size = iosize;
		}
		bdev = em->bdev;
		block_start = em->block_start;
		if (test_bit(EXTENT_FLAG_PREALLOC, &em->flags))
			block_start = EXTENT_MAP_HOLE;

		/*
		 * If we have a file range that points to a compressed extent
		 * and it's followed by a consecutive file range that points to
		 * to the same compressed extent (possibly with a different
		 * offset and/or length, so it either points to the whole extent
		 * or only part of it), we must make sure we do not submit a
		 * single bio to populate the pages for the 2 ranges because
		 * this makes the compressed extent read zero out the pages
		 * belonging to the 2nd range. Imagine the following scenario:
		 *
		 *  File layout
		 *  [0 - 8K]                     [8K - 24K]
		 *    |                               |
		 *    |                               |
		 * points to extent X,         points to extent X,
		 * offset 4K, length of 8K     offset 0, length 16K
		 *
		 * [extent X, compressed length = 4K uncompressed length = 16K]
		 *
		 * If the bio to read the compressed extent covers both ranges,
		 * it will decompress extent X into the pages belonging to the
		 * first range and then it will stop, zeroing out the remaining
		 * pages that belong to the other range that points to extent X.
		 * So here we make sure we submit 2 bios, one for the first
		 * range and another one for the third range. Both will target
		 * the same physical extent from disk, but we can't currently
		 * make the compressed bio endio callback populate the pages
		 * for both ranges because each compressed bio is tightly
		 * coupled with a single extent map, and each range can have
		 * an extent map with a different offset value relative to the
		 * uncompressed data of our extent and different lengths. This
		 * is a corner case so we prioritize correctness over
		 * non-optimal behavior (submitting 2 bios for the same extent).
		 */
		if (test_bit(EXTENT_FLAG_COMPRESSED, &em->flags) &&
		    prev_em_start && *prev_em_start != (u64)-1 &&
		    *prev_em_start != em->orig_start)
			force_bio_submit = true;

		if (prev_em_start)
			*prev_em_start = em->orig_start;

		free_extent_map(em);
		em = NULL;

		/* we've found a hole, just zero and go on */
		if (block_start == EXTENT_MAP_HOLE) {
			char *userpage;
			struct extent_state *cached = NULL;

			userpage = kmap_atomic(page);
			memset(userpage + pg_offset, 0, iosize);
			flush_dcache_page(page);
			kunmap_atomic(userpage);

			set_extent_uptodate(tree, cur, cur + iosize - 1,
					    &cached, GFP_NOFS);
			unlock_extent_cached(tree, cur,
					     cur + iosize - 1,
					     &cached, GFP_NOFS);
			cur = cur + iosize;
			pg_offset += iosize;
			continue;
		}
		/* the get_extent function already copied into the page */
		if (test_range_bit(tree, cur, cur_end,
				   EXTENT_UPTODATE, 1, NULL)) {
			check_page_uptodate(tree, page);
			unlock_extent(tree, cur, cur + iosize - 1);
			cur = cur + iosize;
			pg_offset += iosize;
			continue;
		}
		/* we have an inline extent but it didn't get marked up
		 * to date.  Error out
		 */
		if (block_start == EXTENT_MAP_INLINE) {
			SetPageError(page);
			unlock_extent(tree, cur, cur + iosize - 1);
			cur = cur + iosize;
			pg_offset += iosize;
			continue;
		}

		ret = submit_extent_page(REQ_OP_READ, read_flags, tree, NULL,
					 page, sector, disk_io_size, pg_offset,
					 bdev, bio,
					 end_bio_extent_readpage, mirror_num,
					 *bio_flags,
					 this_bio_flag,
					 force_bio_submit);
		if (!ret) {
			nr++;
			*bio_flags = this_bio_flag;
		} else {
			SetPageError(page);
			unlock_extent(tree, cur, cur + iosize - 1);
			goto out;
		}
		cur = cur + iosize;
		pg_offset += iosize;
	}
out:
	if (!nr) {
		if (!PageError(page))
			SetPageUptodate(page);
		unlock_page(page);
	}
	return ret;
}
					     unsigned long *bio_flags,
					     u64 *prev_em_start)
{
	struct inode *inode;
	struct btrfs_ordered_extent *ordered;
	int index;

	inode = pages[0]->mapping->host;
	while (1) {
		lock_extent(tree, start, end);
		ordered = btrfs_lookup_ordered_range(BTRFS_I(inode), start,
						     end - start + 1);
		if (!ordered)
			break;
		unlock_extent(tree, start, end);
		btrfs_start_ordered_extent(inode, ordered, 1);
		btrfs_put_ordered_extent(ordered);
	}

	for (index = 0; index < nr_pages; index++) {
		__do_readpage(tree, pages[index], get_extent, em_cached, bio,
			      mirror_num, bio_flags, 0, prev_em_start);
		put_page(pages[index]);
	}
}
			       unsigned long *bio_flags,
			       u64 *prev_em_start)
{
	u64 start = 0;
	u64 end = 0;
	u64 page_start;
	int index;
	int first_index = 0;

	for (index = 0; index < nr_pages; index++) {
		page_start = page_offset(pages[index]);
		if (!end) {
			start = page_start;
			end = start + PAGE_SIZE - 1;
			first_index = index;
		} else if (end + 1 == page_start) {
			end += PAGE_SIZE;
		} else {
			__do_contiguous_readpages(tree, &pages[first_index],
						  index - first_index, start,
						  end, get_extent, em_cached,
						  bio, mirror_num, bio_flags,
						  prev_em_start);
			start = page_start;
			end = start + PAGE_SIZE - 1;
			first_index = index;
		}
	}

	if (end)
		__do_contiguous_readpages(tree, &pages[first_index],
					  index - first_index, start,
					  end, get_extent, em_cached, bio,
					  mirror_num, bio_flags,
					  prev_em_start);
}
				   struct bio **bio, int mirror_num,
				   unsigned long *bio_flags, int read_flags)
{
	struct inode *inode = page->mapping->host;
	struct btrfs_ordered_extent *ordered;
	u64 start = page_offset(page);
	u64 end = start + PAGE_SIZE - 1;
	int ret;

	while (1) {
		lock_extent(tree, start, end);
		ordered = btrfs_lookup_ordered_range(BTRFS_I(inode), start,
						PAGE_SIZE);
		if (!ordered)
			break;
		unlock_extent(tree, start, end);
		btrfs_start_ordered_extent(inode, ordered, 1);
		btrfs_put_ordered_extent(ordered);
	}

	ret = __do_readpage(tree, page, get_extent, NULL, bio, mirror_num,
			    bio_flags, read_flags, NULL);
	return ret;
}
			      u64 delalloc_start,
			      unsigned long *nr_written)
{
	struct extent_io_tree *tree = epd->tree;
	u64 page_end = delalloc_start + PAGE_SIZE - 1;
	u64 nr_delalloc;
	u64 delalloc_to_write = 0;
	u64 delalloc_end = 0;
	int ret;
	int page_started = 0;

	if (epd->extent_locked || !tree->ops || !tree->ops->fill_delalloc)
		return 0;

	while (delalloc_end < page_end) {
		nr_delalloc = find_lock_delalloc_range(inode, tree,
					       page,
					       &delalloc_start,
					       &delalloc_end,
					       BTRFS_MAX_EXTENT_SIZE);
		if (nr_delalloc == 0) {
			delalloc_start = delalloc_end + 1;
			continue;
		}
		ret = tree->ops->fill_delalloc(inode, page,
					       delalloc_start,
					       delalloc_end,
					       &page_started,
					       nr_written);
		/* File system has been set read-only */
		if (ret) {
			SetPageError(page);
			/* fill_delalloc should be return < 0 for error
			 * but just in case, we use > 0 here meaning the
			 * IO is started, so we don't want to return > 0
			 * unless things are going well.
			 */
			ret = ret < 0 ? ret : -EIO;
			goto done;
		}
		/*
		 * delalloc_end is already one less than the total length, so
		 * we don't subtract one from PAGE_SIZE
		 */
		delalloc_to_write += (delalloc_end - delalloc_start +
				      PAGE_SIZE) >> PAGE_SHIFT;
		delalloc_start = delalloc_end + 1;
	}
	if (wbc->nr_to_write < delalloc_to_write) {
		int thresh = 8192;

		if (delalloc_to_write < thresh * 2)
			thresh = delalloc_to_write;
		wbc->nr_to_write = min_t(u64, delalloc_to_write,
					 thresh);
	}

	/* did the fill delalloc function already unlock and start
	 * the IO?
	 */
	if (page_started) {
		/*
		 * we've unlocked the page, so we can't update
		 * the mapping's writeback index, just update
		 * nr_to_write.
		 */
		wbc->nr_to_write -= *nr_written;
		return 1;
	}

	ret = 0;

done:
	return ret;
}
				 unsigned long nr_written,
				 int write_flags, int *nr_ret)
{
	struct extent_io_tree *tree = epd->tree;
	u64 start = page_offset(page);
	u64 page_end = start + PAGE_SIZE - 1;
	u64 end;
	u64 cur = start;
	u64 extent_offset;
	u64 block_start;
	u64 iosize;
	sector_t sector;
	struct extent_map *em;
	struct block_device *bdev;
	size_t pg_offset = 0;
	size_t blocksize;
	int ret = 0;
	int nr = 0;
	bool compressed;

	if (tree->ops && tree->ops->writepage_start_hook) {
		ret = tree->ops->writepage_start_hook(page, start,
						      page_end);
		if (ret) {
			/* Fixup worker will requeue */
			if (ret == -EBUSY)
				wbc->pages_skipped++;
			else
				redirty_page_for_writepage(wbc, page);

			update_nr_written(wbc, nr_written);
			unlock_page(page);
			return 1;
		}
	}

	/*
	 * we don't want to touch the inode after unlocking the page,
	 * so we update the mapping writeback index now
	 */
	update_nr_written(wbc, nr_written + 1);

	end = page_end;
	if (i_size <= start) {
		if (tree->ops && tree->ops->writepage_end_io_hook)
			tree->ops->writepage_end_io_hook(page, start,
							 page_end, NULL, 1);
		goto done;
	}

	blocksize = inode->i_sb->s_blocksize;

	while (cur <= end) {
		u64 em_end;

		if (cur >= i_size) {
			if (tree->ops && tree->ops->writepage_end_io_hook)
				tree->ops->writepage_end_io_hook(page, cur,
							 page_end, NULL, 1);
			break;
		}
		em = epd->get_extent(BTRFS_I(inode), page, pg_offset, cur,
				     end - cur + 1, 1);
		if (IS_ERR_OR_NULL(em)) {
			SetPageError(page);
			ret = PTR_ERR_OR_ZERO(em);
			break;
		}

		extent_offset = cur - em->start;
		em_end = extent_map_end(em);
		BUG_ON(em_end <= cur);
		BUG_ON(end < cur);
		iosize = min(em_end - cur, end - cur + 1);
		iosize = ALIGN(iosize, blocksize);
		sector = (em->block_start + extent_offset) >> 9;
		bdev = em->bdev;
		block_start = em->block_start;
		compressed = test_bit(EXTENT_FLAG_COMPRESSED, &em->flags);
		free_extent_map(em);
		em = NULL;

		/*
		 * compressed and inline extents are written through other
		 * paths in the FS
		 */
		if (compressed || block_start == EXTENT_MAP_HOLE ||
		    block_start == EXTENT_MAP_INLINE) {
			/*
			 * end_io notification does not happen here for
			 * compressed extents
			 */
			if (!compressed && tree->ops &&
			    tree->ops->writepage_end_io_hook)
				tree->ops->writepage_end_io_hook(page, cur,
							 cur + iosize - 1,
							 NULL, 1);
			else if (compressed) {
				/* we don't want to end_page_writeback on
				 * a compressed extent.  this happens
				 * elsewhere
				 */
				nr++;
			}

			cur += iosize;
			pg_offset += iosize;
			continue;
		}

		set_range_writeback(tree, cur, cur + iosize - 1);
		if (!PageWriteback(page)) {
			btrfs_err(BTRFS_I(inode)->root->fs_info,
				   "page %lu not writeback, cur %llu end %llu",
			       page->index, cur, end);
		}

		ret = submit_extent_page(REQ_OP_WRITE, write_flags, tree, wbc,
					 page, sector, iosize, pg_offset,
					 bdev, &epd->bio,
					 end_bio_extent_writepage,
					 0, 0, 0, false);
		if (ret) {
			SetPageError(page);
			if (PageWriteback(page))
				end_page_writeback(page);
		}

		cur = cur + iosize;
		pg_offset += iosize;
		nr++;
	}
done:
	*nr_ret = nr;
	return ret;
}
			  struct btrfs_fs_info *fs_info,
			  struct extent_page_data *epd)
{
	unsigned long i, num_pages;
	int flush = 0;
	int ret = 0;

	if (!btrfs_try_tree_write_lock(eb)) {
		flush = 1;
		flush_write_bio(epd);
		btrfs_tree_lock(eb);
	}

	if (test_bit(EXTENT_BUFFER_WRITEBACK, &eb->bflags)) {
		btrfs_tree_unlock(eb);
		if (!epd->sync_io)
			return 0;
		if (!flush) {
			flush_write_bio(epd);
			flush = 1;
		}
		while (1) {
			wait_on_extent_buffer_writeback(eb);
			btrfs_tree_lock(eb);
			if (!test_bit(EXTENT_BUFFER_WRITEBACK, &eb->bflags))
				break;
			btrfs_tree_unlock(eb);
		}
	}

	/*
	 * We need to do this to prevent races in people who check if the eb is
	 * under IO since we can end up having no IO bits set for a short period
	 * of time.
	 */
	spin_lock(&eb->refs_lock);
	if (test_and_clear_bit(EXTENT_BUFFER_DIRTY, &eb->bflags)) {
		set_bit(EXTENT_BUFFER_WRITEBACK, &eb->bflags);
		spin_unlock(&eb->refs_lock);
		btrfs_set_header_flag(eb, BTRFS_HEADER_FLAG_WRITTEN);
		percpu_counter_add_batch(&fs_info->dirty_metadata_bytes,
					 -eb->len,
					 fs_info->dirty_metadata_batch);
		ret = 1;
	} else {
		spin_unlock(&eb->refs_lock);
	}

	btrfs_tree_unlock(eb);

	if (!ret)
		return ret;

	num_pages = num_extent_pages(eb->start, eb->len);
	for (i = 0; i < num_pages; i++) {
		struct page *p = eb->pages[i];

		if (!trylock_page(p)) {
			if (!flush) {
				flush_write_bio(epd);
				flush = 1;
			}
			lock_page(p);
		}
	}

	return ret;
}
			struct writeback_control *wbc,
			struct extent_page_data *epd)
{
	struct block_device *bdev = fs_info->fs_devices->latest_bdev;
	struct extent_io_tree *tree = &BTRFS_I(fs_info->btree_inode)->io_tree;
	u64 offset = eb->start;
	u32 nritems;
	unsigned long i, num_pages;
	unsigned long bio_flags = 0;
	unsigned long start, end;
	int write_flags = (epd->sync_io ? REQ_SYNC : 0) | REQ_META;
	int ret = 0;

	clear_bit(EXTENT_BUFFER_WRITE_ERR, &eb->bflags);
	num_pages = num_extent_pages(eb->start, eb->len);
	atomic_set(&eb->io_pages, num_pages);
	if (btrfs_header_owner(eb) == BTRFS_TREE_LOG_OBJECTID)
		bio_flags = EXTENT_BIO_TREE_LOG;

	/* set btree blocks beyond nritems with 0 to avoid stale content. */
	nritems = btrfs_header_nritems(eb);
	if (btrfs_header_level(eb) > 0) {
		end = btrfs_node_key_ptr_offset(nritems);

		memzero_extent_buffer(eb, end, eb->len - end);
	} else {
		/*
		 * leaf:
		 * header 0 1 2 .. N ... data_N .. data_2 data_1 data_0
		 */
		start = btrfs_item_nr_offset(nritems);
		end = btrfs_leaf_data(eb) + leaf_data_end(fs_info, eb);
		memzero_extent_buffer(eb, start, end - start);
	}

	for (i = 0; i < num_pages; i++) {
		struct page *p = eb->pages[i];

		clear_page_dirty_for_io(p);
		set_page_writeback(p);
		ret = submit_extent_page(REQ_OP_WRITE, write_flags, tree, wbc,
					 p, offset >> 9, PAGE_SIZE, 0, bdev,
					 &epd->bio,
					 end_bio_extent_buffer_writepage,
					 0, epd->bio_flags, bio_flags, false);
		epd->bio_flags = bio_flags;
		if (ret) {
			set_btree_ioerr(p);
			if (PageWriteback(p))
				end_page_writeback(p);
			if (atomic_sub_and_test(num_pages - i, &eb->io_pages))
				end_extent_buffer_writeback(eb);
			ret = -EIO;
			break;
		}
		offset += PAGE_SIZE;
		update_nr_written(wbc, 1);
		unlock_page(p);
	}

	if (unlikely(ret)) {
		for (; i < num_pages; i++) {
			struct page *p = eb->pages[i];
			clear_page_dirty_for_io(p);
			unlock_page(p);
		}
	}

	return ret;
}
int btree_write_cache_pages(struct address_space *mapping,
				   struct writeback_control *wbc)
{
	struct extent_io_tree *tree = &BTRFS_I(mapping->host)->io_tree;
	struct btrfs_fs_info *fs_info = BTRFS_I(mapping->host)->root->fs_info;
	struct extent_buffer *eb, *prev_eb = NULL;
	struct extent_page_data epd = {
		.bio = NULL,
		.tree = tree,
		.extent_locked = 0,
		.sync_io = wbc->sync_mode == WB_SYNC_ALL,
		.bio_flags = 0,
	};
	int ret = 0;
	int done = 0;
	int nr_to_write_done = 0;
	struct pagevec pvec;
	int nr_pages;
	pgoff_t index;
	pgoff_t end;		/* Inclusive */
	int scanned = 0;
	int tag;

	pagevec_init(&pvec, 0);
	if (wbc->range_cyclic) {
		index = mapping->writeback_index; /* Start from prev offset */
		end = -1;
	} else {
		index = wbc->range_start >> PAGE_SHIFT;
		end = wbc->range_end >> PAGE_SHIFT;
		scanned = 1;
	}
	if (wbc->sync_mode == WB_SYNC_ALL)
		tag = PAGECACHE_TAG_TOWRITE;
	else
		tag = PAGECACHE_TAG_DIRTY;
retry:
	if (wbc->sync_mode == WB_SYNC_ALL)
		tag_pages_for_writeback(mapping, index, end);
	while (!done && !nr_to_write_done && (index <= end) &&
	       (nr_pages = pagevec_lookup_tag(&pvec, mapping, &index, tag,
			min(end - index, (pgoff_t)PAGEVEC_SIZE-1) + 1))) {
		unsigned i;

		scanned = 1;
		for (i = 0; i < nr_pages; i++) {
			struct page *page = pvec.pages[i];

			if (!PagePrivate(page))
				continue;

			if (!wbc->range_cyclic && page->index > end) {
				done = 1;
				break;
			}

			spin_lock(&mapping->private_lock);
			if (!PagePrivate(page)) {
				spin_unlock(&mapping->private_lock);
				continue;
			}

			eb = (struct extent_buffer *)page->private;

			/*
			 * Shouldn't happen and normally this would be a BUG_ON
			 * but no sense in crashing the users box for something
			 * we can survive anyway.
			 */
			if (WARN_ON(!eb)) {
				spin_unlock(&mapping->private_lock);
				continue;
			}

			if (eb == prev_eb) {
				spin_unlock(&mapping->private_lock);
				continue;
			}

			ret = atomic_inc_not_zero(&eb->refs);
			spin_unlock(&mapping->private_lock);
			if (!ret)
				continue;

			prev_eb = eb;
			ret = lock_extent_buffer_for_io(eb, fs_info, &epd);
			if (!ret) {
				free_extent_buffer(eb);
				continue;
			}

			ret = write_one_eb(eb, fs_info, wbc, &epd);
			if (ret) {
				done = 1;
				free_extent_buffer(eb);
				break;
			}
			free_extent_buffer(eb);

			/*
			 * the filesystem may choose to bump up nr_to_write.
			 * We have to make sure to honor the new nr_to_write
			 * at any time
			 */
			nr_to_write_done = wbc->nr_to_write <= 0;
		}
		pagevec_release(&pvec);
		cond_resched();
	}
	if (!scanned && !done) {
		/*
		 * We hit the last page and there is more work to be done: wrap
		 * back to the start of the file
		 */
		scanned = 1;
		index = 0;
		goto retry;
	}
	flush_write_bio(&epd);
	return ret;
}
			     writepage_t writepage, void *data,
			     void (*flush_fn)(void *))
{
	struct inode *inode = mapping->host;
	int ret = 0;
	int done = 0;
	int nr_to_write_done = 0;
	struct pagevec pvec;
	int nr_pages;
	pgoff_t index;
	pgoff_t end;		/* Inclusive */
	pgoff_t done_index;
	int range_whole = 0;
	int scanned = 0;
	int tag;

	/*
	 * We have to hold onto the inode so that ordered extents can do their
	 * work when the IO finishes.  The alternative to this is failing to add
	 * an ordered extent if the igrab() fails there and that is a huge pain
	 * to deal with, so instead just hold onto the inode throughout the
	 * writepages operation.  If it fails here we are freeing up the inode
	 * anyway and we'd rather not waste our time writing out stuff that is
	 * going to be truncated anyway.
	 */
	if (!igrab(inode))
		return 0;

	pagevec_init(&pvec, 0);
	if (wbc->range_cyclic) {
		index = mapping->writeback_index; /* Start from prev offset */
		end = -1;
	} else {
		index = wbc->range_start >> PAGE_SHIFT;
		end = wbc->range_end >> PAGE_SHIFT;
		if (wbc->range_start == 0 && wbc->range_end == LLONG_MAX)
			range_whole = 1;
		scanned = 1;
	}
	if (wbc->sync_mode == WB_SYNC_ALL)
		tag = PAGECACHE_TAG_TOWRITE;
	else
		tag = PAGECACHE_TAG_DIRTY;
retry:
	if (wbc->sync_mode == WB_SYNC_ALL)
		tag_pages_for_writeback(mapping, index, end);
	done_index = index;
	while (!done && !nr_to_write_done && (index <= end) &&
	       (nr_pages = pagevec_lookup_tag(&pvec, mapping, &index, tag,
			min(end - index, (pgoff_t)PAGEVEC_SIZE-1) + 1))) {
		unsigned i;

		scanned = 1;
		for (i = 0; i < nr_pages; i++) {
			struct page *page = pvec.pages[i];

			done_index = page->index;
			/*
			 * At this point we hold neither mapping->tree_lock nor
			 * lock on the page itself: the page may be truncated or
			 * invalidated (changing page->mapping to NULL), or even
			 * swizzled back from swapper_space to tmpfs file
			 * mapping
			 */
			if (!trylock_page(page)) {
				flush_fn(data);
				lock_page(page);
			}

			if (unlikely(page->mapping != mapping)) {
				unlock_page(page);
				continue;
			}

			if (!wbc->range_cyclic && page->index > end) {
				done = 1;
				unlock_page(page);
				continue;
			}

			if (wbc->sync_mode != WB_SYNC_NONE) {
				if (PageWriteback(page))
					flush_fn(data);
				wait_on_page_writeback(page);
			}

			if (PageWriteback(page) ||
			    !clear_page_dirty_for_io(page)) {
				unlock_page(page);
				continue;
			}

			ret = (*writepage)(page, wbc, data);

			if (unlikely(ret == AOP_WRITEPAGE_ACTIVATE)) {
				unlock_page(page);
				ret = 0;
			}
			if (ret < 0) {
				/*
				 * done_index is set past this page,
				 * so media errors will not choke
				 * background writeout for the entire
				 * file. This has consequences for
				 * range_cyclic semantics (ie. it may
				 * not be suitable for data integrity
				 * writeout).
				 */
				done_index = page->index + 1;
				done = 1;
				break;
			}

			/*
			 * the filesystem may choose to bump up nr_to_write.
			 * We have to make sure to honor the new nr_to_write
			 * at any time
			 */
			nr_to_write_done = wbc->nr_to_write <= 0;
		}
		pagevec_release(&pvec);
		cond_resched();
	}
	if (!scanned && !done) {
		/*
		 * We hit the last page and there is more work to be done: wrap
		 * back to the start of the file
		 */
		scanned = 1;
		index = 0;
		goto retry;
	}

	if (wbc->range_cyclic || (wbc->nr_to_write > 0 && range_whole))
		mapping->writeback_index = done_index;

	btrfs_add_delayed_iput(inode);
	return ret;
}
			      u64 start, u64 end, get_extent_t *get_extent,
			      int mode)
{
	int ret = 0;
	struct address_space *mapping = inode->i_mapping;
	struct page *page;
	unsigned long nr_pages = (end - start + PAGE_SIZE) >>
		PAGE_SHIFT;

	struct extent_page_data epd = {
		.bio = NULL,
		.tree = tree,
		.get_extent = get_extent,
		.extent_locked = 1,
		.sync_io = mode == WB_SYNC_ALL,
		.bio_flags = 0,
	};
	struct writeback_control wbc_writepages = {
		.sync_mode	= mode,
		.nr_to_write	= nr_pages * 2,
		.range_start	= start,
		.range_end	= end + 1,
	};

	while (start <= end) {
		page = find_get_page(mapping, start >> PAGE_SHIFT);
		if (clear_page_dirty_for_io(page))
			ret = __extent_writepage(page, &wbc_writepages, &epd);
		else {
			if (tree->ops && tree->ops->writepage_end_io_hook)
				tree->ops->writepage_end_io_hook(page, start,
						 start + PAGE_SIZE - 1,
						 NULL, 1);
			unlock_page(page);
		}
		put_page(page);
		start += PAGE_SIZE;
	}

	flush_epd_write_bio(&epd);
	return ret;
}
		     struct list_head *pages, unsigned nr_pages,
		     get_extent_t get_extent)
{
	struct bio *bio = NULL;
	unsigned page_idx;
	unsigned long bio_flags = 0;
	struct page *pagepool[16];
	struct page *page;
	struct extent_map *em_cached = NULL;
	int nr = 0;
	u64 prev_em_start = (u64)-1;

	for (page_idx = 0; page_idx < nr_pages; page_idx++) {
		page = list_entry(pages->prev, struct page, lru);

		prefetchw(&page->flags);
		list_del(&page->lru);
		if (add_to_page_cache_lru(page, mapping,
					page->index,
					readahead_gfp_mask(mapping))) {
			put_page(page);
			continue;
		}

		pagepool[nr++] = page;
		if (nr < ARRAY_SIZE(pagepool))
			continue;
		__extent_readpages(tree, pagepool, nr, get_extent, &em_cached,
				   &bio, 0, &bio_flags, &prev_em_start);
		nr = 0;
	}
	if (nr)
		__extent_readpages(tree, pagepool, nr, get_extent, &em_cached,
				   &bio, 0, &bio_flags, &prev_em_start);

	if (em_cached)
		free_extent_map(em_cached);

	BUG_ON(!list_empty(pages));
	if (bio)
		return submit_one_bio(bio, 0, bio_flags);
	return 0;
}
			       struct extent_io_tree *tree, struct page *page,
			       gfp_t mask)
{
	struct extent_map *em;
	u64 start = page_offset(page);
	u64 end = start + PAGE_SIZE - 1;

	if (gfpflags_allow_blocking(mask) &&
	    page->mapping->host->i_size > SZ_16M) {
		u64 len;
		while (start <= end) {
			len = end - start + 1;
			write_lock(&map->lock);
			em = lookup_extent_mapping(map, start, len);
			if (!em) {
				write_unlock(&map->lock);
				break;
			}
			if (test_bit(EXTENT_FLAG_PINNED, &em->flags) ||
			    em->start != start) {
				write_unlock(&map->lock);
				free_extent_map(em);
				break;
			}
			if (!test_range_bit(tree, em->start,
					    extent_map_end(em) - 1,
					    EXTENT_LOCKED | EXTENT_WRITEBACK,
					    0, NULL)) {
				remove_extent_mapping(map, em);
				/* once for the rb tree */
				free_extent_map(em);
			}
			start = extent_map_end(em);
			write_unlock(&map->lock);

			/* once for us */
			free_extent_map(em);
		}
	}
	return try_release_extent_state(map, tree, page, mask);
}
						u64 last,
						get_extent_t *get_extent)
{
	u64 sectorsize = btrfs_inode_sectorsize(inode);
	struct extent_map *em;
	u64 len;

	if (offset >= last)
		return NULL;

	while (1) {
		len = last - offset;
		if (len == 0)
			break;
		len = ALIGN(len, sectorsize);
		em = get_extent(BTRFS_I(inode), NULL, 0, offset, len, 0);
		if (IS_ERR_OR_NULL(em))
			return em;

		/* if this isn't a hole return it */
		if (!test_bit(EXTENT_FLAG_VACANCY, &em->flags) &&
		    em->block_start != EXTENT_MAP_HOLE) {
			return em;
		}

		/* this is a hole, advance to the next extent */
		offset = extent_map_end(em);
		free_extent_map(em);
		if (offset >= last)
			break;
	}
	return NULL;
}
int extent_fiemap(struct inode *inode, struct fiemap_extent_info *fieinfo,
		__u64 start, __u64 len, get_extent_t *get_extent)
{
	int ret = 0;
	u64 off = start;
	u64 max = start + len;
	u32 flags = 0;
	u32 found_type;
	u64 last;
	u64 last_for_get_extent = 0;
	u64 disko = 0;
	u64 isize = i_size_read(inode);
	struct btrfs_key found_key;
	struct extent_map *em = NULL;
	struct extent_state *cached_state = NULL;
	struct btrfs_path *path;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct fiemap_cache cache = { 0 };
	int end = 0;
	u64 em_start = 0;
	u64 em_len = 0;
	u64 em_end = 0;

	if (len == 0)
		return -EINVAL;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->leave_spinning = 1;

	start = round_down(start, btrfs_inode_sectorsize(inode));
	len = round_up(max, btrfs_inode_sectorsize(inode)) - start;

	/*
	 * lookup the last file extent.  We're not using i_size here
	 * because there might be preallocation past i_size
	 */
	ret = btrfs_lookup_file_extent(NULL, root, path,
			btrfs_ino(BTRFS_I(inode)), -1, 0);
	if (ret < 0) {
		btrfs_free_path(path);
		return ret;
	} else {
		WARN_ON(!ret);
		if (ret == 1)
			ret = 0;
	}

	path->slots[0]--;
	btrfs_item_key_to_cpu(path->nodes[0], &found_key, path->slots[0]);
	found_type = found_key.type;

	/* No extents, but there might be delalloc bits */
	if (found_key.objectid != btrfs_ino(BTRFS_I(inode)) ||
	    found_type != BTRFS_EXTENT_DATA_KEY) {
		/* have to trust i_size as the end */
		last = (u64)-1;
		last_for_get_extent = isize;
	} else {
		/*
		 * remember the start of the last extent.  There are a
		 * bunch of different factors that go into the length of the
		 * extent, so its much less complex to remember where it started
		 */
		last = found_key.offset;
		last_for_get_extent = last + 1;
	}
	btrfs_release_path(path);

	/*
	 * we might have some extents allocated but more delalloc past those
	 * extents.  so, we trust isize unless the start of the last extent is
	 * beyond isize
	 */
	if (last < isize) {
		last = (u64)-1;
		last_for_get_extent = isize;
	}

	lock_extent_bits(&BTRFS_I(inode)->io_tree, start, start + len - 1,
			 &cached_state);

	em = get_extent_skip_holes(inode, start, last_for_get_extent,
				   get_extent);
	if (!em)
		goto out;
	if (IS_ERR(em)) {
		ret = PTR_ERR(em);
		goto out;
	}

	while (!end) {
		u64 offset_in_extent = 0;

		/* break if the extent we found is outside the range */
		if (em->start >= max || extent_map_end(em) < off)
			break;

		/*
		 * get_extent may return an extent that starts before our
		 * requested range.  We have to make sure the ranges
		 * we return to fiemap always move forward and don't
		 * overlap, so adjust the offsets here
		 */
		em_start = max(em->start, off);

		/*
		 * record the offset from the start of the extent
		 * for adjusting the disk offset below.  Only do this if the
		 * extent isn't compressed since our in ram offset may be past
		 * what we have actually allocated on disk.
		 */
		if (!test_bit(EXTENT_FLAG_COMPRESSED, &em->flags))
			offset_in_extent = em_start - em->start;
		em_end = extent_map_end(em);
		em_len = em_end - em_start;
		disko = 0;
		flags = 0;

		/*
		 * bump off for our next call to get_extent
		 */
		off = extent_map_end(em);
		if (off >= max)
			end = 1;

		if (em->block_start == EXTENT_MAP_LAST_BYTE) {
			end = 1;
			flags |= FIEMAP_EXTENT_LAST;
		} else if (em->block_start == EXTENT_MAP_INLINE) {
			flags |= (FIEMAP_EXTENT_DATA_INLINE |
				  FIEMAP_EXTENT_NOT_ALIGNED);
		} else if (em->block_start == EXTENT_MAP_DELALLOC) {
			flags |= (FIEMAP_EXTENT_DELALLOC |
				  FIEMAP_EXTENT_UNKNOWN);
		} else if (fieinfo->fi_extents_max) {
			struct btrfs_trans_handle *trans;

			u64 bytenr = em->block_start -
				(em->start - em->orig_start);

			disko = em->block_start + offset_in_extent;

			/*
			 * We need a trans handle to get delayed refs
			 */
			trans = btrfs_join_transaction(root);
			/*
			 * It's OK if we can't start a trans we can still check
			 * from commit_root
			 */
			if (IS_ERR(trans))
				trans = NULL;

			/*
			 * As btrfs supports shared space, this information
			 * can be exported to userspace tools via
			 * flag FIEMAP_EXTENT_SHARED.  If fi_extents_max == 0
			 * then we're just getting a count and we can skip the
			 * lookup stuff.
			 */
			ret = btrfs_check_shared(trans, root->fs_info,
					root->objectid,
					btrfs_ino(BTRFS_I(inode)), bytenr);
			if (trans)
				btrfs_end_transaction(trans);
			if (ret < 0)
				goto out_free;
			if (ret)
				flags |= FIEMAP_EXTENT_SHARED;
			ret = 0;
		}
		if (test_bit(EXTENT_FLAG_COMPRESSED, &em->flags))
			flags |= FIEMAP_EXTENT_ENCODED;
		if (test_bit(EXTENT_FLAG_PREALLOC, &em->flags))
			flags |= FIEMAP_EXTENT_UNWRITTEN;

		free_extent_map(em);
		em = NULL;
		if ((em_start >= last) || em_len == (u64)-1 ||
		   (last == (u64)-1 && isize <= em_end)) {
			flags |= FIEMAP_EXTENT_LAST;
			end = 1;
		}

		/* now scan forward to see if this is really the last extent. */
		em = get_extent_skip_holes(inode, off, last_for_get_extent,
					   get_extent);
		if (IS_ERR(em)) {
			ret = PTR_ERR(em);
			goto out;
		}
		if (!em) {
			flags |= FIEMAP_EXTENT_LAST;
			end = 1;
		}
		ret = emit_fiemap_extent(fieinfo, &cache, em_start, disko,
					   em_len, flags);
		if (ret) {
			if (ret == 1)
				ret = 0;
			goto out_free;
		}
	}
out_free:
	if (!ret)
		ret = check_fiemap_cache(root->fs_info, fieinfo, &cache);
	free_extent_map(em);
out:
	btrfs_free_path(path);
	unlock_extent_cached(&BTRFS_I(inode)->io_tree, start, start + len - 1,
			     &cached_state, GFP_NOFS);
	return ret;
}
 */
static void btrfs_release_extent_buffer_page(struct extent_buffer *eb)
{
	unsigned long index;
	struct page *page;
	int mapped = !test_bit(EXTENT_BUFFER_DUMMY, &eb->bflags);

	BUG_ON(extent_buffer_under_io(eb));

	index = num_extent_pages(eb->start, eb->len);
	if (index == 0)
		return;

	do {
		index--;
		page = eb->pages[index];
		if (!page)
			continue;
		if (mapped)
			spin_lock(&page->mapping->private_lock);
		/*
		 * We do this since we'll remove the pages after we've
		 * removed the eb from the radix tree, so we could race
		 * and have this page now attached to the new eb.  So
		 * only clear page_private if it's still connected to
		 * this eb.
		 */
		if (PagePrivate(page) &&
		    page->private == (unsigned long)eb) {
			BUG_ON(test_bit(EXTENT_BUFFER_DIRTY, &eb->bflags));
			BUG_ON(PageDirty(page));
			BUG_ON(PageWriteback(page));
			/*
			 * We need to make sure we haven't be attached
			 * to a new eb.
			 */
			ClearPagePrivate(page);
			set_page_private(page, 0);
			/* One for the page private */
			put_page(page);
		}

		if (mapped)
			spin_unlock(&page->mapping->private_lock);

		/* One for when we allocated the page */
		put_page(page);
	} while (index != 0);
}

struct extent_buffer *btrfs_clone_extent_buffer(struct extent_buffer *src)
{
	unsigned long i;
	struct page *p;
	struct extent_buffer *new;
	unsigned long num_pages = num_extent_pages(src->start, src->len);

	new = __alloc_extent_buffer(src->fs_info, src->start, src->len);
	if (new == NULL)
		return NULL;

	for (i = 0; i < num_pages; i++) {
		p = alloc_page(GFP_NOFS);
		if (!p) {
			btrfs_release_extent_buffer(new);
			return NULL;
		}
		attach_extent_buffer_page(new, p);
		WARN_ON(PageDirty(p));
		SetPageUptodate(p);
		new->pages[i] = p;
		copy_page(page_address(p), page_address(src->pages[i]));
	}

	set_bit(EXTENT_BUFFER_UPTODATE, &new->bflags);
	set_bit(EXTENT_BUFFER_DUMMY, &new->bflags);

	return new;
}
struct extent_buffer *__alloc_dummy_extent_buffer(struct btrfs_fs_info *fs_info,
						  u64 start, unsigned long len)
{
	struct extent_buffer *eb;
	unsigned long num_pages;
	unsigned long i;

	num_pages = num_extent_pages(start, len);

	eb = __alloc_extent_buffer(fs_info, start, len);
	if (!eb)
		return NULL;

	for (i = 0; i < num_pages; i++) {
		eb->pages[i] = alloc_page(GFP_NOFS);
		if (!eb->pages[i])
			goto err;
	}
	set_extent_buffer_uptodate(eb);
	btrfs_set_header_nritems(eb, 0);
	set_bit(EXTENT_BUFFER_DUMMY, &eb->bflags);

	return eb;
err:
	for (; i > 0; i--)
		__free_page(eb->pages[i - 1]);
	__free_extent_buffer(eb);
	return NULL;
}
static void mark_extent_buffer_accessed(struct extent_buffer *eb,
		struct page *accessed)
{
	unsigned long num_pages, i;

	check_buffer_tree_ref(eb);

	num_pages = num_extent_pages(eb->start, eb->len);
	for (i = 0; i < num_pages; i++) {
		struct page *p = eb->pages[i];

		if (p != accessed)
			mark_page_accessed(p);
	}
}
struct extent_buffer *alloc_extent_buffer(struct btrfs_fs_info *fs_info,
					  u64 start)
{
	unsigned long len = fs_info->nodesize;
	unsigned long num_pages = num_extent_pages(start, len);
	unsigned long i;
	unsigned long index = start >> PAGE_SHIFT;
	struct extent_buffer *eb;
	struct extent_buffer *exists = NULL;
	struct page *p;
	struct address_space *mapping = fs_info->btree_inode->i_mapping;
	int uptodate = 1;
	int ret;

	if (!IS_ALIGNED(start, fs_info->sectorsize)) {
		btrfs_err(fs_info, "bad tree block start %llu", start);
		return ERR_PTR(-EINVAL);
	}

	eb = find_extent_buffer(fs_info, start);
	if (eb)
		return eb;

	eb = __alloc_extent_buffer(fs_info, start, len);
	if (!eb)
		return ERR_PTR(-ENOMEM);

	for (i = 0; i < num_pages; i++, index++) {
		p = find_or_create_page(mapping, index, GFP_NOFS|__GFP_NOFAIL);
		if (!p) {
			exists = ERR_PTR(-ENOMEM);
			goto free_eb;
		}

		spin_lock(&mapping->private_lock);
		if (PagePrivate(p)) {
			/*
			 * We could have already allocated an eb for this page
			 * and attached one so lets see if we can get a ref on
			 * the existing eb, and if we can we know it's good and
			 * we can just return that one, else we know we can just
			 * overwrite page->private.
			 */
			exists = (struct extent_buffer *)p->private;
			if (atomic_inc_not_zero(&exists->refs)) {
				spin_unlock(&mapping->private_lock);
				unlock_page(p);
				put_page(p);
				mark_extent_buffer_accessed(exists, p);
				goto free_eb;
			}
			exists = NULL;

			/*
			 * Do this so attach doesn't complain and we need to
			 * drop the ref the old guy had.
			 */
			ClearPagePrivate(p);
			WARN_ON(PageDirty(p));
			put_page(p);
		}
		attach_extent_buffer_page(eb, p);
		spin_unlock(&mapping->private_lock);
		WARN_ON(PageDirty(p));
		eb->pages[i] = p;
		if (!PageUptodate(p))
			uptodate = 0;

		/*
		 * see below about how we avoid a nasty race with release page
		 * and why we unlock later
		 */
	}
	if (uptodate)
		set_bit(EXTENT_BUFFER_UPTODATE, &eb->bflags);
again:
	ret = radix_tree_preload(GFP_NOFS);
	if (ret) {
		exists = ERR_PTR(ret);
		goto free_eb;
	}

	spin_lock(&fs_info->buffer_lock);
	ret = radix_tree_insert(&fs_info->buffer_radix,
				start >> PAGE_SHIFT, eb);
	spin_unlock(&fs_info->buffer_lock);
	radix_tree_preload_end();
	if (ret == -EEXIST) {
		exists = find_extent_buffer(fs_info, start);
		if (exists)
			goto free_eb;
		else
			goto again;
	}
	/* add one reference for the tree */
	check_buffer_tree_ref(eb);
	set_bit(EXTENT_BUFFER_IN_TREE, &eb->bflags);

	/*
	 * there is a race where release page may have
	 * tried to find this extent buffer in the radix
	 * but failed.  It will tell the VM it is safe to
	 * reclaim the, and it will clear the page private bit.
	 * We must make sure to set the page private bit properly
	 * after the extent buffer is in the radix tree so
	 * it doesn't get lost
	 */
	SetPageChecked(eb->pages[0]);
	for (i = 1; i < num_pages; i++) {
		p = eb->pages[i];
		ClearPageChecked(p);
		unlock_page(p);
	}
	unlock_page(eb->pages[0]);
	return eb;

free_eb:
	WARN_ON(!atomic_dec_and_test(&eb->refs));
	for (i = 0; i < num_pages; i++) {
		if (eb->pages[i])
			unlock_page(eb->pages[i]);
	}

	btrfs_release_extent_buffer(eb);
	return exists;
}

void free_extent_buffer(struct extent_buffer *eb)
{
	int refs;
	int old;
	if (!eb)
		return;

	while (1) {
		refs = atomic_read(&eb->refs);
		if (refs <= 3)
			break;
		old = atomic_cmpxchg(&eb->refs, refs, refs - 1);
		if (old == refs)
			return;
	}

	spin_lock(&eb->refs_lock);
	if (atomic_read(&eb->refs) == 2 &&
	    test_bit(EXTENT_BUFFER_DUMMY, &eb->bflags))
		atomic_dec(&eb->refs);

	if (atomic_read(&eb->refs) == 2 &&
	    test_bit(EXTENT_BUFFER_STALE, &eb->bflags) &&
	    !extent_buffer_under_io(eb) &&
	    test_and_clear_bit(EXTENT_BUFFER_TREE_REF, &eb->bflags))
		atomic_dec(&eb->refs);

	/*
	 * I know this is terrible, but it's temporary until we stop tracking
	 * the uptodate bits and such for the extent buffers.
	 */
	release_extent_buffer(eb);
}

void clear_extent_buffer_dirty(struct extent_buffer *eb)
{
	unsigned long i;
	unsigned long num_pages;
	struct page *page;

	num_pages = num_extent_pages(eb->start, eb->len);

	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		if (!PageDirty(page))
			continue;

		lock_page(page);
		WARN_ON(!PagePrivate(page));

		clear_page_dirty_for_io(page);
		spin_lock_irq(&page->mapping->tree_lock);
		if (!PageDirty(page)) {
			radix_tree_tag_clear(&page->mapping->page_tree,
						page_index(page),
						PAGECACHE_TAG_DIRTY);
		}
		spin_unlock_irq(&page->mapping->tree_lock);
		ClearPageError(page);
		unlock_page(page);
	}
	WARN_ON(atomic_read(&eb->refs) == 0);
}

int set_extent_buffer_dirty(struct extent_buffer *eb)
{
	unsigned long i;
	unsigned long num_pages;
	int was_dirty = 0;

	check_buffer_tree_ref(eb);

	was_dirty = test_and_set_bit(EXTENT_BUFFER_DIRTY, &eb->bflags);

	num_pages = num_extent_pages(eb->start, eb->len);
	WARN_ON(atomic_read(&eb->refs) == 0);
	WARN_ON(!test_bit(EXTENT_BUFFER_TREE_REF, &eb->bflags));

	for (i = 0; i < num_pages; i++)
		set_page_dirty(eb->pages[i]);
	return was_dirty;
}

void clear_extent_buffer_uptodate(struct extent_buffer *eb)
{
	unsigned long i;
	struct page *page;
	unsigned long num_pages;

	clear_bit(EXTENT_BUFFER_UPTODATE, &eb->bflags);
	num_pages = num_extent_pages(eb->start, eb->len);
	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		if (page)
			ClearPageUptodate(page);
	}
}

void set_extent_buffer_uptodate(struct extent_buffer *eb)
{
	unsigned long i;
	struct page *page;
	unsigned long num_pages;

	set_bit(EXTENT_BUFFER_UPTODATE, &eb->bflags);
	num_pages = num_extent_pages(eb->start, eb->len);
	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		SetPageUptodate(page);
	}
}
			     struct extent_buffer *eb, int wait,
			     get_extent_t *get_extent, int mirror_num)
{
	unsigned long i;
	struct page *page;
	int err;
	int ret = 0;
	int locked_pages = 0;
	int all_uptodate = 1;
	unsigned long num_pages;
	unsigned long num_reads = 0;
	struct bio *bio = NULL;
	unsigned long bio_flags = 0;

	if (test_bit(EXTENT_BUFFER_UPTODATE, &eb->bflags))
		return 0;

	num_pages = num_extent_pages(eb->start, eb->len);
	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		if (wait == WAIT_NONE) {
			if (!trylock_page(page))
				goto unlock_exit;
		} else {
			lock_page(page);
		}
		locked_pages++;
	}
	/*
	 * We need to firstly lock all pages to make sure that
	 * the uptodate bit of our pages won't be affected by
	 * clear_extent_buffer_uptodate().
	 */
	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		if (!PageUptodate(page)) {
			num_reads++;
			all_uptodate = 0;
		}
	}

	if (all_uptodate) {
		set_bit(EXTENT_BUFFER_UPTODATE, &eb->bflags);
		goto unlock_exit;
	}

	clear_bit(EXTENT_BUFFER_READ_ERR, &eb->bflags);
	eb->read_mirror = 0;
	atomic_set(&eb->io_pages, num_reads);
	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];

		if (!PageUptodate(page)) {
			if (ret) {
				atomic_dec(&eb->io_pages);
				unlock_page(page);
				continue;
			}

			ClearPageError(page);
			err = __extent_read_full_page(tree, page,
						      get_extent, &bio,
						      mirror_num, &bio_flags,
						      REQ_META);
			if (err) {
				ret = err;
				/*
				 * We use &bio in above __extent_read_full_page,
				 * so we ensure that if it returns error, the
				 * current page fails to add itself to bio and
				 * it's been unlocked.
				 *
				 * We must dec io_pages by ourselves.
				 */
				atomic_dec(&eb->io_pages);
			}
		} else {
			unlock_page(page);
		}
	}

	if (bio) {
		err = submit_one_bio(bio, mirror_num, bio_flags);
		if (err)
			return err;
	}

	if (ret || wait != WAIT_COMPLETE)
		return ret;

	for (i = 0; i < num_pages; i++) {
		page = eb->pages[i];
		wait_on_page_locked(page);
		if (!PageUptodate(page))
			ret = -EIO;
	}

	return ret;

unlock_exit:
	while (locked_pages > 0) {
		locked_pages--;
		page = eb->pages[locked_pages];
		unlock_page(page);
	}
	return ret;
}
			unsigned long start,
			unsigned long len)
{
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	char *dst = (char *)dstv;
	size_t start_offset = eb->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + start) >> PAGE_SHIFT;

	WARN_ON(start > eb->len);
	WARN_ON(start + len > eb->start + eb->len);

	offset = (start_offset + start) & (PAGE_SIZE - 1);

	while (len > 0) {
		page = eb->pages[i];

		cur = min(len, (PAGE_SIZE - offset));
		kaddr = page_address(page);
		memcpy(dst, kaddr + offset, cur);

		dst += cur;
		len -= cur;
		offset = 0;
		i++;
	}
}
			unsigned long start,
			unsigned long len)
{
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	char __user *dst = (char __user *)dstv;
	size_t start_offset = eb->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + start) >> PAGE_SHIFT;
	int ret = 0;

	WARN_ON(start > eb->len);
	WARN_ON(start + len > eb->start + eb->len);

	offset = (start_offset + start) & (PAGE_SIZE - 1);

	while (len > 0) {
		page = eb->pages[i];

		cur = min(len, (PAGE_SIZE - offset));
		kaddr = page_address(page);
		if (copy_to_user(dst, kaddr + offset, cur)) {
			ret = -EFAULT;
			break;
		}

		dst += cur;
		len -= cur;
		offset = 0;
		i++;
	}

	return ret;
}
			  unsigned long start,
			  unsigned long len)
{
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	char *ptr = (char *)ptrv;
	size_t start_offset = eb->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + start) >> PAGE_SHIFT;
	int ret = 0;

	WARN_ON(start > eb->len);
	WARN_ON(start + len > eb->start + eb->len);

	offset = (start_offset + start) & (PAGE_SIZE - 1);

	while (len > 0) {
		page = eb->pages[i];

		cur = min(len, (PAGE_SIZE - offset));

		kaddr = page_address(page);
		ret = memcmp(ptr, kaddr + offset, cur);
		if (ret)
			break;

		ptr += cur;
		len -= cur;
		offset = 0;
		i++;
	}
	return ret;
}
void write_extent_buffer(struct extent_buffer *eb, const void *srcv,
			 unsigned long start, unsigned long len)
{
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	char *src = (char *)srcv;
	size_t start_offset = eb->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + start) >> PAGE_SHIFT;

	WARN_ON(start > eb->len);
	WARN_ON(start + len > eb->start + eb->len);

	offset = (start_offset + start) & (PAGE_SIZE - 1);

	while (len > 0) {
		page = eb->pages[i];
		WARN_ON(!PageUptodate(page));

		cur = min(len, PAGE_SIZE - offset);
		kaddr = page_address(page);
		memcpy(kaddr + offset, src, cur);

		src += cur;
		len -= cur;
		offset = 0;
		i++;
	}
}
void memzero_extent_buffer(struct extent_buffer *eb, unsigned long start,
		unsigned long len)
{
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	size_t start_offset = eb->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + start) >> PAGE_SHIFT;

	WARN_ON(start > eb->len);
	WARN_ON(start + len > eb->start + eb->len);

	offset = (start_offset + start) & (PAGE_SIZE - 1);

	while (len > 0) {
		page = eb->pages[i];
		WARN_ON(!PageUptodate(page));

		cur = min(len, PAGE_SIZE - offset);
		kaddr = page_address(page);
		memset(kaddr + offset, 0, cur);

		len -= cur;
		offset = 0;
		i++;
	}
}
void copy_extent_buffer_full(struct extent_buffer *dst,
			     struct extent_buffer *src)
{
	int i;
	unsigned num_pages;

	ASSERT(dst->len == src->len);

	num_pages = num_extent_pages(dst->start, dst->len);
	for (i = 0; i < num_pages; i++)
		copy_page(page_address(dst->pages[i]),
				page_address(src->pages[i]));
}
			unsigned long dst_offset, unsigned long src_offset,
			unsigned long len)
{
	u64 dst_len = dst->len;
	size_t cur;
	size_t offset;
	struct page *page;
	char *kaddr;
	size_t start_offset = dst->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + dst_offset) >> PAGE_SHIFT;

	WARN_ON(src->len != dst_len);

	offset = (start_offset + dst_offset) &
		(PAGE_SIZE - 1);

	while (len > 0) {
		page = dst->pages[i];
		WARN_ON(!PageUptodate(page));

		cur = min(len, (unsigned long)(PAGE_SIZE - offset));

		kaddr = page_address(page);
		read_extent_buffer(src, kaddr + offset, src_offset, cur);

		src_offset += cur;
		len -= cur;
		offset = 0;
		i++;
	}
}

void le_bitmap_set(u8 *map, unsigned int start, int len)
{
	u8 *p = map + BIT_BYTE(start);
	const unsigned int size = start + len;
	int bits_to_set = BITS_PER_BYTE - (start % BITS_PER_BYTE);
	u8 mask_to_set = BITMAP_FIRST_BYTE_MASK(start);

	while (len - bits_to_set >= 0) {
		*p |= mask_to_set;
		len -= bits_to_set;
		bits_to_set = BITS_PER_BYTE;
		mask_to_set = ~0;
		p++;
	}
	if (len) {
		mask_to_set &= BITMAP_LAST_BYTE_MASK(size);
		*p |= mask_to_set;
	}
}

void le_bitmap_clear(u8 *map, unsigned int start, int len)
{
	u8 *p = map + BIT_BYTE(start);
	const unsigned int size = start + len;
	int bits_to_clear = BITS_PER_BYTE - (start % BITS_PER_BYTE);
	u8 mask_to_clear = BITMAP_FIRST_BYTE_MASK(start);

	while (len - bits_to_clear >= 0) {
		*p &= ~mask_to_clear;
		len -= bits_to_clear;
		bits_to_clear = BITS_PER_BYTE;
		mask_to_clear = ~0;
		p++;
	}
	if (len) {
		mask_to_clear &= BITMAP_LAST_BYTE_MASK(size);
		*p &= ~mask_to_clear;
	}
}
void extent_buffer_bitmap_set(struct extent_buffer *eb, unsigned long start,
			      unsigned long pos, unsigned long len)
{
	u8 *kaddr;
	struct page *page;
	unsigned long i;
	size_t offset;
	const unsigned int size = pos + len;
	int bits_to_set = BITS_PER_BYTE - (pos % BITS_PER_BYTE);
	u8 mask_to_set = BITMAP_FIRST_BYTE_MASK(pos);

	eb_bitmap_offset(eb, start, pos, &i, &offset);
	page = eb->pages[i];
	WARN_ON(!PageUptodate(page));
	kaddr = page_address(page);

	while (len >= bits_to_set) {
		kaddr[offset] |= mask_to_set;
		len -= bits_to_set;
		bits_to_set = BITS_PER_BYTE;
		mask_to_set = ~0;
		if (++offset >= PAGE_SIZE && len > 0) {
			offset = 0;
			page = eb->pages[++i];
			WARN_ON(!PageUptodate(page));
			kaddr = page_address(page);
		}
	}
	if (len) {
		mask_to_set &= BITMAP_LAST_BYTE_MASK(size);
		kaddr[offset] |= mask_to_set;
	}
}
void extent_buffer_bitmap_clear(struct extent_buffer *eb, unsigned long start,
				unsigned long pos, unsigned long len)
{
	u8 *kaddr;
	struct page *page;
	unsigned long i;
	size_t offset;
	const unsigned int size = pos + len;
	int bits_to_clear = BITS_PER_BYTE - (pos % BITS_PER_BYTE);
	u8 mask_to_clear = BITMAP_FIRST_BYTE_MASK(pos);

	eb_bitmap_offset(eb, start, pos, &i, &offset);
	page = eb->pages[i];
	WARN_ON(!PageUptodate(page));
	kaddr = page_address(page);

	while (len >= bits_to_clear) {
		kaddr[offset] &= ~mask_to_clear;
		len -= bits_to_clear;
		bits_to_clear = BITS_PER_BYTE;
		mask_to_clear = ~0;
		if (++offset >= PAGE_SIZE && len > 0) {
			offset = 0;
			page = eb->pages[++i];
			WARN_ON(!PageUptodate(page));
			kaddr = page_address(page);
		}
	}
	if (len) {
		mask_to_clear &= BITMAP_LAST_BYTE_MASK(size);
		kaddr[offset] &= ~mask_to_clear;
	}
}
void memcpy_extent_buffer(struct extent_buffer *dst, unsigned long dst_offset,
			   unsigned long src_offset, unsigned long len)
{
	struct btrfs_fs_info *fs_info = dst->fs_info;
	size_t cur;
	size_t dst_off_in_page;
	size_t src_off_in_page;
	size_t start_offset = dst->start & ((u64)PAGE_SIZE - 1);
	unsigned long dst_i;
	unsigned long src_i;

	if (src_offset + len > dst->len) {
		btrfs_err(fs_info,
			"memmove bogus src_offset %lu move len %lu dst len %lu",
			 src_offset, len, dst->len);
		BUG_ON(1);
	}
	if (dst_offset + len > dst->len) {
		btrfs_err(fs_info,
			"memmove bogus dst_offset %lu move len %lu dst len %lu",
			 dst_offset, len, dst->len);
		BUG_ON(1);
	}

	while (len > 0) {
		dst_off_in_page = (start_offset + dst_offset) &
			(PAGE_SIZE - 1);
		src_off_in_page = (start_offset + src_offset) &
			(PAGE_SIZE - 1);

		dst_i = (start_offset + dst_offset) >> PAGE_SHIFT;
		src_i = (start_offset + src_offset) >> PAGE_SHIFT;

		cur = min(len, (unsigned long)(PAGE_SIZE -
					       src_off_in_page));
		cur = min_t(unsigned long, cur,
			(unsigned long)(PAGE_SIZE - dst_off_in_page));

		copy_pages(dst->pages[dst_i], dst->pages[src_i],
			   dst_off_in_page, src_off_in_page, cur);

		src_offset += cur;
		dst_offset += cur;
		len -= cur;
	}
}
void memmove_extent_buffer(struct extent_buffer *dst, unsigned long dst_offset,
			   unsigned long src_offset, unsigned long len)
{
	struct btrfs_fs_info *fs_info = dst->fs_info;
	size_t cur;
	size_t dst_off_in_page;
	size_t src_off_in_page;
	unsigned long dst_end = dst_offset + len - 1;
	unsigned long src_end = src_offset + len - 1;
	size_t start_offset = dst->start & ((u64)PAGE_SIZE - 1);
	unsigned long dst_i;
	unsigned long src_i;

	if (src_offset + len > dst->len) {
		btrfs_err(fs_info,
			  "memmove bogus src_offset %lu move len %lu len %lu",
			  src_offset, len, dst->len);
		BUG_ON(1);
	}
	if (dst_offset + len > dst->len) {
		btrfs_err(fs_info,
			  "memmove bogus dst_offset %lu move len %lu len %lu",
			  dst_offset, len, dst->len);
		BUG_ON(1);
	}
	if (dst_offset < src_offset) {
		memcpy_extent_buffer(dst, dst_offset, src_offset, len);
		return;
	}
	while (len > 0) {
		dst_i = (start_offset + dst_end) >> PAGE_SHIFT;
		src_i = (start_offset + src_end) >> PAGE_SHIFT;

		dst_off_in_page = (start_offset + dst_end) &
			(PAGE_SIZE - 1);
		src_off_in_page = (start_offset + src_end) &
			(PAGE_SIZE - 1);

		cur = min_t(unsigned long, len, src_off_in_page + 1);
		cur = min(cur, dst_off_in_page + 1);
		copy_pages(dst->pages[dst_i], dst->pages[src_i],
			   dst_off_in_page - cur + 1,
			   src_off_in_page - cur + 1, cur);

		dst_end -= cur;
		src_end -= cur;
		len -= cur;
	}
}
