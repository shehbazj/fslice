				int compress_type,
				struct page **compressed_pages)
{
	struct extent_buffer *leaf;
	struct page *page = NULL;
	char *kaddr;
	unsigned long ptr;
	struct btrfs_file_extent_item *ei;
	int err = 0;
	int ret;
	size_t cur_size = size;
	unsigned long offset;

	if (compressed_size && compressed_pages)
		cur_size = compressed_size;

	inode_add_bytes(inode, size);

	if (!extent_inserted) {
		struct btrfs_key key;
		size_t datasize;

		key.objectid = btrfs_ino(BTRFS_I(inode));
		key.offset = start;
		key.type = BTRFS_EXTENT_DATA_KEY;

		datasize = btrfs_file_extent_calc_inline_size(cur_size);
		path->leave_spinning = 1;
		ret = btrfs_insert_empty_item(trans, root, path, &key,
					      datasize);
		if (ret) {
			err = ret;
			goto fail;
		}
	}
	leaf = path->nodes[0];
	ei = btrfs_item_ptr(leaf, path->slots[0],
			    struct btrfs_file_extent_item);
	btrfs_set_file_extent_generation(leaf, ei, trans->transid);
	btrfs_set_file_extent_type(leaf, ei, BTRFS_FILE_EXTENT_INLINE);
	btrfs_set_file_extent_encryption(leaf, ei, 0);
	btrfs_set_file_extent_other_encoding(leaf, ei, 0);
	btrfs_set_file_extent_ram_bytes(leaf, ei, size);
	ptr = btrfs_file_extent_inline_start(ei);

	if (compress_type != BTRFS_COMPRESS_NONE) {
		struct page *cpage;
		int i = 0;
		while (compressed_size > 0) {
			cpage = compressed_pages[i];
			cur_size = min_t(unsigned long, compressed_size,
				       PAGE_SIZE);

			kaddr = kmap_atomic(cpage);
			write_extent_buffer(leaf, kaddr, ptr, cur_size);
			kunmap_atomic(kaddr);

			i++;
			ptr += cur_size;
			compressed_size -= cur_size;
		}
		btrfs_set_file_extent_compression(leaf, ei,
						  compress_type);
	} else {
		page = find_get_page(inode->i_mapping,
				     start >> PAGE_SHIFT);
		btrfs_set_file_extent_compression(leaf, ei, 0);
		kaddr = kmap_atomic(page);
		offset = start & (PAGE_SIZE - 1);
		write_extent_buffer(leaf, kaddr + offset, ptr, size);
		kunmap_atomic(kaddr);
		put_page(page);
	}
	btrfs_mark_buffer_dirty(leaf);
	btrfs_release_path(path);

	/*
	 * we're an inline extent, so nobody can
	 * extend the file past i_size without locking
	 * a page we already have locked.
	 *
	 * We must do any isize and inode updates
	 * before we unlock the pages.  Otherwise we
	 * could end up racing with unlink.
	 */
	BTRFS_I(inode)->disk_i_size = inode->i_size;
	ret = btrfs_update_inode(trans, root, inode);

	return ret;
fail:
	return err;
}
					struct async_cow *async_cow,
					int *num_added)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	u64 num_bytes;
	u64 blocksize = fs_info->sectorsize;
	u64 actual_end;
	u64 isize = i_size_read(inode);
	int ret = 0;
	struct page **pages = NULL;
	unsigned long nr_pages;
	unsigned long total_compressed = 0;
	unsigned long total_in = 0;
	int i;
	int will_compress;
	int compress_type = fs_info->compress_type;
	int redirty = 0;

	inode_should_defrag(BTRFS_I(inode), start, end, end - start + 1,
			SZ_16K);

	actual_end = min_t(u64, isize, end + 1);
again:
	will_compress = 0;
	nr_pages = (end >> PAGE_SHIFT) - (start >> PAGE_SHIFT) + 1;
	BUILD_BUG_ON((BTRFS_MAX_COMPRESSED % PAGE_SIZE) != 0);
	nr_pages = min_t(unsigned long, nr_pages,
			BTRFS_MAX_COMPRESSED / PAGE_SIZE);

	/*
	 * we don't want to send crud past the end of i_size through
	 * compression, that's just a waste of CPU time.  So, if the
	 * end of the file is before the start of our current
	 * requested range of bytes, we bail out to the uncompressed
	 * cleanup code that can deal with all of this.
	 *
	 * It isn't really the fastest way to fix things, but this is a
	 * very uncommon corner.
	 */
	if (actual_end <= start)
		goto cleanup_and_bail_uncompressed;

	total_compressed = actual_end - start;

	/*
	 * skip compression for a small file range(<=blocksize) that
	 * isn't an inline extent, since it doesn't save disk space at all.
	 */
	if (total_compressed <= blocksize &&
	   (start > 0 || end + 1 < BTRFS_I(inode)->disk_i_size))
		goto cleanup_and_bail_uncompressed;

	total_compressed = min_t(unsigned long, total_compressed,
			BTRFS_MAX_UNCOMPRESSED);
	num_bytes = ALIGN(end - start + 1, blocksize);
	num_bytes = max(blocksize,  num_bytes);
	total_in = 0;
	ret = 0;

	/*
	 * we do compression for mount -o compress and when the
	 * inode has not been flagged as nocompress.  This flag can
	 * change at any time if we discover bad compression ratios.
	 */
	if (inode_need_compress(inode)) {
		WARN_ON(pages);
		pages = kcalloc(nr_pages, sizeof(struct page *), GFP_NOFS);
		if (!pages) {
			/* just bail out to the uncompressed code */
			goto cont;
		}

		if (BTRFS_I(inode)->force_compress)
			compress_type = BTRFS_I(inode)->force_compress;

		/*
		 * we need to call clear_page_dirty_for_io on each
		 * page in the range.  Otherwise applications with the file
		 * mmap'd can wander in and change the page contents while
		 * we are compressing them.
		 *
		 * If the compression fails for any reason, we set the pages
		 * dirty again later on.
		 */
		extent_range_clear_dirty_for_io(inode, start, end);
		redirty = 1;
		ret = btrfs_compress_pages(compress_type,
					   inode->i_mapping, start,
					   pages,
					   &nr_pages,
					   &total_in,
					   &total_compressed);

		if (!ret) {
			unsigned long offset = total_compressed &
				(PAGE_SIZE - 1);
			struct page *page = pages[nr_pages - 1];
			char *kaddr;

			/* zero the tail end of the last page, we might be
			 * sending it down to disk
			 */
			if (offset) {
				kaddr = kmap_atomic(page);
				memset(kaddr + offset, 0,
				       PAGE_SIZE - offset);
				kunmap_atomic(kaddr);
			}
			will_compress = 1;
		}
	}
cont:
	if (start == 0) {
		/* lets try to make an inline extent */
		if (ret || total_in < (actual_end - start)) {
			/* we didn't compress the entire range, try
			 * to make an uncompressed inline extent.
			 */
			ret = cow_file_range_inline(root, inode, start, end,
					    0, BTRFS_COMPRESS_NONE, NULL);
		} else {
			/* try making a compressed inline extent */
			ret = cow_file_range_inline(root, inode, start, end,
						    total_compressed,
						    compress_type, pages);
		}
		if (ret <= 0) {
			unsigned long clear_flags = EXTENT_DELALLOC |
				EXTENT_DELALLOC_NEW | EXTENT_DEFRAG;
			unsigned long page_error_op;

			clear_flags |= (ret < 0) ? EXTENT_DO_ACCOUNTING : 0;
			page_error_op = ret < 0 ? PAGE_SET_ERROR : 0;

			/*
			 * inline extent creation worked or returned error,
			 * we don't need to create any more async work items.
			 * Unlock and free up our temp pages.
			 */
			extent_clear_unlock_delalloc(inode, start, end, end,
						     NULL, clear_flags,
						     PAGE_UNLOCK |
						     PAGE_CLEAR_DIRTY |
						     PAGE_SET_WRITEBACK |
						     page_error_op |
						     PAGE_END_WRITEBACK);
			if (ret == 0)
				btrfs_free_reserved_data_space_noquota(inode,
							       start,
							       end - start + 1);
			goto free_pages_out;
		}
	}

	if (will_compress) {
		/*
		 * we aren't doing an inline extent round the compressed size
		 * up to a block size boundary so the allocator does sane
		 * things
		 */
		total_compressed = ALIGN(total_compressed, blocksize);

		/*
		 * one last check to make sure the compression is really a
		 * win, compare the page count read with the blocks on disk
		 */
		total_in = ALIGN(total_in, PAGE_SIZE);
		if (total_compressed >= total_in) {
			will_compress = 0;
		} else {
			num_bytes = total_in;
			*num_added += 1;

			/*
			 * The async work queues will take care of doing actual
			 * allocation on disk for these compressed pages, and
			 * will submit them to the elevator.
			 */
			add_async_extent(async_cow, start, num_bytes,
					total_compressed, pages, nr_pages,
					compress_type);

			if (start + num_bytes < end) {
				start += num_bytes;
				pages = NULL;
				cond_resched();
				goto again;
			}
			return;
		}
	}
	if (pages) {
		/*
		 * the compression code ran but failed to make things smaller,
		 * free any pages it allocated and our page pointer array
		 */
		for (i = 0; i < nr_pages; i++) {
			WARN_ON(pages[i]->mapping);
			put_page(pages[i]);
		}
		kfree(pages);
		pages = NULL;
		total_compressed = 0;
		nr_pages = 0;

		/* flag the file so we don't compress in the future */
		if (!btrfs_test_opt(fs_info, FORCE_COMPRESS) &&
		    !(BTRFS_I(inode)->force_compress)) {
			BTRFS_I(inode)->flags |= BTRFS_INODE_NOCOMPRESS;
		}
	}
cleanup_and_bail_uncompressed:
	/*
	 * No compression, but we still need to write the pages in the file
	 * we've been given so far.  redirty the locked page if it corresponds
	 * to our extent and set things up for the async work queue to run
	 * cow_file_range to do the normal delalloc dance.
	 */
	if (page_offset(locked_page) >= start &&
	    page_offset(locked_page) <= end)
		__set_page_dirty_nobuffers(locked_page);
		/* unlocked later on in the async handlers */

	if (redirty)
		extent_range_redirty_for_io(inode, start, end);
	add_async_extent(async_cow, start, end - start + 1, 0, NULL, 0,
			 BTRFS_COMPRESS_NONE);
	*num_added += 1;

	return;

free_pages_out:
	for (i = 0; i < nr_pages; i++) {
		WARN_ON(pages[i]->mapping);
		put_page(pages[i]);
	}
	kfree(pages);
}

static void free_async_extent_pages(struct async_extent *async_extent)
{
	int i;

	if (!async_extent->pages)
		return;

	for (i = 0; i < async_extent->nr_pages; i++) {
		WARN_ON(async_extent->pages[i]->mapping);
		put_page(async_extent->pages[i]);
	}
	kfree(async_extent->pages);
	async_extent->nr_pages = 0;
	async_extent->pages = NULL;
}
static noinline void submit_compressed_extents(struct inode *inode,
					      struct async_cow *async_cow)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct async_extent *async_extent;
	u64 alloc_hint = 0;
	struct btrfs_key ins;
	struct extent_map *em;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct extent_io_tree *io_tree;
	int ret = 0;

again:
	while (!list_empty(&async_cow->extents)) {
		async_extent = list_entry(async_cow->extents.next,
					  struct async_extent, list);
		list_del(&async_extent->list);

		io_tree = &BTRFS_I(inode)->io_tree;

retry:
		/* did the compression code fall back to uncompressed IO? */
		if (!async_extent->pages) {
			int page_started = 0;
			unsigned long nr_written = 0;

			lock_extent(io_tree, async_extent->start,
					 async_extent->start +
					 async_extent->ram_size - 1);

			/* allocate blocks */
			ret = cow_file_range(inode, async_cow->locked_page,
					     async_extent->start,
					     async_extent->start +
					     async_extent->ram_size - 1,
					     async_extent->start +
					     async_extent->ram_size - 1,
					     &page_started, &nr_written, 0,
					     NULL);

			/* JDM XXX */

			/*
			 * if page_started, cow_file_range inserted an
			 * inline extent and took care of all the unlocking
			 * and IO for us.  Otherwise, we need to submit
			 * all those pages down to the drive.
			 */
			if (!page_started && !ret)
				extent_write_locked_range(io_tree,
						  inode, async_extent->start,
						  async_extent->start +
						  async_extent->ram_size - 1,
						  btrfs_get_extent,
						  WB_SYNC_ALL);
			else if (ret)
				unlock_page(async_cow->locked_page);
			kfree(async_extent);
			cond_resched();
			continue;
		}

		lock_extent(io_tree, async_extent->start,
			    async_extent->start + async_extent->ram_size - 1);

		ret = btrfs_reserve_extent(root, async_extent->ram_size,
					   async_extent->compressed_size,
					   async_extent->compressed_size,
					   0, alloc_hint, &ins, 1, 1);
		if (ret) {
			free_async_extent_pages(async_extent);

			if (ret == -ENOSPC) {
				unlock_extent(io_tree, async_extent->start,
					      async_extent->start +
					      async_extent->ram_size - 1);

				/*
				 * we need to redirty the pages if we decide to
				 * fallback to uncompressed IO, otherwise we
				 * will not submit these pages down to lower
				 * layers.
				 */
				extent_range_redirty_for_io(inode,
						async_extent->start,
						async_extent->start +
						async_extent->ram_size - 1);

				goto retry;
			}
			goto out_free;
		}
		/*
		 * here we're doing allocation and writeback of the
		 * compressed pages
		 */
		em = create_io_em(inode, async_extent->start,
				  async_extent->ram_size, /* len */
				  async_extent->start, /* orig_start */
				  ins.objectid, /* block_start */
				  ins.offset, /* block_len */
				  ins.offset, /* orig_block_len */
				  async_extent->ram_size, /* ram_bytes */
				  async_extent->compress_type,
				  BTRFS_ORDERED_COMPRESSED);
		if (IS_ERR(em))
			/* ret value is not necessary due to void function */
			goto out_free_reserve;
		free_extent_map(em);

		ret = btrfs_add_ordered_extent_compress(inode,
						async_extent->start,
						ins.objectid,
						async_extent->ram_size,
						ins.offset,
						BTRFS_ORDERED_COMPRESSED,
						async_extent->compress_type);
		if (ret) {
			btrfs_drop_extent_cache(BTRFS_I(inode),
						async_extent->start,
						async_extent->start +
						async_extent->ram_size - 1, 0);
			goto out_free_reserve;
		}
		btrfs_dec_block_group_reservations(fs_info, ins.objectid);

		/*
		 * clear dirty, set writeback and unlock the pages.
		 */
		extent_clear_unlock_delalloc(inode, async_extent->start,
				async_extent->start +
				async_extent->ram_size - 1,
				async_extent->start +
				async_extent->ram_size - 1,
				NULL, EXTENT_LOCKED | EXTENT_DELALLOC,
				PAGE_UNLOCK | PAGE_CLEAR_DIRTY |
				PAGE_SET_WRITEBACK);
		ret = btrfs_submit_compressed_write(inode,
				    async_extent->start,
				    async_extent->ram_size,
				    ins.objectid,
				    ins.offset, async_extent->pages,
				    async_extent->nr_pages);
		if (ret) {
			struct extent_io_tree *tree = &BTRFS_I(inode)->io_tree;
			struct page *p = async_extent->pages[0];
			const u64 start = async_extent->start;
			const u64 end = start + async_extent->ram_size - 1;

			p->mapping = inode->i_mapping;
			tree->ops->writepage_end_io_hook(p, start, end,
							 NULL, 0);
			p->mapping = NULL;
			extent_clear_unlock_delalloc(inode, start, end, end,
						     NULL, 0,
						     PAGE_END_WRITEBACK |
						     PAGE_SET_ERROR);
			free_async_extent_pages(async_extent);
		}
		alloc_hint = ins.objectid + ins.offset;
		kfree(async_extent);
		cond_resched();
	}
	return;
out_free_reserve:
	btrfs_dec_block_group_reservations(fs_info, ins.objectid);
	btrfs_free_reserved_extent(fs_info, ins.objectid, ins.offset, 1);
out_free:
	extent_clear_unlock_delalloc(inode, async_extent->start,
				     async_extent->start +
				     async_extent->ram_size - 1,
				     async_extent->start +
				     async_extent->ram_size - 1,
				     NULL, EXTENT_LOCKED | EXTENT_DELALLOC |
				     EXTENT_DELALLOC_NEW |
				     EXTENT_DEFRAG | EXTENT_DO_ACCOUNTING,
				     PAGE_UNLOCK | PAGE_CLEAR_DIRTY |
				     PAGE_SET_WRITEBACK | PAGE_END_WRITEBACK |
				     PAGE_SET_ERROR);
	free_async_extent_pages(async_extent);
	kfree(async_extent);
	goto again;
}
				   int *page_started, unsigned long *nr_written,
				   int unlock, struct btrfs_dedupe_hash *hash)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	u64 alloc_hint = 0;
	u64 num_bytes;
	unsigned long ram_size;
	u64 disk_num_bytes;
	u64 cur_alloc_size = 0;
	u64 blocksize = fs_info->sectorsize;
	struct btrfs_key ins;
	struct extent_map *em;
	unsigned clear_bits;
	unsigned long page_ops;
	bool extent_reserved = false;
	int ret = 0;

	if (btrfs_is_free_space_inode(BTRFS_I(inode))) {
		WARN_ON_ONCE(1);
		ret = -EINVAL;
		goto out_unlock;
	}

	num_bytes = ALIGN(end - start + 1, blocksize);
	num_bytes = max(blocksize,  num_bytes);
	disk_num_bytes = num_bytes;

	inode_should_defrag(BTRFS_I(inode), start, end, num_bytes, SZ_64K);

	if (start == 0) {
		/* lets try to make an inline extent */
		ret = cow_file_range_inline(root, inode, start, end, 0,
					BTRFS_COMPRESS_NONE, NULL);
		if (ret == 0) {
			extent_clear_unlock_delalloc(inode, start, end,
				     delalloc_end, NULL,
				     EXTENT_LOCKED | EXTENT_DELALLOC |
				     EXTENT_DELALLOC_NEW |
				     EXTENT_DEFRAG, PAGE_UNLOCK |
				     PAGE_CLEAR_DIRTY | PAGE_SET_WRITEBACK |
				     PAGE_END_WRITEBACK);
			btrfs_free_reserved_data_space_noquota(inode, start,
						end - start + 1);
			*nr_written = *nr_written +
			     (end - start + PAGE_SIZE) / PAGE_SIZE;
			*page_started = 1;
			goto out;
		} else if (ret < 0) {
			goto out_unlock;
		}
	}

	BUG_ON(disk_num_bytes >
	       btrfs_super_total_bytes(fs_info->super_copy));

	alloc_hint = get_extent_allocation_hint(inode, start, num_bytes);
	btrfs_drop_extent_cache(BTRFS_I(inode), start,
			start + num_bytes - 1, 0);

	while (disk_num_bytes > 0) {
		cur_alloc_size = disk_num_bytes;
		ret = btrfs_reserve_extent(root, cur_alloc_size, cur_alloc_size,
					   fs_info->sectorsize, 0, alloc_hint,
					   &ins, 1, 1);
		if (ret < 0)
			goto out_unlock;
		cur_alloc_size = ins.offset;
		extent_reserved = true;

		ram_size = ins.offset;
		em = create_io_em(inode, start, ins.offset, /* len */
				  start, /* orig_start */
				  ins.objectid, /* block_start */
				  ins.offset, /* block_len */
				  ins.offset, /* orig_block_len */
				  ram_size, /* ram_bytes */
				  BTRFS_COMPRESS_NONE, /* compress_type */
				  BTRFS_ORDERED_REGULAR /* type */);
		if (IS_ERR(em))
			goto out_reserve;
		free_extent_map(em);

		ret = btrfs_add_ordered_extent(inode, start, ins.objectid,
					       ram_size, cur_alloc_size, 0);
		if (ret)
			goto out_drop_extent_cache;

		if (root->root_key.objectid ==
		    BTRFS_DATA_RELOC_TREE_OBJECTID) {
			ret = btrfs_reloc_clone_csums(inode, start,
						      cur_alloc_size);
			/*
			 * Only drop cache here, and process as normal.
			 *
			 * We must not allow extent_clear_unlock_delalloc()
			 * at out_unlock label to free meta of this ordered
			 * extent, as its meta should be freed by
			 * btrfs_finish_ordered_io().
			 *
			 * So we must continue until @start is increased to
			 * skip current ordered extent.
			 */
			if (ret)
				btrfs_drop_extent_cache(BTRFS_I(inode), start,
						start + ram_size - 1, 0);
		}

		btrfs_dec_block_group_reservations(fs_info, ins.objectid);

		/* we're not doing compressed IO, don't unlock the first
		 * page (which the caller expects to stay locked), don't
		 * clear any dirty bits and don't set any writeback bits
		 *
		 * Do set the Private2 bit so we know this page was properly
		 * setup for writepage
		 */
		page_ops = unlock ? PAGE_UNLOCK : 0;
		page_ops |= PAGE_SET_PRIVATE2;

		extent_clear_unlock_delalloc(inode, start,
					     start + ram_size - 1,
					     delalloc_end, locked_page,
					     EXTENT_LOCKED | EXTENT_DELALLOC,
					     page_ops);
		if (disk_num_bytes < cur_alloc_size)
			disk_num_bytes = 0;
		else
			disk_num_bytes -= cur_alloc_size;
		num_bytes -= cur_alloc_size;
		alloc_hint = ins.objectid + ins.offset;
		start += cur_alloc_size;
		extent_reserved = false;

		/*
		 * btrfs_reloc_clone_csums() error, since start is increased
		 * extent_clear_unlock_delalloc() at out_unlock label won't
		 * free metadata of current ordered extent, we're OK to exit.
		 */
		if (ret)
			goto out_unlock;
	}
out:
	return ret;

out_drop_extent_cache:
	btrfs_drop_extent_cache(BTRFS_I(inode), start, start + ram_size - 1, 0);
out_reserve:
	btrfs_dec_block_group_reservations(fs_info, ins.objectid);
	btrfs_free_reserved_extent(fs_info, ins.objectid, ins.offset, 1);
out_unlock:
	clear_bits = EXTENT_LOCKED | EXTENT_DELALLOC | EXTENT_DELALLOC_NEW |
		EXTENT_DEFRAG | EXTENT_CLEAR_META_RESV;
	page_ops = PAGE_UNLOCK | PAGE_CLEAR_DIRTY | PAGE_SET_WRITEBACK |
		PAGE_END_WRITEBACK;
	/*
	 * If we reserved an extent for our delalloc range (or a subrange) and
	 * failed to create the respective ordered extent, then it means that
	 * when we reserved the extent we decremented the extent's size from
	 * the data space_info's bytes_may_use counter and incremented the
	 * space_info's bytes_reserved counter by the same amount. We must make
	 * sure extent_clear_unlock_delalloc() does not try to decrement again
	 * the data space_info's bytes_may_use counter, therefore we do not pass
	 * it the flag EXTENT_CLEAR_DATA_RESV.
	 */
	if (extent_reserved) {
		extent_clear_unlock_delalloc(inode, start,
					     start + cur_alloc_size,
					     start + cur_alloc_size,
					     locked_page,
					     clear_bits,
					     page_ops);
		start += cur_alloc_size;
		if (start >= end)
			goto out;
	}
	extent_clear_unlock_delalloc(inode, start, end, delalloc_end,
				     locked_page,
				     clear_bits | EXTENT_CLEAR_DATA_RESV,
				     page_ops);
	goto out;
}
				u64 start, u64 end, int *page_started,
				unsigned long *nr_written)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct async_cow *async_cow;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	unsigned long nr_pages;
	u64 cur_end;

	clear_extent_bit(&BTRFS_I(inode)->io_tree, start, end, EXTENT_LOCKED,
			 1, 0, NULL, GFP_NOFS);
	while (start < end) {
		async_cow = kmalloc(sizeof(*async_cow), GFP_NOFS);
		BUG_ON(!async_cow); /* -ENOMEM */
		async_cow->inode = igrab(inode);
		async_cow->root = root;
		async_cow->locked_page = locked_page;
		async_cow->start = start;

		if (BTRFS_I(inode)->flags & BTRFS_INODE_NOCOMPRESS &&
		    !btrfs_test_opt(fs_info, FORCE_COMPRESS))
			cur_end = end;
		else
			cur_end = min(end, start + SZ_512K - 1);

		async_cow->end = cur_end;
		INIT_LIST_HEAD(&async_cow->extents);

		btrfs_init_work(&async_cow->work,
				btrfs_delalloc_helper,
				async_cow_start, async_cow_submit,
				async_cow_free);

		nr_pages = (cur_end - start + PAGE_SIZE) >>
			PAGE_SHIFT;
		atomic_add(nr_pages, &fs_info->async_delalloc_pages);

		btrfs_queue_work(fs_info->delalloc_workers, &async_cow->work);

		while (atomic_read(&fs_info->async_submit_draining) &&
		       atomic_read(&fs_info->async_delalloc_pages)) {
			wait_event(fs_info->async_submit_wait,
				   (atomic_read(&fs_info->async_delalloc_pages) ==
				    0));
		}

		*nr_written += nr_pages;
		start = cur_end + 1;
	}
	*page_started = 1;
	return 0;
}
static noinline int csum_exist_in_range(struct btrfs_fs_info *fs_info,
					u64 bytenr, u64 num_bytes)
{
	int ret;
	struct btrfs_ordered_sum *sums;
	LIST_HEAD(list);

	ret = btrfs_lookup_csums_range(fs_info->csum_root, bytenr,
				       bytenr + num_bytes - 1, &list, 0);
	if (ret == 0 && list_empty(&list))
		return 0;

	while (!list_empty(&list)) {
		sums = list_entry(list.next, struct btrfs_ordered_sum, list);
		list_del(&sums->list);
		kfree(sums);
	}
	return 1;
}
			      u64 start, u64 end, int *page_started, int force,
			      unsigned long *nr_written)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct extent_buffer *leaf;
	struct btrfs_path *path;
	struct btrfs_file_extent_item *fi;
	struct btrfs_key found_key;
	struct extent_map *em;
	u64 cow_start;
	u64 cur_offset;
	u64 extent_end;
	u64 extent_offset;
	u64 disk_bytenr;
	u64 num_bytes;
	u64 disk_num_bytes;
	u64 ram_bytes;
	int extent_type;
	int ret, err;
	int type;
	int nocow;
	int check_prev = 1;
	bool nolock;
	u64 ino = btrfs_ino(BTRFS_I(inode));

	path = btrfs_alloc_path();
	if (!path) {
		extent_clear_unlock_delalloc(inode, start, end, end,
					     locked_page,
					     EXTENT_LOCKED | EXTENT_DELALLOC |
					     EXTENT_DO_ACCOUNTING |
					     EXTENT_DEFRAG, PAGE_UNLOCK |
					     PAGE_CLEAR_DIRTY |
					     PAGE_SET_WRITEBACK |
					     PAGE_END_WRITEBACK);
		return -ENOMEM;
	}

	nolock = btrfs_is_free_space_inode(BTRFS_I(inode));

	cow_start = (u64)-1;
	cur_offset = start;
	while (1) {
		ret = btrfs_lookup_file_extent(NULL, root, path, ino,
					       cur_offset, 0);
		if (ret < 0)
			goto error;
		if (ret > 0 && path->slots[0] > 0 && check_prev) {
			leaf = path->nodes[0];
			btrfs_item_key_to_cpu(leaf, &found_key,
					      path->slots[0] - 1);
			if (found_key.objectid == ino &&
			    found_key.type == BTRFS_EXTENT_DATA_KEY)
				path->slots[0]--;
		}
		check_prev = 0;
next_slot:
		leaf = path->nodes[0];
		if (path->slots[0] >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto error;
			if (ret > 0)
				break;
			leaf = path->nodes[0];
		}

		nocow = 0;
		disk_bytenr = 0;
		num_bytes = 0;
		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);

		if (found_key.objectid > ino)
			break;
		if (WARN_ON_ONCE(found_key.objectid < ino) ||
		    found_key.type < BTRFS_EXTENT_DATA_KEY) {
			path->slots[0]++;
			goto next_slot;
		}
		if (found_key.type > BTRFS_EXTENT_DATA_KEY ||
		    found_key.offset > end)
			break;

		if (found_key.offset > cur_offset) {
			extent_end = found_key.offset;
			extent_type = 0;
			goto out_check;
		}

		fi = btrfs_item_ptr(leaf, path->slots[0],
				    struct btrfs_file_extent_item);
		extent_type = btrfs_file_extent_type(leaf, fi);

		ram_bytes = btrfs_file_extent_ram_bytes(leaf, fi);
		if (extent_type == BTRFS_FILE_EXTENT_REG ||
		    extent_type == BTRFS_FILE_EXTENT_PREALLOC) {
			disk_bytenr = btrfs_file_extent_disk_bytenr(leaf, fi);
			extent_offset = btrfs_file_extent_offset(leaf, fi);
			extent_end = found_key.offset +
				btrfs_file_extent_num_bytes(leaf, fi);
			disk_num_bytes =
				btrfs_file_extent_disk_num_bytes(leaf, fi);
			if (extent_end <= start) {
				path->slots[0]++;
				goto next_slot;
			}
			if (disk_bytenr == 0)
				goto out_check;
			if (btrfs_file_extent_compression(leaf, fi) ||
			    btrfs_file_extent_encryption(leaf, fi) ||
			    btrfs_file_extent_other_encoding(leaf, fi))
				goto out_check;
			if (extent_type == BTRFS_FILE_EXTENT_REG && !force)
				goto out_check;
			if (btrfs_extent_readonly(fs_info, disk_bytenr))
				goto out_check;
			if (btrfs_cross_ref_exist(root, ino,
						  found_key.offset -
						  extent_offset, disk_bytenr))
				goto out_check;
			disk_bytenr += extent_offset;
			disk_bytenr += cur_offset - found_key.offset;
			num_bytes = min(end + 1, extent_end) - cur_offset;
			/*
			 * if there are pending snapshots for this root,
			 * we fall into common COW way.
			 */
			if (!nolock) {
				err = btrfs_start_write_no_snapshoting(root);
				if (!err)
					goto out_check;
			}
			/*
			 * force cow if csum exists in the range.
			 * this ensure that csum for a given extent are
			 * either valid or do not exist.
			 */
			if (csum_exist_in_range(fs_info, disk_bytenr,
						num_bytes)) {
				if (!nolock)
					btrfs_end_write_no_snapshoting(root);
				goto out_check;
			}
			if (!btrfs_inc_nocow_writers(fs_info, disk_bytenr)) {
				if (!nolock)
					btrfs_end_write_no_snapshoting(root);
				goto out_check;
			}
			nocow = 1;
		} else if (extent_type == BTRFS_FILE_EXTENT_INLINE) {
			extent_end = found_key.offset +
				btrfs_file_extent_inline_len(leaf,
						     path->slots[0], fi);
			extent_end = ALIGN(extent_end,
					   fs_info->sectorsize);
		} else {
			BUG_ON(1);
		}
out_check:
		if (extent_end <= start) {
			path->slots[0]++;
			if (!nolock && nocow)
				btrfs_end_write_no_snapshoting(root);
			if (nocow)
				btrfs_dec_nocow_writers(fs_info, disk_bytenr);
			goto next_slot;
		}
		if (!nocow) {
			if (cow_start == (u64)-1)
				cow_start = cur_offset;
			cur_offset = extent_end;
			if (cur_offset > end)
				break;
			path->slots[0]++;
			goto next_slot;
		}

		btrfs_release_path(path);
		if (cow_start != (u64)-1) {
			ret = cow_file_range(inode, locked_page,
					     cow_start, found_key.offset - 1,
					     end, page_started, nr_written, 1,
					     NULL);
			if (ret) {
				if (!nolock && nocow)
					btrfs_end_write_no_snapshoting(root);
				if (nocow)
					btrfs_dec_nocow_writers(fs_info,
								disk_bytenr);
				goto error;
			}
			cow_start = (u64)-1;
		}

		if (extent_type == BTRFS_FILE_EXTENT_PREALLOC) {
			u64 orig_start = found_key.offset - extent_offset;

			em = create_io_em(inode, cur_offset, num_bytes,
					  orig_start,
					  disk_bytenr, /* block_start */
					  num_bytes, /* block_len */
					  disk_num_bytes, /* orig_block_len */
					  ram_bytes, BTRFS_COMPRESS_NONE,
					  BTRFS_ORDERED_PREALLOC);
			if (IS_ERR(em)) {
				if (!nolock && nocow)
					btrfs_end_write_no_snapshoting(root);
				if (nocow)
					btrfs_dec_nocow_writers(fs_info,
								disk_bytenr);
				ret = PTR_ERR(em);
				goto error;
			}
			free_extent_map(em);
		}

		if (extent_type == BTRFS_FILE_EXTENT_PREALLOC) {
			type = BTRFS_ORDERED_PREALLOC;
		} else {
			type = BTRFS_ORDERED_NOCOW;
		}

		ret = btrfs_add_ordered_extent(inode, cur_offset, disk_bytenr,
					       num_bytes, num_bytes, type);
		if (nocow)
			btrfs_dec_nocow_writers(fs_info, disk_bytenr);
		BUG_ON(ret); /* -ENOMEM */

		if (root->root_key.objectid ==
		    BTRFS_DATA_RELOC_TREE_OBJECTID)
			/*
			 * Error handled later, as we must prevent
			 * extent_clear_unlock_delalloc() in error handler
			 * from freeing metadata of created ordered extent.
			 */
			ret = btrfs_reloc_clone_csums(inode, cur_offset,
						      num_bytes);

		extent_clear_unlock_delalloc(inode, cur_offset,
					     cur_offset + num_bytes - 1, end,
					     locked_page, EXTENT_LOCKED |
					     EXTENT_DELALLOC |
					     EXTENT_CLEAR_DATA_RESV,
					     PAGE_UNLOCK | PAGE_SET_PRIVATE2);

		if (!nolock && nocow)
			btrfs_end_write_no_snapshoting(root);
		cur_offset = extent_end;

		/*
		 * btrfs_reloc_clone_csums() error, now we're OK to call error
		 * handler, as metadata for created ordered extent will only
		 * be freed by btrfs_finish_ordered_io().
		 */
		if (ret)
			goto error;
		if (cur_offset > end)
			break;
	}
	btrfs_release_path(path);

	if (cur_offset <= end && cow_start == (u64)-1) {
		cow_start = cur_offset;
		cur_offset = end;
	}

	if (cow_start != (u64)-1) {
		ret = cow_file_range(inode, locked_page, cow_start, end, end,
				     page_started, nr_written, 1, NULL);
		if (ret)
			goto error;
	}

error:
	if (ret && cur_offset < end)
		extent_clear_unlock_delalloc(inode, cur_offset, end, end,
					     locked_page, EXTENT_LOCKED |
					     EXTENT_DELALLOC | EXTENT_DEFRAG |
					     EXTENT_DO_ACCOUNTING, PAGE_UNLOCK |
					     PAGE_CLEAR_DIRTY |
					     PAGE_SET_WRITEBACK |
					     PAGE_END_WRITEBACK);
	btrfs_free_path(path);
	return ret;
}
static void backref_insert(struct rb_root *root,
			   struct sa_defrag_extent_backref *backref)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent = NULL;
	struct sa_defrag_extent_backref *entry;
	int ret;

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct sa_defrag_extent_backref, node);

		ret = backref_comp(backref, entry);
		if (ret < 0)
			p = &(*p)->rb_left;
		else
			p = &(*p)->rb_right;
	}

	rb_link_node(&backref->node, parent, p);
	rb_insert_color(&backref->node, root);
}
static noinline int record_one_backref(u64 inum, u64 offset, u64 root_id,
				       void *ctx)
{
	struct btrfs_file_extent_item *extent;
	struct old_sa_defrag_extent *old = ctx;
	struct new_sa_defrag_extent *new = old->new;
	struct btrfs_path *path = new->path;
	struct btrfs_key key;
	struct btrfs_root *root;
	struct sa_defrag_extent_backref *backref;
	struct extent_buffer *leaf;
	struct inode *inode = new->inode;
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	int slot;
	int ret;
	u64 extent_offset;
	u64 num_bytes;

	if (BTRFS_I(inode)->root->root_key.objectid == root_id &&
	    inum == btrfs_ino(BTRFS_I(inode)))
		return 0;

	key.objectid = root_id;
	key.type = BTRFS_ROOT_ITEM_KEY;
	key.offset = (u64)-1;

	root = btrfs_read_fs_root_no_name(fs_info, &key);
	if (IS_ERR(root)) {
		if (PTR_ERR(root) == -ENOENT)
			return 0;
		WARN_ON(1);
		btrfs_debug(fs_info, "inum=%llu, offset=%llu, root_id=%llu",
			 inum, offset, root_id);
		return PTR_ERR(root);
	}

	key.objectid = inum;
	key.type = BTRFS_EXTENT_DATA_KEY;
	if (offset > (u64)-1 << 32)
		key.offset = 0;
	else
		key.offset = offset;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (WARN_ON(ret < 0))
		return ret;
	ret = 0;

	while (1) {
		cond_resched();

		leaf = path->nodes[0];
		slot = path->slots[0];

		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0) {
				goto out;
			} else if (ret > 0) {
				ret = 0;
				goto out;
			}
			continue;
		}

		path->slots[0]++;

		btrfs_item_key_to_cpu(leaf, &key, slot);

		if (key.objectid > inum)
			goto out;

		if (key.objectid < inum || key.type != BTRFS_EXTENT_DATA_KEY)
			continue;

		extent = btrfs_item_ptr(leaf, slot,
					struct btrfs_file_extent_item);

		if (btrfs_file_extent_disk_bytenr(leaf, extent) != old->bytenr)
			continue;

		/*
		 * 'offset' refers to the exact key.offset,
		 * NOT the 'offset' field in btrfs_extent_data_ref, ie.
		 * (key.offset - extent_offset).
		 */
		if (key.offset != offset)
			continue;

		extent_offset = btrfs_file_extent_offset(leaf, extent);
		num_bytes = btrfs_file_extent_num_bytes(leaf, extent);

		if (extent_offset >= old->extent_offset + old->offset +
		    old->len || extent_offset + num_bytes <=
		    old->extent_offset + old->offset)
			continue;
		break;
	}

	backref = kmalloc(sizeof(*backref), GFP_NOFS);
	if (!backref) {
		ret = -ENOENT;
		goto out;
	}

	backref->root_id = root_id;
	backref->inum = inum;
	backref->file_pos = offset;
	backref->num_bytes = num_bytes;
	backref->extent_offset = extent_offset;
	backref->generation = btrfs_file_extent_generation(leaf, extent);
	backref->old = old;
	backref_insert(&new->root, backref);
	old->count++;
out:
	btrfs_release_path(path);
	WARN_ON(ret);
	return ret;
}

static void relink_file_extents(struct new_sa_defrag_extent *new)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(new->inode->i_sb);
	struct btrfs_path *path;
	struct sa_defrag_extent_backref *backref;
	struct sa_defrag_extent_backref *prev = NULL;
	struct inode *inode;
	struct btrfs_root *root;
	struct rb_node *node;
	int ret;

	inode = new->inode;
	root = BTRFS_I(inode)->root;

	path = btrfs_alloc_path();
	if (!path)
		return;

	if (!record_extent_backrefs(path, new)) {
		btrfs_free_path(path);
		goto out;
	}
	btrfs_release_path(path);

	while (1) {
		node = rb_first(&new->root);
		if (!node)
			break;
		rb_erase(node, &new->root);

		backref = rb_entry(node, struct sa_defrag_extent_backref, node);

		ret = relink_extent_backref(path, prev, backref);
		WARN_ON(ret < 0);

		kfree(prev);

		if (ret == 1)
			prev = backref;
		else
			prev = NULL;
		cond_resched();
	}
	kfree(prev);

	btrfs_free_path(path);
out:
	free_sa_defrag_extent(new);

	atomic_dec(&fs_info->defrag_running);
	wake_up(&fs_info->transaction_wait);
}
record_old_file_extents(struct inode *inode,
			struct btrfs_ordered_extent *ordered)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct old_sa_defrag_extent *old;
	struct new_sa_defrag_extent *new;
	int ret;

	new = kmalloc(sizeof(*new), GFP_NOFS);
	if (!new)
		return NULL;

	new->inode = inode;
	new->file_pos = ordered->file_offset;
	new->len = ordered->len;
	new->bytenr = ordered->start;
	new->disk_len = ordered->disk_len;
	new->compress_type = ordered->compress_type;
	new->root = RB_ROOT;
	INIT_LIST_HEAD(&new->head);

	path = btrfs_alloc_path();
	if (!path)
		goto out_kfree;

	key.objectid = btrfs_ino(BTRFS_I(inode));
	key.type = BTRFS_EXTENT_DATA_KEY;
	key.offset = new->file_pos;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out_free_path;
	if (ret > 0 && path->slots[0] > 0)
		path->slots[0]--;

	/* find out all the old extents for the file range */
	while (1) {
		struct btrfs_file_extent_item *extent;
		struct extent_buffer *l;
		int slot;
		u64 num_bytes;
		u64 offset;
		u64 end;
		u64 disk_bytenr;
		u64 extent_offset;

		l = path->nodes[0];
		slot = path->slots[0];

		if (slot >= btrfs_header_nritems(l)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out_free_path;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(l, &key, slot);

		if (key.objectid != btrfs_ino(BTRFS_I(inode)))
			break;
		if (key.type != BTRFS_EXTENT_DATA_KEY)
			break;
		if (key.offset >= new->file_pos + new->len)
			break;

		extent = btrfs_item_ptr(l, slot, struct btrfs_file_extent_item);

		num_bytes = btrfs_file_extent_num_bytes(l, extent);
		if (key.offset + num_bytes < new->file_pos)
			goto next;

		disk_bytenr = btrfs_file_extent_disk_bytenr(l, extent);
		if (!disk_bytenr)
			goto next;

		extent_offset = btrfs_file_extent_offset(l, extent);

		old = kmalloc(sizeof(*old), GFP_NOFS);
		if (!old)
			goto out_free_path;

		offset = max(new->file_pos, key.offset);
		end = min(new->file_pos + new->len, key.offset + num_bytes);

		old->bytenr = disk_bytenr;
		old->extent_offset = extent_offset;
		old->offset = offset - key.offset;
		old->len = end - offset;
		old->new = new;
		old->count = 0;
		list_add_tail(&old->list, &new->head);
next:
		path->slots[0]++;
		cond_resched();
	}

	btrfs_free_path(path);
	atomic_inc(&fs_info->defrag_running);

	return new;

out_free_path:
	btrfs_free_path(path);
out_kfree:
	free_sa_defrag_extent(new);
	return NULL;
}

void btrfs_run_delayed_iputs(struct btrfs_fs_info *fs_info)
{

	spin_lock(&fs_info->delayed_iput_lock);
	while (!list_empty(&fs_info->delayed_iputs)) {
		struct btrfs_inode *inode;

		inode = list_first_entry(&fs_info->delayed_iputs,
				struct btrfs_inode, delayed_iput);
		if (inode->delayed_iput_count) {
			inode->delayed_iput_count--;
			list_move_tail(&inode->delayed_iput,
					&fs_info->delayed_iputs);
		} else {
			list_del_init(&inode->delayed_iput);
		}
		spin_unlock(&fs_info->delayed_iput_lock);
		iput(&inode->vfs_inode);
		spin_lock(&fs_info->delayed_iput_lock);
	}
	spin_unlock(&fs_info->delayed_iput_lock);
}
 */
int btrfs_orphan_cleanup(struct btrfs_root *root)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_key key, found_key;
	struct btrfs_trans_handle *trans;
	struct inode *inode;
	u64 last_objectid = 0;
	int ret = 0, nr_unlink = 0, nr_truncate = 0;

	if (cmpxchg(&root->orphan_cleanup_state, 0, ORPHAN_CLEANUP_STARTED))
		return 0;

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}
	path->reada = READA_BACK;

	key.objectid = BTRFS_ORPHAN_OBJECTID;
	key.type = BTRFS_ORPHAN_ITEM_KEY;
	key.offset = (u64)-1;

	while (1) {
		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0)
			goto out;

		/*
		 * if ret == 0 means we found what we were searching for, which
		 * is weird, but possible, so only screw with path if we didn't
		 * find the key and see if we have stuff that matches
		 */
		if (ret > 0) {
			ret = 0;
			if (path->slots[0] == 0)
				break;
			path->slots[0]--;
		}

		/* pull out the item */
		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);

		/* make sure the item matches what we want */
		if (found_key.objectid != BTRFS_ORPHAN_OBJECTID)
			break;
		if (found_key.type != BTRFS_ORPHAN_ITEM_KEY)
			break;

		/* release the path since we're done with it */
		btrfs_release_path(path);

		/*
		 * this is where we are basically btrfs_lookup, without the
		 * crossing root thing.  we store the inode number in the
		 * offset of the orphan item.
		 */

		if (found_key.offset == last_objectid) {
			btrfs_err(fs_info,
				  "Error removing orphan entry, stopping orphan cleanup");
			ret = -EINVAL;
			goto out;
		}

		last_objectid = found_key.offset;

		found_key.objectid = found_key.offset;
		found_key.type = BTRFS_INODE_ITEM_KEY;
		found_key.offset = 0;
		inode = btrfs_iget(fs_info->sb, &found_key, root, NULL);
		ret = PTR_ERR_OR_ZERO(inode);
		if (ret && ret != -ENOENT)
			goto out;

		if (ret == -ENOENT && root == fs_info->tree_root) {
			struct btrfs_root *dead_root;
			struct btrfs_fs_info *fs_info = root->fs_info;
			int is_dead_root = 0;

			/*
			 * this is an orphan in the tree root. Currently these
			 * could come from 2 sources:
			 *  a) a snapshot deletion in progress
			 *  b) a free space cache inode
			 * We need to distinguish those two, as the snapshot
			 * orphan must not get deleted.
			 * find_dead_roots already ran before us, so if this
			 * is a snapshot deletion, we should find the root
			 * in the dead_roots list
			 */
			spin_lock(&fs_info->trans_lock);
			list_for_each_entry(dead_root, &fs_info->dead_roots,
					    root_list) {
				if (dead_root->root_key.objectid ==
				    found_key.objectid) {
					is_dead_root = 1;
					break;
				}
			}
			spin_unlock(&fs_info->trans_lock);
			if (is_dead_root) {
				/* prevent this orphan from being found again */
				key.offset = found_key.objectid - 1;
				continue;
			}
		}
		/*
		 * Inode is already gone but the orphan item is still there,
		 * kill the orphan item.
		 */
		if (ret == -ENOENT) {
			trans = btrfs_start_transaction(root, 1);
			if (IS_ERR(trans)) {
				ret = PTR_ERR(trans);
				goto out;
			}
			btrfs_debug(fs_info, "auto deleting %Lu",
				    found_key.objectid);
			ret = btrfs_del_orphan_item(trans, root,
						    found_key.objectid);
			btrfs_end_transaction(trans);
			if (ret)
				goto out;
			continue;
		}

		/*
		 * add this inode to the orphan list so btrfs_orphan_del does
		 * the proper thing when we hit it
		 */
		set_bit(BTRFS_INODE_HAS_ORPHAN_ITEM,
			&BTRFS_I(inode)->runtime_flags);
		atomic_inc(&root->orphan_inodes);

		/* if we have links, this was a truncate, lets do that */
		if (inode->i_nlink) {
			if (WARN_ON(!S_ISREG(inode->i_mode))) {
				iput(inode);
				continue;
			}
			nr_truncate++;

			/* 1 for the orphan item deletion. */
			trans = btrfs_start_transaction(root, 1);
			if (IS_ERR(trans)) {
				iput(inode);
				ret = PTR_ERR(trans);
				goto out;
			}
			ret = btrfs_orphan_add(trans, BTRFS_I(inode));
			btrfs_end_transaction(trans);
			if (ret) {
				iput(inode);
				goto out;
			}

			ret = btrfs_truncate(inode);
			if (ret)
				btrfs_orphan_del(NULL, BTRFS_I(inode));
		} else {
			nr_unlink++;
		}

		/* this will do delete_inode and everything for us */
		iput(inode);
		if (ret)
			goto out;
	}
	/* release the path since we're done with it */
	btrfs_release_path(path);

	root->orphan_cleanup_state = ORPHAN_CLEANUP_DONE;

	if (root->orphan_block_rsv)
		btrfs_block_rsv_release(fs_info, root->orphan_block_rsv,
					(u64)-1);

	if (root->orphan_block_rsv ||
	    test_bit(BTRFS_ROOT_ORPHAN_ITEM_INSERTED, &root->state)) {
		trans = btrfs_join_transaction(root);
		if (!IS_ERR(trans))
			btrfs_end_transaction(trans);
	}

	if (nr_unlink)
		btrfs_debug(fs_info, "unlinked %d orphans", nr_unlink);
	if (nr_truncate)
		btrfs_debug(fs_info, "truncated %d orphans", nr_truncate);

out:
	if (ret)
		btrfs_err(fs_info, "could not do orphan cleanup %d", ret);
	btrfs_free_path(path);
	return ret;
}
					  int slot, u64 objectid,
					  int *first_xattr_slot)
{
	u32 nritems = btrfs_header_nritems(leaf);
	struct btrfs_key found_key;
	static u64 xattr_access = 0;
	static u64 xattr_default = 0;
	int scanned = 0;

	if (!xattr_access) {
		xattr_access = btrfs_name_hash(XATTR_NAME_POSIX_ACL_ACCESS,
					strlen(XATTR_NAME_POSIX_ACL_ACCESS));
		xattr_default = btrfs_name_hash(XATTR_NAME_POSIX_ACL_DEFAULT,
					strlen(XATTR_NAME_POSIX_ACL_DEFAULT));
	}

	slot++;
	*first_xattr_slot = -1;
	while (slot < nritems) {
		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		/* we found a different objectid, there must not be acls */
		if (found_key.objectid != objectid)
			return 0;

		/* we found an xattr, assume we've got an acl */
		if (found_key.type == BTRFS_XATTR_ITEM_KEY) {
			if (*first_xattr_slot == -1)
				*first_xattr_slot = slot;
			if (found_key.offset == xattr_access ||
			    found_key.offset == xattr_default)
				return 1;
		}

		/*
		 * we found a key greater than an xattr key, there can't
		 * be any acls later on
		 */
		if (found_key.type > BTRFS_XATTR_ITEM_KEY)
			return 0;

		slot++;
		scanned++;

		/*
		 * it goes inode, inode backrefs, xattrs, extents,
		 * so if there are a ton of hard links to an inode there can
		 * be a lot of backrefs.  Don't waste time searching too hard,
		 * this is just an optimization
		 */
		if (scanned >= 8)
			break;
	}
	/* we hit the end of the leaf before we found an xattr or
	 * something larger than an xattr.  We have to assume the inode
	 * has acls
	 */
	if (*first_xattr_slot == -1)
		*first_xattr_slot = slot;
	return 1;
}
			       struct inode *inode,
			       u64 new_size, u32 min_type)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_file_extent_item *fi;
	struct btrfs_key key;
	struct btrfs_key found_key;
	u64 extent_start = 0;
	u64 extent_num_bytes = 0;
	u64 extent_offset = 0;
	u64 item_end = 0;
	u64 last_size = new_size;
	u32 found_type = (u8)-1;
	int found_extent;
	int del_item;
	int pending_del_nr = 0;
	int pending_del_slot = 0;
	int extent_type = -1;
	int ret;
	int err = 0;
	u64 ino = btrfs_ino(BTRFS_I(inode));
	u64 bytes_deleted = 0;
	bool be_nice = 0;
	bool should_throttle = 0;
	bool should_end = 0;

	BUG_ON(new_size > 0 && min_type != BTRFS_EXTENT_DATA_KEY);

	/*
	 * for non-free space inodes and ref cows, we want to back off from
	 * time to time
	 */
	if (!btrfs_is_free_space_inode(BTRFS_I(inode)) &&
	    test_bit(BTRFS_ROOT_REF_COWS, &root->state))
		be_nice = 1;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->reada = READA_BACK;

	/*
	 * We want to drop from the next block forward in case this new size is
	 * not block aligned since we will be keeping the last block of the
	 * extent just the way it is.
	 */
	if (test_bit(BTRFS_ROOT_REF_COWS, &root->state) ||
	    root == fs_info->tree_root)
		btrfs_drop_extent_cache(BTRFS_I(inode), ALIGN(new_size,
					fs_info->sectorsize),
					(u64)-1, 0);

	/*
	 * This function is also used to drop the items in the log tree before
	 * we relog the inode, so if root != BTRFS_I(inode)->root, it means
	 * it is used to drop the loged items. So we shouldn't kill the delayed
	 * items.
	 */
	if (min_type == 0 && root == BTRFS_I(inode)->root)
		btrfs_kill_delayed_inode_items(BTRFS_I(inode));

	key.objectid = ino;
	key.offset = (u64)-1;
	key.type = (u8)-1;

search_again:
	/*
	 * with a 16K leaf size and 128MB extents, you can actually queue
	 * up a huge file in a single leaf.  Most of the time that
	 * bytes_deleted is > 0, it will be huge by the time we get here
	 */
	if (be_nice && bytes_deleted > SZ_32M) {
		if (btrfs_should_end_transaction(trans)) {
			err = -EAGAIN;
			goto error;
		}
	}


	path->leave_spinning = 1;
	ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
	if (ret < 0) {
		err = ret;
		goto out;
	}

	if (ret > 0) {
		/* there are no items in the tree for us to truncate, we're
		 * done
		 */
		if (path->slots[0] == 0)
			goto out;
		path->slots[0]--;
	}

	while (1) {
		fi = NULL;
		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);
		found_type = found_key.type;

		if (found_key.objectid != ino)
			break;

		if (found_type < min_type)
			break;

		item_end = found_key.offset;
		if (found_type == BTRFS_EXTENT_DATA_KEY) {
			fi = btrfs_item_ptr(leaf, path->slots[0],
					    struct btrfs_file_extent_item);
			extent_type = btrfs_file_extent_type(leaf, fi);
			if (extent_type != BTRFS_FILE_EXTENT_INLINE) {
				item_end +=
				    btrfs_file_extent_num_bytes(leaf, fi);

				trace_btrfs_truncate_show_fi_regular(
					BTRFS_I(inode), leaf, fi,
					found_key.offset);
			} else if (extent_type == BTRFS_FILE_EXTENT_INLINE) {
				item_end += btrfs_file_extent_inline_len(leaf,
							 path->slots[0], fi);

				trace_btrfs_truncate_show_fi_inline(
					BTRFS_I(inode), leaf, fi, path->slots[0],
					found_key.offset);
			}
			item_end--;
		}
		if (found_type > min_type) {
			del_item = 1;
		} else {
			if (item_end < new_size)
				break;
			if (found_key.offset >= new_size)
				del_item = 1;
			else
				del_item = 0;
		}
		found_extent = 0;
		/* FIXME, shrink the extent if the ref count is only 1 */
		if (found_type != BTRFS_EXTENT_DATA_KEY)
			goto delete;

		if (del_item)
			last_size = found_key.offset;
		else
			last_size = new_size;

		if (extent_type != BTRFS_FILE_EXTENT_INLINE) {
			u64 num_dec;
			extent_start = btrfs_file_extent_disk_bytenr(leaf, fi);
			if (!del_item) {
				u64 orig_num_bytes =
					btrfs_file_extent_num_bytes(leaf, fi);
				extent_num_bytes = ALIGN(new_size -
						found_key.offset,
						fs_info->sectorsize);
				btrfs_set_file_extent_num_bytes(leaf, fi,
							 extent_num_bytes);
				num_dec = (orig_num_bytes -
					   extent_num_bytes);
				if (test_bit(BTRFS_ROOT_REF_COWS,
					     &root->state) &&
				    extent_start != 0)
					inode_sub_bytes(inode, num_dec);
				btrfs_mark_buffer_dirty(leaf);
			} else {
				extent_num_bytes =
					btrfs_file_extent_disk_num_bytes(leaf,
									 fi);
				extent_offset = found_key.offset -
					btrfs_file_extent_offset(leaf, fi);

				/* FIXME blocksize != 4096 */
				num_dec = btrfs_file_extent_num_bytes(leaf, fi);
				if (extent_start != 0) {
					found_extent = 1;
					if (test_bit(BTRFS_ROOT_REF_COWS,
						     &root->state))
						inode_sub_bytes(inode, num_dec);
				}
			}
		} else if (extent_type == BTRFS_FILE_EXTENT_INLINE) {
			/*
			 * we can't truncate inline items that have had
			 * special encodings
			 */
			if (!del_item &&
			    btrfs_file_extent_encryption(leaf, fi) == 0 &&
			    btrfs_file_extent_other_encoding(leaf, fi) == 0) {

				/*
				 * Need to release path in order to truncate a
				 * compressed extent. So delete any accumulated
				 * extent items so far.
				 */
				if (btrfs_file_extent_compression(leaf, fi) !=
				    BTRFS_COMPRESS_NONE && pending_del_nr) {
					err = btrfs_del_items(trans, root, path,
							      pending_del_slot,
							      pending_del_nr);
					if (err) {
						btrfs_abort_transaction(trans,
									err);
						goto error;
					}
					pending_del_nr = 0;
				}

				err = truncate_inline_extent(inode, path,
							     &found_key,
							     item_end,
							     new_size);
				if (err) {
					btrfs_abort_transaction(trans, err);
					goto error;
				}
			} else if (test_bit(BTRFS_ROOT_REF_COWS,
					    &root->state)) {
				inode_sub_bytes(inode, item_end + 1 - new_size);
			}
		}
delete:
		if (del_item) {
			if (!pending_del_nr) {
				/* no pending yet, add ourselves */
				pending_del_slot = path->slots[0];
				pending_del_nr = 1;
			} else if (pending_del_nr &&
				   path->slots[0] + 1 == pending_del_slot) {
				/* hop on the pending chunk */
				pending_del_nr++;
				pending_del_slot = path->slots[0];
			} else {
				BUG();
			}
		} else {
			break;
		}
		should_throttle = 0;

		if (found_extent &&
		    (test_bit(BTRFS_ROOT_REF_COWS, &root->state) ||
		     root == fs_info->tree_root)) {
			btrfs_set_path_blocking(path);
			bytes_deleted += extent_num_bytes;
			ret = btrfs_free_extent(trans, fs_info, extent_start,
						extent_num_bytes, 0,
						btrfs_header_owner(leaf),
						ino, extent_offset);
			BUG_ON(ret);
			if (btrfs_should_throttle_delayed_refs(trans, fs_info))
				btrfs_async_run_delayed_refs(fs_info,
					trans->delayed_ref_updates * 2,
					trans->transid, 0);
			if (be_nice) {
				if (truncate_space_check(trans, root,
							 extent_num_bytes)) {
					should_end = 1;
				}
				if (btrfs_should_throttle_delayed_refs(trans,
								       fs_info))
					should_throttle = 1;
			}
		}

		if (found_type == BTRFS_INODE_ITEM_KEY)
			break;

		if (path->slots[0] == 0 ||
		    path->slots[0] != pending_del_slot ||
		    should_throttle || should_end) {
			if (pending_del_nr) {
				ret = btrfs_del_items(trans, root, path,
						pending_del_slot,
						pending_del_nr);
				if (ret) {
					btrfs_abort_transaction(trans, ret);
					goto error;
				}
				pending_del_nr = 0;
			}
			btrfs_release_path(path);
			if (should_throttle) {
				unsigned long updates = trans->delayed_ref_updates;
				if (updates) {
					trans->delayed_ref_updates = 0;
					ret = btrfs_run_delayed_refs(trans,
								   fs_info,
								   updates * 2);
					if (ret && !err)
						err = ret;
				}
			}
			/*
			 * if we failed to refill our space rsv, bail out
			 * and let the transaction restart
			 */
			if (should_end) {
				err = -EAGAIN;
				goto error;
			}
			goto search_again;
		} else {
			path->slots[0]--;
		}
	}
out:
	if (pending_del_nr) {
		ret = btrfs_del_items(trans, root, path, pending_del_slot,
				      pending_del_nr);
		if (ret)
			btrfs_abort_transaction(trans, ret);
	}
error:
	if (root->root_key.objectid != BTRFS_TREE_LOG_OBJECTID) {
		ASSERT(last_size >= new_size);
		if (!err && last_size > new_size)
			last_size = new_size;
		btrfs_ordered_update_i_size(inode, last_size, NULL);
	}

	btrfs_free_path(path);

	if (be_nice && bytes_deleted > SZ_32M) {
		unsigned long updates = trans->delayed_ref_updates;
		if (updates) {
			trans->delayed_ref_updates = 0;
			ret = btrfs_run_delayed_refs(trans, fs_info,
						     updates * 2);
			if (ret && !err)
				err = ret;
		}
	}
	return err;
}
 */
int btrfs_cont_expand(struct inode *inode, loff_t oldsize, loff_t size)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct extent_io_tree *io_tree = &BTRFS_I(inode)->io_tree;
	struct extent_map *em = NULL;
	struct extent_state *cached_state = NULL;
	struct extent_map_tree *em_tree = &BTRFS_I(inode)->extent_tree;
	u64 hole_start = ALIGN(oldsize, fs_info->sectorsize);
	u64 block_end = ALIGN(size, fs_info->sectorsize);
	u64 last_byte;
	u64 cur_offset;
	u64 hole_size;
	int err = 0;

	/*
	 * If our size started in the middle of a block we need to zero out the
	 * rest of the block before we expand the i_size, otherwise we could
	 * expose stale data.
	 */
	err = btrfs_truncate_block(inode, oldsize, 0, 0);
	if (err)
		return err;

	if (size <= hole_start)
		return 0;

	while (1) {
		struct btrfs_ordered_extent *ordered;

		lock_extent_bits(io_tree, hole_start, block_end - 1,
				 &cached_state);
		ordered = btrfs_lookup_ordered_range(BTRFS_I(inode), hole_start,
						     block_end - hole_start);
		if (!ordered)
			break;
		unlock_extent_cached(io_tree, hole_start, block_end - 1,
				     &cached_state, GFP_NOFS);
		btrfs_start_ordered_extent(inode, ordered, 1);
		btrfs_put_ordered_extent(ordered);
	}

	cur_offset = hole_start;
	while (1) {
		em = btrfs_get_extent(BTRFS_I(inode), NULL, 0, cur_offset,
				block_end - cur_offset, 0);
		if (IS_ERR(em)) {
			err = PTR_ERR(em);
			em = NULL;
			break;
		}
		last_byte = min(extent_map_end(em), block_end);
		last_byte = ALIGN(last_byte, fs_info->sectorsize);
		if (!test_bit(EXTENT_FLAG_PREALLOC, &em->flags)) {
			struct extent_map *hole_em;
			hole_size = last_byte - cur_offset;

			err = maybe_insert_hole(root, inode, cur_offset,
						hole_size);
			if (err)
				break;
			btrfs_drop_extent_cache(BTRFS_I(inode), cur_offset,
						cur_offset + hole_size - 1, 0);
			hole_em = alloc_extent_map();
			if (!hole_em) {
				set_bit(BTRFS_INODE_NEEDS_FULL_SYNC,
					&BTRFS_I(inode)->runtime_flags);
				goto next;
			}
			hole_em->start = cur_offset;
			hole_em->len = hole_size;
			hole_em->orig_start = cur_offset;

			hole_em->block_start = EXTENT_MAP_HOLE;
			hole_em->block_len = 0;
			hole_em->orig_block_len = 0;
			hole_em->ram_bytes = hole_size;
			hole_em->bdev = fs_info->fs_devices->latest_bdev;
			hole_em->compress_type = BTRFS_COMPRESS_NONE;
			hole_em->generation = fs_info->generation;

			while (1) {
				write_lock(&em_tree->lock);
				err = add_extent_mapping(em_tree, hole_em, 1);
				write_unlock(&em_tree->lock);
				if (err != -EEXIST)
					break;
				btrfs_drop_extent_cache(BTRFS_I(inode),
							cur_offset,
							cur_offset +
							hole_size - 1, 0);
			}
			free_extent_map(hole_em);
		}
next:
		free_extent_map(em);
		em = NULL;
		cur_offset = last_byte;
		if (cur_offset >= block_end)
			break;
	}
	free_extent_map(em);
	unlock_extent_cached(io_tree, hole_start, block_end - 1, &cached_state,
			     GFP_NOFS);
	return err;
}
 */
static void evict_inode_truncate_pages(struct inode *inode)
{
	struct extent_io_tree *io_tree = &BTRFS_I(inode)->io_tree;
	struct extent_map_tree *map_tree = &BTRFS_I(inode)->extent_tree;
	struct rb_node *node;

	ASSERT(inode->i_state & I_FREEING);
	truncate_inode_pages_final(&inode->i_data);

	write_lock(&map_tree->lock);
	while (!RB_EMPTY_ROOT(&map_tree->map)) {
		struct extent_map *em;

		node = rb_first(&map_tree->map);
		em = rb_entry(node, struct extent_map, rb_node);
		clear_bit(EXTENT_FLAG_PINNED, &em->flags);
		clear_bit(EXTENT_FLAG_LOGGING, &em->flags);
		remove_extent_mapping(map_tree, em);
		free_extent_map(em);
		if (need_resched()) {
			write_unlock(&map_tree->lock);
			cond_resched();
			write_lock(&map_tree->lock);
		}
	}
	write_unlock(&map_tree->lock);

	/*
	 * Keep looping until we have no more ranges in the io tree.
	 * We can have ongoing bios started by readpages (called from readahead)
	 * that have their endio callback (extent_io.c:end_bio_extent_readpage)
	 * still in progress (unlocked the pages in the bio but did not yet
	 * unlocked the ranges in the io tree). Therefore this means some
	 * ranges can still be locked and eviction started because before
	 * submitting those bios, which are executed by a separate task (work
	 * queue kthread), inode references (inode->i_count) were not taken
	 * (which would be dropped in the end io callback of each bio).
	 * Therefore here we effectively end up waiting for those bios and
	 * anyone else holding locked ranges without having bumped the inode's
	 * reference count - if we don't do it, when they access the inode's
	 * io_tree to unlock a range it may be too late, leading to an
	 * use-after-free issue.
	 */
	spin_lock(&io_tree->lock);
	while (!RB_EMPTY_ROOT(&io_tree->state)) {
		struct extent_state *state;
		struct extent_state *cached_state = NULL;
		u64 start;
		u64 end;

		node = rb_first(&io_tree->state);
		state = rb_entry(node, struct extent_state, rb_node);
		start = state->start;
		end = state->end;
		spin_unlock(&io_tree->lock);

		lock_extent_bits(io_tree, start, end, &cached_state);

		/*
		 * If still has DELALLOC flag, the extent didn't reach disk,
		 * and its reserved space won't be freed by delayed_ref.
		 * So we need to free its reserved space here.
		 * (Refer to comment in btrfs_invalidatepage, case 2)
		 *
		 * Note, end is the bytenr of last byte, so we need + 1 here.
		 */
		if (state->state & EXTENT_DELALLOC)
			btrfs_qgroup_free_data(inode, start, end - start + 1);

		clear_extent_bit(io_tree, start, end,
				 EXTENT_LOCKED | EXTENT_DIRTY |
				 EXTENT_DELALLOC | EXTENT_DO_ACCOUNTING |
				 EXTENT_DEFRAG, 1, 1,
				 &cached_state, GFP_NOFS);

		cond_resched();
		spin_lock(&io_tree->lock);
	}
	spin_unlock(&io_tree->lock);
}

void btrfs_evict_inode(struct inode *inode)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_trans_handle *trans;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_block_rsv *rsv, *global_rsv;
	int steal_from_global = 0;
	u64 min_size;
	int ret;

	trace_btrfs_inode_evict(inode);

	if (!root) {
		kmem_cache_free(btrfs_inode_cachep, BTRFS_I(inode));
		return;
	}

	min_size = btrfs_calc_trunc_metadata_size(fs_info, 1);

	evict_inode_truncate_pages(inode);

	if (inode->i_nlink &&
	    ((btrfs_root_refs(&root->root_item) != 0 &&
	      root->root_key.objectid != BTRFS_ROOT_TREE_OBJECTID) ||
	     btrfs_is_free_space_inode(BTRFS_I(inode))))
		goto no_delete;

	if (is_bad_inode(inode)) {
		btrfs_orphan_del(NULL, BTRFS_I(inode));
		goto no_delete;
	}
	/* do we really want it for ->i_nlink > 0 and zero btrfs_root_refs? */
	if (!special_file(inode->i_mode))
		btrfs_wait_ordered_range(inode, 0, (u64)-1);

	btrfs_free_io_failure_record(BTRFS_I(inode), 0, (u64)-1);

	if (test_bit(BTRFS_FS_LOG_RECOVERING, &fs_info->flags)) {
		BUG_ON(test_bit(BTRFS_INODE_HAS_ORPHAN_ITEM,
				 &BTRFS_I(inode)->runtime_flags));
		goto no_delete;
	}

	if (inode->i_nlink > 0) {
		BUG_ON(btrfs_root_refs(&root->root_item) != 0 &&
		       root->root_key.objectid != BTRFS_ROOT_TREE_OBJECTID);
		goto no_delete;
	}

	ret = btrfs_commit_inode_delayed_inode(BTRFS_I(inode));
	if (ret) {
		btrfs_orphan_del(NULL, BTRFS_I(inode));
		goto no_delete;
	}

	rsv = btrfs_alloc_block_rsv(fs_info, BTRFS_BLOCK_RSV_TEMP);
	if (!rsv) {
		btrfs_orphan_del(NULL, BTRFS_I(inode));
		goto no_delete;
	}
	rsv->size = min_size;
	rsv->failfast = 1;
	global_rsv = &fs_info->global_block_rsv;

	btrfs_i_size_write(BTRFS_I(inode), 0);

	/*
	 * This is a bit simpler than btrfs_truncate since we've already
	 * reserved our space for our orphan item in the unlink, so we just
	 * need to reserve some slack space in case we add bytes and update
	 * inode item when doing the truncate.
	 */
	while (1) {
		ret = btrfs_block_rsv_refill(root, rsv, min_size,
					     BTRFS_RESERVE_FLUSH_LIMIT);

		/*
		 * Try and steal from the global reserve since we will
		 * likely not use this space anyway, we want to try as
		 * hard as possible to get this to work.
		 */
		if (ret)
			steal_from_global++;
		else
			steal_from_global = 0;
		ret = 0;

		/*
		 * steal_from_global == 0: we reserved stuff, hooray!
		 * steal_from_global == 1: we didn't reserve stuff, boo!
		 * steal_from_global == 2: we've committed, still not a lot of
		 * room but maybe we'll have room in the global reserve this
		 * time.
		 * steal_from_global == 3: abandon all hope!
		 */
		if (steal_from_global > 2) {
			btrfs_warn(fs_info,
				   "Could not get space for a delete, will truncate on mount %d",
				   ret);
			btrfs_orphan_del(NULL, BTRFS_I(inode));
			btrfs_free_block_rsv(fs_info, rsv);
			goto no_delete;
		}

		trans = btrfs_join_transaction(root);
		if (IS_ERR(trans)) {
			btrfs_orphan_del(NULL, BTRFS_I(inode));
			btrfs_free_block_rsv(fs_info, rsv);
			goto no_delete;
		}

		/*
		 * We can't just steal from the global reserve, we need to make
		 * sure there is room to do it, if not we need to commit and try
		 * again.
		 */
		if (steal_from_global) {
			if (!btrfs_check_space_for_delayed_refs(trans, fs_info))
				ret = btrfs_block_rsv_migrate(global_rsv, rsv,
							      min_size, 0);
			else
				ret = -ENOSPC;
		}

		/*
		 * Couldn't steal from the global reserve, we have too much
		 * pending stuff built up, commit the transaction and try it
		 * again.
		 */
		if (ret) {
			ret = btrfs_commit_transaction(trans);
			if (ret) {
				btrfs_orphan_del(NULL, BTRFS_I(inode));
				btrfs_free_block_rsv(fs_info, rsv);
				goto no_delete;
			}
			continue;
		} else {
			steal_from_global = 0;
		}

		trans->block_rsv = rsv;

		ret = btrfs_truncate_inode_items(trans, root, inode, 0, 0);
		if (ret != -ENOSPC && ret != -EAGAIN)
			break;

		trans->block_rsv = &fs_info->trans_block_rsv;
		btrfs_end_transaction(trans);
		trans = NULL;
		btrfs_btree_balance_dirty(fs_info);
	}

	btrfs_free_block_rsv(fs_info, rsv);

	/*
	 * Errors here aren't a big deal, it just means we leave orphan items
	 * in the tree.  They will be cleaned up on the next mount.
	 */
	if (ret == 0) {
		trans->block_rsv = root->orphan_block_rsv;
		btrfs_orphan_del(trans, BTRFS_I(inode));
	} else {
		btrfs_orphan_del(NULL, BTRFS_I(inode));
	}

	trans->block_rsv = &fs_info->trans_block_rsv;
	if (!(root == fs_info->tree_root ||
	      root->root_key.objectid == BTRFS_TREE_RELOC_OBJECTID))
		btrfs_return_ino(root, btrfs_ino(BTRFS_I(inode)));

	btrfs_end_transaction(trans);
	btrfs_btree_balance_dirty(fs_info);
no_delete:
	btrfs_remove_delayed_node(BTRFS_I(inode));
	clear_inode(inode);
}

static void inode_tree_add(struct inode *inode)
{
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_inode *entry;
	struct rb_node **p;
	struct rb_node *parent;
	struct rb_node *new = &BTRFS_I(inode)->rb_node;
	u64 ino = btrfs_ino(BTRFS_I(inode));

	if (inode_unhashed(inode))
		return;
	parent = NULL;
	spin_lock(&root->inode_lock);
	p = &root->inode_tree.rb_node;
	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct btrfs_inode, rb_node);

		if (ino < btrfs_ino(BTRFS_I(&entry->vfs_inode)))
			p = &parent->rb_left;
		else if (ino > btrfs_ino(BTRFS_I(&entry->vfs_inode)))
			p = &parent->rb_right;
		else {
			WARN_ON(!(entry->vfs_inode.i_state &
				  (I_WILL_FREE | I_FREEING)));
			rb_replace_node(parent, new, &root->inode_tree);
			RB_CLEAR_NODE(parent);
			spin_unlock(&root->inode_lock);
			return;
		}
	}
	rb_link_node(new, parent, p);
	rb_insert_color(new, &root->inode_tree);
	spin_unlock(&root->inode_lock);
}

void btrfs_invalidate_inodes(struct btrfs_root *root)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct rb_node *node;
	struct rb_node *prev;
	struct btrfs_inode *entry;
	struct inode *inode;
	u64 objectid = 0;

	if (!test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state))
		WARN_ON(btrfs_root_refs(&root->root_item) != 0);

	spin_lock(&root->inode_lock);
again:
	node = root->inode_tree.rb_node;
	prev = NULL;
	while (node) {
		prev = node;
		entry = rb_entry(node, struct btrfs_inode, rb_node);

		if (objectid < btrfs_ino(BTRFS_I(&entry->vfs_inode)))
			node = node->rb_left;
		else if (objectid > btrfs_ino(BTRFS_I(&entry->vfs_inode)))
			node = node->rb_right;
		else
			break;
	}
	if (!node) {
		while (prev) {
			entry = rb_entry(prev, struct btrfs_inode, rb_node);
			if (objectid <= btrfs_ino(BTRFS_I(&entry->vfs_inode))) {
				node = prev;
				break;
			}
			prev = rb_next(prev);
		}
	}
	while (node) {
		entry = rb_entry(node, struct btrfs_inode, rb_node);
		objectid = btrfs_ino(BTRFS_I(&entry->vfs_inode)) + 1;
		inode = igrab(&entry->vfs_inode);
		if (inode) {
			spin_unlock(&root->inode_lock);
			if (atomic_read(&inode->i_count) > 1)
				d_prune_aliases(inode);
			/*
			 * btrfs_drop_inode will have it removed from
			 * the inode cache when its usage count
			 * hits zero.
			 */
			iput(inode);
			cond_resched();
			spin_lock(&root->inode_lock);
			goto again;
		}

		if (cond_resched_lock(&root->inode_lock))
			goto again;

		node = rb_next(node);
	}
	spin_unlock(&root->inode_lock);
}

static int btrfs_real_readdir(struct file *file, struct dir_context *ctx)
{
	struct inode *inode = file_inode(file);
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_item *item;
	struct btrfs_dir_item *di;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_path *path;
	struct list_head ins_list;
	struct list_head del_list;
	int ret;
	struct extent_buffer *leaf;
	int slot;
	unsigned char d_type;
	int over = 0;
	char tmp_name[32];
	char *name_ptr;
	int name_len;
	bool put = false;
	struct btrfs_key location;

	if (!dir_emit_dots(file, ctx))
		return 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->reada = READA_FORWARD;

	INIT_LIST_HEAD(&ins_list);
	INIT_LIST_HEAD(&del_list);
	put = btrfs_readdir_get_delayed_items(inode, &ins_list, &del_list);

	key.type = BTRFS_DIR_INDEX_KEY;
	key.offset = ctx->pos;
	key.objectid = btrfs_ino(BTRFS_I(inode));

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto err;

	while (1) {
		leaf = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto err;
			else if (ret > 0)
				break;
			continue;
		}

		item = btrfs_item_nr(slot);
		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		if (found_key.objectid != key.objectid)
			break;
		if (found_key.type != BTRFS_DIR_INDEX_KEY)
			break;
		if (found_key.offset < ctx->pos)
			goto next;
		if (btrfs_should_delete_dir_index(&del_list, found_key.offset))
			goto next;

		ctx->pos = found_key.offset;

		di = btrfs_item_ptr(leaf, slot, struct btrfs_dir_item);
		if (verify_dir_item(fs_info, leaf, di))
			goto next;

		name_len = btrfs_dir_name_len(leaf, di);
		if (name_len <= sizeof(tmp_name)) {
			name_ptr = tmp_name;
		} else {
			name_ptr = kmalloc(name_len, GFP_KERNEL);
			if (!name_ptr) {
				ret = -ENOMEM;
				goto err;
			}
		}
		read_extent_buffer(leaf, name_ptr, (unsigned long)(di + 1),
				   name_len);

		d_type = btrfs_filetype_table[btrfs_dir_type(leaf, di)];
		btrfs_dir_item_key_to_cpu(leaf, di, &location);

		over = !dir_emit(ctx, name_ptr, name_len, location.objectid,
				 d_type);

		if (name_ptr != tmp_name)
			kfree(name_ptr);

		if (over)
			goto nopos;
		ctx->pos++;
next:
		path->slots[0]++;
	}

	ret = btrfs_readdir_delayed_dir_index(ctx, &ins_list);
	if (ret)
		goto nopos;

	/*
	 * Stop new entries from being returned after we return the last
	 * entry.
	 *
	 * New directory entries are assigned a strictly increasing
	 * offset.  This means that new entries created during readdir
	 * are *guaranteed* to be seen in the future by that readdir.
	 * This has broken buggy programs which operate on names as
	 * they're returned by readdir.  Until we re-use freed offsets
	 * we have this hack to stop new entries from being returned
	 * under the assumption that they'll never reach this huge
	 * offset.
	 *
	 * This is being careful not to overflow 32bit loff_t unless the
	 * last entry requires it because doing so has broken 32bit apps
	 * in the past.
	 */
	if (ctx->pos >= INT_MAX)
		ctx->pos = LLONG_MAX;
	else
		ctx->pos = INT_MAX;
nopos:
	ret = 0;
err:
	if (put)
		btrfs_readdir_put_delayed_items(inode, &ins_list, &del_list);
	btrfs_free_path(path);
	return ret;
}

bool btrfs_page_exists_in_range(struct inode *inode, loff_t start, loff_t end)
{
	struct radix_tree_root *root = &inode->i_mapping->page_tree;
	int found = false;
	void **pagep = NULL;
	struct page *page = NULL;
	unsigned long start_idx;
	unsigned long end_idx;

	start_idx = start >> PAGE_SHIFT;

	/*
	 * end is the last byte in the last page.  end == start is legal
	 */
	end_idx = end >> PAGE_SHIFT;

	rcu_read_lock();

	/* Most of the code in this while loop is lifted from
	 * find_get_page.  It's been modified to begin searching from a
	 * page and return just the first page found in that range.  If the
	 * found idx is less than or equal to the end idx then we know that
	 * a page exists.  If no pages are found or if those pages are
	 * outside of the range then we're fine (yay!) */
	while (page == NULL &&
	       radix_tree_gang_lookup_slot(root, &pagep, NULL, start_idx, 1)) {
		page = radix_tree_deref_slot(pagep);
		if (unlikely(!page))
			break;

		if (radix_tree_exception(page)) {
			if (radix_tree_deref_retry(page)) {
				page = NULL;
				continue;
			}
			/*
			 * Otherwise, shmem/tmpfs must be storing a swap entry
			 * here as an exceptional entry: so return it without
			 * attempting to raise page count.
			 */
			page = NULL;
			break; /* TODO: Is this relevant for this use case? */
		}

		if (!page_cache_get_speculative(page)) {
			page = NULL;
			continue;
		}

		/*
		 * Has the page moved?
		 * This is part of the lockless pagecache protocol. See
		 * include/linux/pagemap.h for details.
		 */
		if (unlikely(page != *pagep)) {
			put_page(page);
			page = NULL;
		}
	}

	if (page) {
		if (page->index <= end_idx)
			found = true;
		put_page(page);
	}

	rcu_read_unlock();
	return found;
}
static int lock_extent_direct(struct inode *inode, u64 lockstart, u64 lockend,
			      struct extent_state **cached_state, int writing)
{
	struct btrfs_ordered_extent *ordered;
	int ret = 0;

	while (1) {
		lock_extent_bits(&BTRFS_I(inode)->io_tree, lockstart, lockend,
				 cached_state);
		/*
		 * We're concerned with the entire range that we're going to be
		 * doing DIO to, so we need to make sure there's no ordered
		 * extents in this range.
		 */
		ordered = btrfs_lookup_ordered_range(BTRFS_I(inode), lockstart,
						     lockend - lockstart + 1);

		/*
		 * We need to make sure there are no buffered pages in this
		 * range either, we could have raced between the invalidate in
		 * generic_file_direct_write and locking the extent.  The
		 * invalidate needs to happen so that reads after a write do not
		 * get stale data.
		 */
		if (!ordered &&
		    (!writing ||
		     !btrfs_page_exists_in_range(inode, lockstart, lockend)))
			break;

		unlock_extent_cached(&BTRFS_I(inode)->io_tree, lockstart, lockend,
				     cached_state, GFP_NOFS);

		if (ordered) {
			/*
			 * If we are doing a DIO read and the ordered extent we
			 * found is for a buffered write, we can not wait for it
			 * to complete and retry, because if we do so we can
			 * deadlock with concurrent buffered writes on page
			 * locks. This happens only if our DIO read covers more
			 * than one extent map, if at this point has already
			 * created an ordered extent for a previous extent map
			 * and locked its range in the inode's io tree, and a
			 * concurrent write against that previous extent map's
			 * range and this range started (we unlock the ranges
			 * in the io tree only when the bios complete and
			 * buffered writes always lock pages before attempting
			 * to lock range in the io tree).
			 */
			if (writing ||
			    test_bit(BTRFS_ORDERED_DIRECT, &ordered->flags))
				btrfs_start_ordered_extent(inode, ordered, 1);
			else
				ret = -ENOTBLK;
			btrfs_put_ordered_extent(ordered);
		} else {
			/*
			 * We could trigger writeback for this range (and wait
			 * for it to complete) and then invalidate the pages for
			 * this range (through invalidate_inode_pages2_range()),
			 * but that can lead us to a deadlock with a concurrent
			 * call to readpages() (a buffered read or a defrag call
			 * triggered a readahead) on a page lock due to an
			 * ordered dio extent we created before but did not have
			 * yet a corresponding bio submitted (whence it can not
			 * complete), which makes readpages() wait for that
			 * ordered extent to complete while holding a lock on
			 * that page.
			 */
			ret = -ENOTBLK;
		}

		if (ret)
			break;

		cond_resched();
	}

	return ret;
}
				       u64 ram_bytes, int compress_type,
				       int type)
{
	struct extent_map_tree *em_tree;
	struct extent_map *em;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	int ret;

	ASSERT(type == BTRFS_ORDERED_PREALLOC ||
	       type == BTRFS_ORDERED_COMPRESSED ||
	       type == BTRFS_ORDERED_NOCOW ||
	       type == BTRFS_ORDERED_REGULAR);

	em_tree = &BTRFS_I(inode)->extent_tree;
	em = alloc_extent_map();
	if (!em)
		return ERR_PTR(-ENOMEM);

	em->start = start;
	em->orig_start = orig_start;
	em->len = len;
	em->block_len = block_len;
	em->block_start = block_start;
	em->bdev = root->fs_info->fs_devices->latest_bdev;
	em->orig_block_len = orig_block_len;
	em->ram_bytes = ram_bytes;
	em->generation = -1;
	set_bit(EXTENT_FLAG_PINNED, &em->flags);
	if (type == BTRFS_ORDERED_PREALLOC) {
		set_bit(EXTENT_FLAG_FILLING, &em->flags);
	} else if (type == BTRFS_ORDERED_COMPRESSED) {
		set_bit(EXTENT_FLAG_COMPRESSED, &em->flags);
		em->compress_type = compress_type;
	}

	do {
		btrfs_drop_extent_cache(BTRFS_I(inode), em->start,
				em->start + em->len - 1, 0);
		write_lock(&em_tree->lock);
		ret = add_extent_mapping(em_tree, em, 1);
		write_unlock(&em_tree->lock);
		/*
		 * The caller has taken lock_extent(), who could race with us
		 * to add em?
		 */
	} while (ret == -EEXIST);

	if (ret) {
		free_extent_map(em);
		return ERR_PTR(ret);
	}

	/* em got 2 refs now, callers needs to do free_extent_map once. */
	return em;
}
			       struct kiocb *iocb,
			       const struct iov_iter *iter, loff_t offset)
{
	int seg;
	int i;
	unsigned int blocksize_mask = fs_info->sectorsize - 1;
	ssize_t retval = -EINVAL;

	if (offset & blocksize_mask)
		goto out;

	if (iov_iter_alignment(iter) & blocksize_mask)
		goto out;

	/* If this is a write we don't need to check anymore */
	if (iov_iter_rw(iter) != READ || !iter_is_iovec(iter))
		return 0;
	/*
	 * Check to make sure we don't have duplicate iov_base's in this
	 * iovec, if so return EINVAL, otherwise we'll get csum errors
	 * when reading back.
	 */
	for (seg = 0; seg < iter->nr_segs; seg++) {
		for (i = seg + 1; i < iter->nr_segs; i++) {
			if (iter->iov[seg].iov_base == iter->iov[i].iov_base)
				goto out;
		}
	}
	retval = 0;
out:
	return retval;
}

static int btrfs_truncate(struct inode *inode)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_block_rsv *rsv;
	int ret = 0;
	int err = 0;
	struct btrfs_trans_handle *trans;
	u64 mask = fs_info->sectorsize - 1;
	u64 min_size = btrfs_calc_trunc_metadata_size(fs_info, 1);

	ret = btrfs_wait_ordered_range(inode, inode->i_size & (~mask),
				       (u64)-1);
	if (ret)
		return ret;

	/*
	 * Yes ladies and gentlemen, this is indeed ugly.  The fact is we have
	 * 3 things going on here
	 *
	 * 1) We need to reserve space for our orphan item and the space to
	 * delete our orphan item.  Lord knows we don't want to have a dangling
	 * orphan item because we didn't reserve space to remove it.
	 *
	 * 2) We need to reserve space to update our inode.
	 *
	 * 3) We need to have something to cache all the space that is going to
	 * be free'd up by the truncate operation, but also have some slack
	 * space reserved in case it uses space during the truncate (thank you
	 * very much snapshotting).
	 *
	 * And we need these to all be separate.  The fact is we can use a lot of
	 * space doing the truncate, and we have no earthly idea how much space
	 * we will use, so we need the truncate reservation to be separate so it
	 * doesn't end up using space reserved for updating the inode or
	 * removing the orphan item.  We also need to be able to stop the
	 * transaction and start a new one, which means we need to be able to
	 * update the inode several times, and we have no idea of knowing how
	 * many times that will be, so we can't just reserve 1 item for the
	 * entirety of the operation, so that has to be done separately as well.
	 * Then there is the orphan item, which does indeed need to be held on
	 * to for the whole operation, and we need nobody to touch this reserved
	 * space except the orphan code.
	 *
	 * So that leaves us with
	 *
	 * 1) root->orphan_block_rsv - for the orphan deletion.
	 * 2) rsv - for the truncate reservation, which we will steal from the
	 * transaction reservation.
	 * 3) fs_info->trans_block_rsv - this will have 1 items worth left for
	 * updating the inode.
	 */
	rsv = btrfs_alloc_block_rsv(fs_info, BTRFS_BLOCK_RSV_TEMP);
	if (!rsv)
		return -ENOMEM;
	rsv->size = min_size;
	rsv->failfast = 1;

	/*
	 * 1 for the truncate slack space
	 * 1 for updating the inode.
	 */
	trans = btrfs_start_transaction(root, 2);
	if (IS_ERR(trans)) {
		err = PTR_ERR(trans);
		goto out;
	}

	/* Migrate the slack space for the truncate to our reserve */
	ret = btrfs_block_rsv_migrate(&fs_info->trans_block_rsv, rsv,
				      min_size, 0);
	BUG_ON(ret);

	/*
	 * So if we truncate and then write and fsync we normally would just
	 * write the extents that changed, which is a problem if we need to
	 * first truncate that entire inode.  So set this flag so we write out
	 * all of the extents in the inode to the sync log so we're completely
	 * safe.
	 */
	set_bit(BTRFS_INODE_NEEDS_FULL_SYNC, &BTRFS_I(inode)->runtime_flags);
	trans->block_rsv = rsv;

	while (1) {
		ret = btrfs_truncate_inode_items(trans, root, inode,
						 inode->i_size,
						 BTRFS_EXTENT_DATA_KEY);
		if (ret != -ENOSPC && ret != -EAGAIN) {
			err = ret;
			break;
		}

		trans->block_rsv = &fs_info->trans_block_rsv;
		ret = btrfs_update_inode(trans, root, inode);
		if (ret) {
			err = ret;
			break;
		}

		btrfs_end_transaction(trans);
		btrfs_btree_balance_dirty(fs_info);

		trans = btrfs_start_transaction(root, 2);
		if (IS_ERR(trans)) {
			ret = err = PTR_ERR(trans);
			trans = NULL;
			break;
		}

		btrfs_block_rsv_release(fs_info, rsv, -1);
		ret = btrfs_block_rsv_migrate(&fs_info->trans_block_rsv,
					      rsv, min_size, 0);
		BUG_ON(ret);	/* shouldn't happen */
		trans->block_rsv = rsv;
	}

	if (ret == 0 && inode->i_nlink > 0) {
		trans->block_rsv = root->orphan_block_rsv;
		ret = btrfs_orphan_del(trans, BTRFS_I(inode));
		if (ret)
			err = ret;
	}

	if (trans) {
		trans->block_rsv = &fs_info->trans_block_rsv;
		ret = btrfs_update_inode(trans, root, inode);
		if (ret && !err)
			err = ret;

		ret = btrfs_end_transaction(trans);
		btrfs_btree_balance_dirty(fs_info);
	}
out:
	btrfs_free_block_rsv(fs_info, rsv);

	if (ret && !err)
		err = ret;

	return err;
}

void btrfs_destroy_inode(struct inode *inode)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_ordered_extent *ordered;
	struct btrfs_root *root = BTRFS_I(inode)->root;

	WARN_ON(!hlist_empty(&inode->i_dentry));
	WARN_ON(inode->i_data.nrpages);
	WARN_ON(BTRFS_I(inode)->outstanding_extents);
	WARN_ON(BTRFS_I(inode)->reserved_extents);
	WARN_ON(BTRFS_I(inode)->delalloc_bytes);
	WARN_ON(BTRFS_I(inode)->new_delalloc_bytes);
	WARN_ON(BTRFS_I(inode)->csum_bytes);
	WARN_ON(BTRFS_I(inode)->defrag_bytes);

	/*
	 * This can happen where we create an inode, but somebody else also
	 * created the same inode and we need to destroy the one we already
	 * created.
	 */
	if (!root)
		goto free;

	if (test_bit(BTRFS_INODE_HAS_ORPHAN_ITEM,
		     &BTRFS_I(inode)->runtime_flags)) {
		btrfs_info(fs_info, "inode %llu still on the orphan list",
			   btrfs_ino(BTRFS_I(inode)));
		atomic_dec(&root->orphan_inodes);
	}

	while (1) {
		ordered = btrfs_lookup_first_ordered_extent(inode, (u64)-1);
		if (!ordered)
			break;
		else {
			btrfs_err(fs_info,
				  "found ordered extent %llu %llu on inode cleanup",
				  ordered->file_offset, ordered->len);
			btrfs_remove_ordered_extent(inode, ordered);
			btrfs_put_ordered_extent(ordered);
			btrfs_put_ordered_extent(ordered);
		}
	}
	btrfs_qgroup_check_reserved_leak(inode);
	inode_tree_del(inode);
	btrfs_drop_extent_cache(BTRFS_I(inode), 0, (u64)-1, 0);
free:
	call_rcu(&inode->i_rcu, btrfs_i_callback);
}
static int __start_delalloc_inodes(struct btrfs_root *root, int delay_iput,
				   int nr)
{
	struct btrfs_inode *binode;
	struct inode *inode;
	struct btrfs_delalloc_work *work, *next;
	struct list_head works;
	struct list_head splice;
	int ret = 0;

	INIT_LIST_HEAD(&works);
	INIT_LIST_HEAD(&splice);

	mutex_lock(&root->delalloc_mutex);
	spin_lock(&root->delalloc_lock);
	list_splice_init(&root->delalloc_inodes, &splice);
	while (!list_empty(&splice)) {
		binode = list_entry(splice.next, struct btrfs_inode,
				    delalloc_inodes);

		list_move_tail(&binode->delalloc_inodes,
			       &root->delalloc_inodes);
		inode = igrab(&binode->vfs_inode);
		if (!inode) {
			cond_resched_lock(&root->delalloc_lock);
			continue;
		}
		spin_unlock(&root->delalloc_lock);

		work = btrfs_alloc_delalloc_work(inode, delay_iput);
		if (!work) {
			if (delay_iput)
				btrfs_add_delayed_iput(inode);
			else
				iput(inode);
			ret = -ENOMEM;
			goto out;
		}
		list_add_tail(&work->list, &works);
		btrfs_queue_work(root->fs_info->flush_workers,
				 &work->work);
		ret++;
		if (nr != -1 && ret >= nr)
			goto out;
		cond_resched();
		spin_lock(&root->delalloc_lock);
	}
	spin_unlock(&root->delalloc_lock);

out:
	list_for_each_entry_safe(work, next, &works, list) {
		list_del_init(&work->list);
		btrfs_wait_and_free_delalloc_work(work);
	}

	if (!list_empty_careful(&splice)) {
		spin_lock(&root->delalloc_lock);
		list_splice_tail(&splice, &root->delalloc_inodes);
		spin_unlock(&root->delalloc_lock);
	}
	mutex_unlock(&root->delalloc_mutex);
	return ret;
}

int btrfs_start_delalloc_inodes(struct btrfs_root *root, int delay_iput)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret;

	if (test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state))
		return -EROFS;

	ret = __start_delalloc_inodes(root, delay_iput, -1);
	if (ret > 0)
		ret = 0;
	/*
	 * the filemap_flush will queue IO into the worker threads, but
	 * we have to make sure the IO is actually started and that
	 * ordered extents get created before we return
	 */
	atomic_inc(&fs_info->async_submit_draining);
	while (atomic_read(&fs_info->nr_async_submits) ||
	       atomic_read(&fs_info->async_delalloc_pages)) {
		wait_event(fs_info->async_submit_wait,
			   (atomic_read(&fs_info->nr_async_submits) == 0 &&
			    atomic_read(&fs_info->async_delalloc_pages) == 0));
	}
	atomic_dec(&fs_info->async_submit_draining);
	return ret;
}
int btrfs_start_delalloc_roots(struct btrfs_fs_info *fs_info, int delay_iput,
			       int nr)
{
	struct btrfs_root *root;
	struct list_head splice;
	int ret;

	if (test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state))
		return -EROFS;

	INIT_LIST_HEAD(&splice);

	mutex_lock(&fs_info->delalloc_root_mutex);
	spin_lock(&fs_info->delalloc_root_lock);
	list_splice_init(&fs_info->delalloc_roots, &splice);
	while (!list_empty(&splice) && nr) {
		root = list_first_entry(&splice, struct btrfs_root,
					delalloc_root);
		root = btrfs_grab_fs_root(root);
		BUG_ON(!root);
		list_move_tail(&root->delalloc_root,
			       &fs_info->delalloc_roots);
		spin_unlock(&fs_info->delalloc_root_lock);

		ret = __start_delalloc_inodes(root, delay_iput, nr);
		btrfs_put_fs_root(root);
		if (ret < 0)
			goto out;

		if (nr != -1) {
			nr -= ret;
			WARN_ON(nr < 0);
		}
		spin_lock(&fs_info->delalloc_root_lock);
	}
	spin_unlock(&fs_info->delalloc_root_lock);

	ret = 0;
	atomic_inc(&fs_info->async_submit_draining);
	while (atomic_read(&fs_info->nr_async_submits) ||
	      atomic_read(&fs_info->async_delalloc_pages)) {
		wait_event(fs_info->async_submit_wait,
		   (atomic_read(&fs_info->nr_async_submits) == 0 &&
		    atomic_read(&fs_info->async_delalloc_pages) == 0));
	}
	atomic_dec(&fs_info->async_submit_draining);
out:
	if (!list_empty_careful(&splice)) {
		spin_lock(&fs_info->delalloc_root_lock);
		list_splice_tail(&splice, &fs_info->delalloc_roots);
		spin_unlock(&fs_info->delalloc_root_lock);
	}
	mutex_unlock(&fs_info->delalloc_root_mutex);
	return ret;
}
				       loff_t actual_len, u64 *alloc_hint,
				       struct btrfs_trans_handle *trans)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct extent_map_tree *em_tree = &BTRFS_I(inode)->extent_tree;
	struct extent_map *em;
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct btrfs_key ins;
	u64 cur_offset = start;
	u64 i_size;
	u64 cur_bytes;
	u64 last_alloc = (u64)-1;
	int ret = 0;
	bool own_trans = true;
	u64 end = start + num_bytes - 1;

	if (trans)
		own_trans = false;
	while (num_bytes > 0) {
		if (own_trans) {
			trans = btrfs_start_transaction(root, 3);
			if (IS_ERR(trans)) {
				ret = PTR_ERR(trans);
				break;
			}
		}

		cur_bytes = min_t(u64, num_bytes, SZ_256M);
		cur_bytes = max(cur_bytes, min_size);
		/*
		 * If we are severely fragmented we could end up with really
		 * small allocations, so if the allocator is returning small
		 * chunks lets make its job easier by only searching for those
		 * sized chunks.
		 */
		cur_bytes = min(cur_bytes, last_alloc);
		ret = btrfs_reserve_extent(root, cur_bytes, cur_bytes,
				min_size, 0, *alloc_hint, &ins, 1, 0);
		if (ret) {
			if (own_trans)
				btrfs_end_transaction(trans);
			break;
		}
		btrfs_dec_block_group_reservations(fs_info, ins.objectid);

		last_alloc = ins.offset;
		ret = insert_reserved_file_extent(trans, inode,
						  cur_offset, ins.objectid,
						  ins.offset, ins.offset,
						  ins.offset, 0, 0, 0,
						  BTRFS_FILE_EXTENT_PREALLOC);
		if (ret) {
			btrfs_free_reserved_extent(fs_info, ins.objectid,
						   ins.offset, 0);
			btrfs_abort_transaction(trans, ret);
			if (own_trans)
				btrfs_end_transaction(trans);
			break;
		}

		btrfs_drop_extent_cache(BTRFS_I(inode), cur_offset,
					cur_offset + ins.offset -1, 0);

		em = alloc_extent_map();
		if (!em) {
			set_bit(BTRFS_INODE_NEEDS_FULL_SYNC,
				&BTRFS_I(inode)->runtime_flags);
			goto next;
		}

		em->start = cur_offset;
		em->orig_start = cur_offset;
		em->len = ins.offset;
		em->block_start = ins.objectid;
		em->block_len = ins.offset;
		em->orig_block_len = ins.offset;
		em->ram_bytes = ins.offset;
		em->bdev = fs_info->fs_devices->latest_bdev;
		set_bit(EXTENT_FLAG_PREALLOC, &em->flags);
		em->generation = trans->transid;

		while (1) {
			write_lock(&em_tree->lock);
			ret = add_extent_mapping(em_tree, em, 1);
			write_unlock(&em_tree->lock);
			if (ret != -EEXIST)
				break;
			btrfs_drop_extent_cache(BTRFS_I(inode), cur_offset,
						cur_offset + ins.offset - 1,
						0);
		}
		free_extent_map(em);
next:
		num_bytes -= ins.offset;
		cur_offset += ins.offset;
		*alloc_hint = ins.objectid + ins.offset;

		inode_inc_iversion(inode);
		inode->i_ctime = current_time(inode);
		BTRFS_I(inode)->flags |= BTRFS_INODE_PREALLOC;
		if (!(mode & FALLOC_FL_KEEP_SIZE) &&
		    (actual_len > inode->i_size) &&
		    (cur_offset > inode->i_size)) {
			if (cur_offset > actual_len)
				i_size = actual_len;
			else
				i_size = cur_offset;
			i_size_write(inode, i_size);
			btrfs_ordered_update_i_size(inode, i_size, NULL);
		}

		ret = btrfs_update_inode(trans, root, inode);

		if (ret) {
			btrfs_abort_transaction(trans, ret);
			if (own_trans)
				btrfs_end_transaction(trans);
			break;
		}

		if (own_trans)
			btrfs_end_transaction(trans);
	}
	if (cur_offset < end)
		btrfs_free_reserved_data_space(inode, cur_offset,
			end - cur_offset + 1);
	return ret;
}
