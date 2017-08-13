
static void btrfsic_block_hashtable_init(struct btrfsic_block_hashtable *h)
{
	int i;

	for (i = 0; i < BTRFSIC_BLOCK_HASHTABLE_SIZE; i++)
		INIT_LIST_HEAD(h->table + i);
}
static void btrfsic_block_link_hashtable_init(
		struct btrfsic_block_link_hashtable *h)
{
	int i;

	for (i = 0; i < BTRFSIC_BLOCK_LINK_HASHTABLE_SIZE; i++)
		INIT_LIST_HEAD(h->table + i);
}
static void btrfsic_dev_state_hashtable_init(
		struct btrfsic_dev_state_hashtable *h)
{
	int i;

	for (i = 0; i < BTRFSIC_DEV2STATE_HASHTABLE_SIZE; i++)
		INIT_LIST_HEAD(h->table + i);
}
static int btrfsic_process_superblock(struct btrfsic_state *state,
				      struct btrfs_fs_devices *fs_devices)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	struct btrfs_super_block *selected_super;
	struct list_head *dev_head = &fs_devices->devices;
	struct btrfs_device *device;
	struct btrfsic_dev_state *selected_dev_state = NULL;
	int ret = 0;
	int pass;

	BUG_ON(NULL == state);
	selected_super = kzalloc(sizeof(*selected_super), GFP_NOFS);
	if (NULL == selected_super) {
		pr_info("btrfsic: error, kmalloc failed!\n");
		return -ENOMEM;
	}

	list_for_each_entry(device, dev_head, dev_list) {
		int i;
		struct btrfsic_dev_state *dev_state;

		if (!device->bdev || !device->name)
			continue;

		dev_state = btrfsic_dev_state_lookup(device->bdev);
		BUG_ON(NULL == dev_state);
		for (i = 0; i < BTRFS_SUPER_MIRROR_MAX; i++) {
			ret = btrfsic_process_superblock_dev_mirror(
					state, dev_state, device, i,
					&selected_dev_state, selected_super);
			if (0 != ret && 0 == i) {
				kfree(selected_super);
				return ret;
			}
		}
	}

	if (NULL == state->latest_superblock) {
		pr_info("btrfsic: no superblock found!\n");
		kfree(selected_super);
		return -1;
	}

	state->csum_size = btrfs_super_csum_size(selected_super);

	for (pass = 0; pass < 3; pass++) {
		int num_copies;
		int mirror_num;
		u64 next_bytenr;

		switch (pass) {
		case 0:
			next_bytenr = btrfs_super_root(selected_super);
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("root@%llu\n", next_bytenr);
			break;
		case 1:
			next_bytenr = btrfs_super_chunk_root(selected_super);
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("chunk@%llu\n", next_bytenr);
			break;
		case 2:
			next_bytenr = btrfs_super_log_root(selected_super);
			if (0 == next_bytenr)
				continue;
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("log@%llu\n", next_bytenr);
			break;
		}

		num_copies = btrfs_num_copies(fs_info, next_bytenr,
					      state->metablock_size);
		if (state->print_mask & BTRFSIC_PRINT_MASK_NUM_COPIES)
			pr_info("num_copies(log_bytenr=%llu) = %d\n",
			       next_bytenr, num_copies);

		for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
			struct btrfsic_block *next_block;
			struct btrfsic_block_data_ctx tmp_next_block_ctx;
			struct btrfsic_block_link *l;

			ret = btrfsic_map_block(state, next_bytenr,
						state->metablock_size,
						&tmp_next_block_ctx,
						mirror_num);
			if (ret) {
				pr_info("btrfsic: btrfsic_map_block(root @%llu, mirror %d) failed!\n",
				       next_bytenr, mirror_num);
				kfree(selected_super);
				return -1;
			}

			next_block = btrfsic_block_hashtable_lookup(
					tmp_next_block_ctx.dev->bdev,
					tmp_next_block_ctx.dev_bytenr,
					&state->block_hashtable);
			BUG_ON(NULL == next_block);

			l = btrfsic_block_link_hashtable_lookup(
					tmp_next_block_ctx.dev->bdev,
					tmp_next_block_ctx.dev_bytenr,
					state->latest_superblock->dev_state->
					bdev,
					state->latest_superblock->dev_bytenr,
					&state->block_link_hashtable);
			BUG_ON(NULL == l);

			ret = btrfsic_read_block(state, &tmp_next_block_ctx);
			if (ret < (int)PAGE_SIZE) {
				pr_info("btrfsic: read @logical %llu failed!\n",
				       tmp_next_block_ctx.start);
				btrfsic_release_block_ctx(&tmp_next_block_ctx);
				kfree(selected_super);
				return -1;
			}

			ret = btrfsic_process_metablock(state,
							next_block,
							&tmp_next_block_ctx,
							BTRFS_MAX_LEVEL + 3, 1);
			btrfsic_release_block_ctx(&tmp_next_block_ctx);
		}
	}

	kfree(selected_super);
	return ret;
}
		struct btrfsic_dev_state **selected_dev_state,
		struct btrfs_super_block *selected_super)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	struct btrfs_super_block *super_tmp;
	u64 dev_bytenr;
	struct buffer_head *bh;
	struct btrfsic_block *superblock_tmp;
	int pass;
	struct block_device *const superblock_bdev = device->bdev;

	/* super block bytenr is always the unmapped device bytenr */
	dev_bytenr = btrfs_sb_offset(superblock_mirror_num);
	if (dev_bytenr + BTRFS_SUPER_INFO_SIZE > device->commit_total_bytes)
		return -1;
	bh = __bread(superblock_bdev, dev_bytenr / 4096,
		     BTRFS_SUPER_INFO_SIZE);
	if (NULL == bh)
		return -1;
	super_tmp = (struct btrfs_super_block *)
	    (bh->b_data + (dev_bytenr & 4095));

	if (btrfs_super_bytenr(super_tmp) != dev_bytenr ||
	    btrfs_super_magic(super_tmp) != BTRFS_MAGIC ||
	    memcmp(device->uuid, super_tmp->dev_item.uuid, BTRFS_UUID_SIZE) ||
	    btrfs_super_nodesize(super_tmp) != state->metablock_size ||
	    btrfs_super_sectorsize(super_tmp) != state->datablock_size) {
		brelse(bh);
		return 0;
	}

	superblock_tmp =
	    btrfsic_block_hashtable_lookup(superblock_bdev,
					   dev_bytenr,
					   &state->block_hashtable);
	if (NULL == superblock_tmp) {
		superblock_tmp = btrfsic_block_alloc();
		if (NULL == superblock_tmp) {
			pr_info("btrfsic: error, kmalloc failed!\n");
			brelse(bh);
			return -1;
		}
		/* for superblock, only the dev_bytenr makes sense */
		superblock_tmp->dev_bytenr = dev_bytenr;
		superblock_tmp->dev_state = dev_state;
		superblock_tmp->logical_bytenr = dev_bytenr;
		superblock_tmp->generation = btrfs_super_generation(super_tmp);
		superblock_tmp->is_metadata = 1;
		superblock_tmp->is_superblock = 1;
		superblock_tmp->is_iodone = 1;
		superblock_tmp->never_written = 0;
		superblock_tmp->mirror_num = 1 + superblock_mirror_num;
		if (state->print_mask & BTRFSIC_PRINT_MASK_SUPERBLOCK_WRITE)
			btrfs_info_in_rcu(fs_info,
				"new initial S-block (bdev %p, %s) @%llu (%s/%llu/%d)",
				     superblock_bdev,
				     rcu_str_deref(device->name), dev_bytenr,
				     dev_state->name, dev_bytenr,
				     superblock_mirror_num);
		list_add(&superblock_tmp->all_blocks_node,
			 &state->all_blocks_list);
		btrfsic_block_hashtable_add(superblock_tmp,
					    &state->block_hashtable);
	}

	/* select the one with the highest generation field */
	if (btrfs_super_generation(super_tmp) >
	    state->max_superblock_generation ||
	    0 == state->max_superblock_generation) {
		memcpy(selected_super, super_tmp, sizeof(*selected_super));
		*selected_dev_state = dev_state;
		state->max_superblock_generation =
		    btrfs_super_generation(super_tmp);
		state->latest_superblock = superblock_tmp;
	}

	for (pass = 0; pass < 3; pass++) {
		u64 next_bytenr;
		int num_copies;
		int mirror_num;
		const char *additional_string = NULL;
		struct btrfs_disk_key tmp_disk_key;

		tmp_disk_key.type = BTRFS_ROOT_ITEM_KEY;
		tmp_disk_key.offset = 0;
		switch (pass) {
		case 0:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_ROOT_TREE_OBJECTID);
			additional_string = "initial root ";
			next_bytenr = btrfs_super_root(super_tmp);
			break;
		case 1:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_CHUNK_TREE_OBJECTID);
			additional_string = "initial chunk ";
			next_bytenr = btrfs_super_chunk_root(super_tmp);
			break;
		case 2:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_TREE_LOG_OBJECTID);
			additional_string = "initial log ";
			next_bytenr = btrfs_super_log_root(super_tmp);
			if (0 == next_bytenr)
				continue;
			break;
		}

		num_copies = btrfs_num_copies(fs_info, next_bytenr,
					      state->metablock_size);
		if (state->print_mask & BTRFSIC_PRINT_MASK_NUM_COPIES)
			pr_info("num_copies(log_bytenr=%llu) = %d\n",
			       next_bytenr, num_copies);
		for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
			struct btrfsic_block *next_block;
			struct btrfsic_block_data_ctx tmp_next_block_ctx;
			struct btrfsic_block_link *l;

			if (btrfsic_map_block(state, next_bytenr,
					      state->metablock_size,
					      &tmp_next_block_ctx,
					      mirror_num)) {
				pr_info("btrfsic: btrfsic_map_block(bytenr @%llu, mirror %d) failed!\n",
				       next_bytenr, mirror_num);
				brelse(bh);
				return -1;
			}

			next_block = btrfsic_block_lookup_or_add(
					state, &tmp_next_block_ctx,
					additional_string, 1, 1, 0,
					mirror_num, NULL);
			if (NULL == next_block) {
				btrfsic_release_block_ctx(&tmp_next_block_ctx);
				brelse(bh);
				return -1;
			}

			next_block->disk_key = tmp_disk_key;
			next_block->generation = BTRFSIC_GENERATION_UNKNOWN;
			l = btrfsic_block_link_lookup_or_add(
					state, &tmp_next_block_ctx,
					next_block, superblock_tmp,
					BTRFSIC_GENERATION_UNKNOWN);
			btrfsic_release_block_ctx(&tmp_next_block_ctx);
			if (NULL == l) {
				brelse(bh);
				return -1;
			}
		}
	}
	if (state->print_mask & BTRFSIC_PRINT_MASK_INITIAL_ALL_TREES)
		btrfsic_dump_tree_sub(state, superblock_tmp, 0);

	brelse(bh);
	return 0;
}
	struct btrfsic_block_data_ctx *block_ctx,
	void *dstv, u32 offset, size_t len)
{
	size_t cur;
	size_t offset_in_page;
	char *kaddr;
	char *dst = (char *)dstv;
	size_t start_offset = block_ctx->start & ((u64)PAGE_SIZE - 1);
	unsigned long i = (start_offset + offset) >> PAGE_SHIFT;

	WARN_ON(offset + len > block_ctx->len);
	offset_in_page = (start_offset + offset) & (PAGE_SIZE - 1);

	while (len > 0) {
		cur = min(len, ((size_t)PAGE_SIZE - offset_in_page));
		BUG_ON(i >= DIV_ROUND_UP(block_ctx->len, PAGE_SIZE));
		kaddr = block_ctx->datav[i];
		memcpy(dst, kaddr + offset_in_page, cur);

		dst += cur;
		len -= cur;
		offset_in_page = 0;
		i++;
	}
}
		struct btrfsic_block_data_ctx *block_ctx,
		u32 item_offset, int force_iodone_flag)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	struct btrfs_file_extent_item file_extent_item;
	u64 file_extent_item_offset;
	u64 next_bytenr;
	u64 num_bytes;
	u64 generation;
	struct btrfsic_block_link *l;
	int ret;

	file_extent_item_offset = offsetof(struct btrfs_leaf, items) +
				  item_offset;
	if (file_extent_item_offset +
	    offsetof(struct btrfs_file_extent_item, disk_num_bytes) >
	    block_ctx->len) {
		pr_info("btrfsic: file item out of bounce at logical %llu, dev %s\n",
		       block_ctx->start, block_ctx->dev->name);
		return -1;
	}

	btrfsic_read_from_block_data(block_ctx, &file_extent_item,
		file_extent_item_offset,
		offsetof(struct btrfs_file_extent_item, disk_num_bytes));
	if (BTRFS_FILE_EXTENT_REG != file_extent_item.type ||
	    btrfs_stack_file_extent_disk_bytenr(&file_extent_item) == 0) {
		if (state->print_mask & BTRFSIC_PRINT_MASK_VERY_VERBOSE)
			pr_info("extent_data: type %u, disk_bytenr = %llu\n",
			       file_extent_item.type,
			       btrfs_stack_file_extent_disk_bytenr(
			       &file_extent_item));
		return 0;
	}

	if (file_extent_item_offset + sizeof(struct btrfs_file_extent_item) >
	    block_ctx->len) {
		pr_info("btrfsic: file item out of bounce at logical %llu, dev %s\n",
		       block_ctx->start, block_ctx->dev->name);
		return -1;
	}
	btrfsic_read_from_block_data(block_ctx, &file_extent_item,
				     file_extent_item_offset,
				     sizeof(struct btrfs_file_extent_item));
	next_bytenr = btrfs_stack_file_extent_disk_bytenr(&file_extent_item);
	if (btrfs_stack_file_extent_compression(&file_extent_item) ==
	    BTRFS_COMPRESS_NONE) {
		next_bytenr += btrfs_stack_file_extent_offset(&file_extent_item);
		num_bytes = btrfs_stack_file_extent_num_bytes(&file_extent_item);
	} else {
		num_bytes = btrfs_stack_file_extent_disk_num_bytes(&file_extent_item);
	}
	generation = btrfs_stack_file_extent_generation(&file_extent_item);

	if (state->print_mask & BTRFSIC_PRINT_MASK_VERY_VERBOSE)
		pr_info("extent_data: type %u, disk_bytenr = %llu, offset = %llu, num_bytes = %llu\n",
		       file_extent_item.type,
		       btrfs_stack_file_extent_disk_bytenr(&file_extent_item),
		       btrfs_stack_file_extent_offset(&file_extent_item),
		       num_bytes);
	while (num_bytes > 0) {
		u32 chunk_len;
		int num_copies;
		int mirror_num;

		if (num_bytes > state->datablock_size)
			chunk_len = state->datablock_size;
		else
			chunk_len = num_bytes;

		num_copies = btrfs_num_copies(fs_info, next_bytenr,
					      state->datablock_size);
		if (state->print_mask & BTRFSIC_PRINT_MASK_NUM_COPIES)
			pr_info("num_copies(log_bytenr=%llu) = %d\n",
			       next_bytenr, num_copies);
		for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
			struct btrfsic_block_data_ctx next_block_ctx;
			struct btrfsic_block *next_block;
			int block_was_created;

			if (state->print_mask & BTRFSIC_PRINT_MASK_VERBOSE)
				pr_info("btrfsic_handle_extent_data(mirror_num=%d)\n",
					mirror_num);
			if (state->print_mask & BTRFSIC_PRINT_MASK_VERY_VERBOSE)
				pr_info("\tdisk_bytenr = %llu, num_bytes %u\n",
				       next_bytenr, chunk_len);
			ret = btrfsic_map_block(state, next_bytenr,
						chunk_len, &next_block_ctx,
						mirror_num);
			if (ret) {
				pr_info("btrfsic: btrfsic_map_block(@%llu, mirror=%d) failed!\n",
				       next_bytenr, mirror_num);
				return -1;
			}

			next_block = btrfsic_block_lookup_or_add(
					state,
					&next_block_ctx,
					"referenced ",
					0,
					force_iodone_flag,
					!force_iodone_flag,
					mirror_num,
					&block_was_created);
			if (NULL == next_block) {
				pr_info("btrfsic: error, kmalloc failed!\n");
				btrfsic_release_block_ctx(&next_block_ctx);
				return -1;
			}
			if (!block_was_created) {
				if ((state->print_mask &
				     BTRFSIC_PRINT_MASK_VERBOSE) &&
				    next_block->logical_bytenr != next_bytenr &&
				    !(!next_block->is_metadata &&
				      0 == next_block->logical_bytenr)) {
					pr_info("Referenced block @%llu (%s/%llu/%d) found in hash table, D, bytenr mismatch (!= stored %llu).\n",
					       next_bytenr,
					       next_block_ctx.dev->name,
					       next_block_ctx.dev_bytenr,
					       mirror_num,
					       next_block->logical_bytenr);
				}
				next_block->logical_bytenr = next_bytenr;
				next_block->mirror_num = mirror_num;
			}

			l = btrfsic_block_link_lookup_or_add(state,
							     &next_block_ctx,
							     next_block, block,
							     generation);
			btrfsic_release_block_ctx(&next_block_ctx);
			if (NULL == l)
				return -1;
		}

		next_bytenr += chunk_len;
		num_bytes -= chunk_len;
	}

	return 0;
}

static void btrfsic_release_block_ctx(struct btrfsic_block_data_ctx *block_ctx)
{
	if (block_ctx->mem_to_free) {
		unsigned int num_pages;

		BUG_ON(!block_ctx->datav);
		BUG_ON(!block_ctx->pagev);
		num_pages = (block_ctx->len + (u64)PAGE_SIZE - 1) >>
			    PAGE_SHIFT;
		while (num_pages > 0) {
			num_pages--;
			if (block_ctx->datav[num_pages]) {
				kunmap(block_ctx->pagev[num_pages]);
				block_ctx->datav[num_pages] = NULL;
			}
			if (block_ctx->pagev[num_pages]) {
				__free_page(block_ctx->pagev[num_pages]);
				block_ctx->pagev[num_pages] = NULL;
			}
		}

		kfree(block_ctx->mem_to_free);
		block_ctx->mem_to_free = NULL;
		block_ctx->pagev = NULL;
		block_ctx->datav = NULL;
	}
}
static int btrfsic_read_block(struct btrfsic_state *state,
			      struct btrfsic_block_data_ctx *block_ctx)
{
	unsigned int num_pages;
	unsigned int i;
	u64 dev_bytenr;
	int ret;

	BUG_ON(block_ctx->datav);
	BUG_ON(block_ctx->pagev);
	BUG_ON(block_ctx->mem_to_free);
	if (block_ctx->dev_bytenr & ((u64)PAGE_SIZE - 1)) {
		pr_info("btrfsic: read_block() with unaligned bytenr %llu\n",
		       block_ctx->dev_bytenr);
		return -1;
	}

	num_pages = (block_ctx->len + (u64)PAGE_SIZE - 1) >>
		    PAGE_SHIFT;
	block_ctx->mem_to_free = kzalloc((sizeof(*block_ctx->datav) +
					  sizeof(*block_ctx->pagev)) *
					 num_pages, GFP_NOFS);
	if (!block_ctx->mem_to_free)
		return -ENOMEM;
	block_ctx->datav = block_ctx->mem_to_free;
	block_ctx->pagev = (struct page **)(block_ctx->datav + num_pages);
	for (i = 0; i < num_pages; i++) {
		block_ctx->pagev[i] = alloc_page(GFP_NOFS);
		if (!block_ctx->pagev[i])
			return -1;
	}

	dev_bytenr = block_ctx->dev_bytenr;
	for (i = 0; i < num_pages;) {
		struct bio *bio;
		unsigned int j;

		bio = btrfs_io_bio_alloc(GFP_NOFS, num_pages - i);
		if (!bio) {
			pr_info("btrfsic: bio_alloc() for %u pages failed!\n",
			       num_pages - i);
			return -1;
		}
		bio->bi_bdev = block_ctx->dev->bdev;
		bio->bi_iter.bi_sector = dev_bytenr >> 9;
		bio_set_op_attrs(bio, REQ_OP_READ, 0);

		for (j = i; j < num_pages; j++) {
			ret = bio_add_page(bio, block_ctx->pagev[j],
					   PAGE_SIZE, 0);
			if (PAGE_SIZE != ret)
				break;
		}
		if (j == i) {
			pr_info("btrfsic: error, failed to add a single page!\n");
			return -1;
		}
		if (submit_bio_wait(bio)) {
			pr_info("btrfsic: read error at logical %llu dev %s!\n",
			       block_ctx->start, block_ctx->dev->name);
			bio_put(bio);
			return -1;
		}
		bio_put(bio);
		dev_bytenr += (j - i) * PAGE_SIZE;
		i = j;
	}
	for (i = 0; i < num_pages; i++) {
		block_ctx->datav[i] = kmap(block_ctx->pagev[i]);
		if (!block_ctx->datav[i]) {
			pr_info("btrfsic: kmap() failed (dev %s)!\n",
			       block_ctx->dev->name);
			return -1;
		}
	}

	return block_ctx->len;
}
static int btrfsic_test_for_metadata(struct btrfsic_state *state,
				     char **datav, unsigned int num_pages)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	struct btrfs_header *h;
	u8 csum[BTRFS_CSUM_SIZE];
	u32 crc = ~(u32)0;
	unsigned int i;

	if (num_pages * PAGE_SIZE < state->metablock_size)
		return 1; /* not metadata */
	num_pages = state->metablock_size >> PAGE_SHIFT;
	h = (struct btrfs_header *)datav[0];

	if (memcmp(h->fsid, fs_info->fsid, BTRFS_UUID_SIZE))
		return 1;

	for (i = 0; i < num_pages; i++) {
		u8 *data = i ? datav[i] : (datav[i] + BTRFS_CSUM_SIZE);
		size_t sublen = i ? PAGE_SIZE :
				    (PAGE_SIZE - BTRFS_CSUM_SIZE);

		crc = btrfs_crc32c(crc, data, sublen);
	}
	btrfs_csum_final(crc, csum);
	if (memcmp(csum, h->csum, state->csum_size))
		return 1;

	return 0; /* is metadata */
}

static void btrfsic_bio_end_io(struct bio *bp)
{
	struct btrfsic_block *block = (struct btrfsic_block *)bp->bi_private;
	int iodone_w_error;

	/* mutex is not held! This is not save if IO is not yet completed
	 * on umount */
	iodone_w_error = 0;
	if (bp->bi_error)
		iodone_w_error = 1;

	BUG_ON(NULL == block);
	bp->bi_private = block->orig_bio_bh_private;
	bp->bi_end_io = block->orig_bio_bh_end_io.bio;

	do {
		struct btrfsic_block *next_block;
		struct btrfsic_dev_state *const dev_state = block->dev_state;

		if ((dev_state->state->print_mask &
		     BTRFSIC_PRINT_MASK_END_IO_BIO_BH))
			pr_info("bio_end_io(err=%d) for %c @%llu (%s/%llu/%d)\n",
			       bp->bi_error,
			       btrfsic_get_block_type(dev_state->state, block),
			       block->logical_bytenr, dev_state->name,
			       block->dev_bytenr, block->mirror_num);
		next_block = block->next_in_same_bio;
		block->iodone_w_error = iodone_w_error;
		if (block->submit_bio_bh_rw & REQ_PREFLUSH) {
			dev_state->last_flush_gen++;
			if ((dev_state->state->print_mask &
			     BTRFSIC_PRINT_MASK_END_IO_BIO_BH))
				pr_info("bio_end_io() new %s flush_gen=%llu\n",
				       dev_state->name,
				       dev_state->last_flush_gen);
		}
		if (block->submit_bio_bh_rw & REQ_FUA)
			block->flush_gen = 0; /* FUA completed means block is
					       * on disk */
		block->is_iodone = 1; /* for FLUSH, this releases the block */
		block = next_block;
	} while (NULL != block);

	bp->bi_end_io(bp);
}
		struct btrfsic_block *const superblock,
		struct btrfs_super_block *const super_hdr)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	int pass;

	superblock->generation = btrfs_super_generation(super_hdr);
	if (!(superblock->generation > state->max_superblock_generation ||
	      0 == state->max_superblock_generation)) {
		if (state->print_mask & BTRFSIC_PRINT_MASK_SUPERBLOCK_WRITE)
			pr_info("btrfsic: superblock @%llu (%s/%llu/%d) with old gen %llu <= %llu\n",
			       superblock->logical_bytenr,
			       superblock->dev_state->name,
			       superblock->dev_bytenr, superblock->mirror_num,
			       btrfs_super_generation(super_hdr),
			       state->max_superblock_generation);
	} else {
		if (state->print_mask & BTRFSIC_PRINT_MASK_SUPERBLOCK_WRITE)
			pr_info("btrfsic: got new superblock @%llu (%s/%llu/%d) with new gen %llu > %llu\n",
			       superblock->logical_bytenr,
			       superblock->dev_state->name,
			       superblock->dev_bytenr, superblock->mirror_num,
			       btrfs_super_generation(super_hdr),
			       state->max_superblock_generation);

		state->max_superblock_generation =
		    btrfs_super_generation(super_hdr);
		state->latest_superblock = superblock;
	}

	for (pass = 0; pass < 3; pass++) {
		int ret;
		u64 next_bytenr;
		struct btrfsic_block *next_block;
		struct btrfsic_block_data_ctx tmp_next_block_ctx;
		struct btrfsic_block_link *l;
		int num_copies;
		int mirror_num;
		const char *additional_string = NULL;
		struct btrfs_disk_key tmp_disk_key = {0};

		btrfs_set_disk_key_objectid(&tmp_disk_key,
					    BTRFS_ROOT_ITEM_KEY);
		btrfs_set_disk_key_objectid(&tmp_disk_key, 0);

		switch (pass) {
		case 0:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_ROOT_TREE_OBJECTID);
			additional_string = "root ";
			next_bytenr = btrfs_super_root(super_hdr);
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("root@%llu\n", next_bytenr);
			break;
		case 1:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_CHUNK_TREE_OBJECTID);
			additional_string = "chunk ";
			next_bytenr = btrfs_super_chunk_root(super_hdr);
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("chunk@%llu\n", next_bytenr);
			break;
		case 2:
			btrfs_set_disk_key_objectid(&tmp_disk_key,
						    BTRFS_TREE_LOG_OBJECTID);
			additional_string = "log ";
			next_bytenr = btrfs_super_log_root(super_hdr);
			if (0 == next_bytenr)
				continue;
			if (state->print_mask &
			    BTRFSIC_PRINT_MASK_ROOT_CHUNK_LOG_TREE_LOCATION)
				pr_info("log@%llu\n", next_bytenr);
			break;
		}

		num_copies = btrfs_num_copies(fs_info, next_bytenr,
					      BTRFS_SUPER_INFO_SIZE);
		if (state->print_mask & BTRFSIC_PRINT_MASK_NUM_COPIES)
			pr_info("num_copies(log_bytenr=%llu) = %d\n",
			       next_bytenr, num_copies);
		for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
			int was_created;

			if (state->print_mask & BTRFSIC_PRINT_MASK_VERBOSE)
				pr_info("btrfsic_process_written_superblock(mirror_num=%d)\n", mirror_num);
			ret = btrfsic_map_block(state, next_bytenr,
						BTRFS_SUPER_INFO_SIZE,
						&tmp_next_block_ctx,
						mirror_num);
			if (ret) {
				pr_info("btrfsic: btrfsic_map_block(@%llu, mirror=%d) failed!\n",
				       next_bytenr, mirror_num);
				return -1;
			}

			next_block = btrfsic_block_lookup_or_add(
					state,
					&tmp_next_block_ctx,
					additional_string,
					1, 0, 1,
					mirror_num,
					&was_created);
			if (NULL == next_block) {
				pr_info("btrfsic: error, kmalloc failed!\n");
				btrfsic_release_block_ctx(&tmp_next_block_ctx);
				return -1;
			}

			next_block->disk_key = tmp_disk_key;
			if (was_created)
				next_block->generation =
				    BTRFSIC_GENERATION_UNKNOWN;
			l = btrfsic_block_link_lookup_or_add(
					state,
					&tmp_next_block_ctx,
					next_block,
					superblock,
					BTRFSIC_GENERATION_UNKNOWN);
			btrfsic_release_block_ctx(&tmp_next_block_ctx);
			if (NULL == l)
				return -1;
		}
	}

	if (WARN_ON(-1 == btrfsic_check_all_ref_blocks(state, superblock, 0)))
		btrfsic_dump_tree(state);

	return 0;
}
				  const struct btrfsic_block *block,
				  int indent_level)
{
	const struct btrfsic_block_link *l;
	int indent_add;
	static char buf[80];
	int cursor_position;

	/*
	 * Should better fill an on-stack buffer with a complete line and
	 * dump it at once when it is time to print a newline character.
	 */

	/*
	 * This algorithm is recursive because the amount of used stack space
	 * is very small and the max recursion depth is limited.
	 */
	indent_add = sprintf(buf, "%c-%llu(%s/%llu/%u)",
			     btrfsic_get_block_type(state, block),
			     block->logical_bytenr, block->dev_state->name,
			     block->dev_bytenr, block->mirror_num);
	if (indent_level + indent_add > BTRFSIC_TREE_DUMP_MAX_INDENT_LEVEL) {
		printk("[...]\n");
		return;
	}
	printk(buf);
	indent_level += indent_add;
	if (list_empty(&block->ref_to_list)) {
		printk("\n");
		return;
	}
	if (block->mirror_num > 1 &&
	    !(state->print_mask & BTRFSIC_PRINT_MASK_TREE_WITH_ALL_MIRRORS)) {
		printk(" [...]\n");
		return;
	}

	cursor_position = indent_level;
	list_for_each_entry(l, &block->ref_to_list, node_ref_to) {
		while (cursor_position < indent_level) {
			printk(" ");
			cursor_position++;
		}
		if (l->ref_cnt > 1)
			indent_add = sprintf(buf, " %d*--> ", l->ref_cnt);
		else
			indent_add = sprintf(buf, " --> ");
		if (indent_level + indent_add >
		    BTRFSIC_TREE_DUMP_MAX_INDENT_LEVEL) {
			printk("[...]\n");
			cursor_position = 0;
			continue;
		}

		printk(buf);

		btrfsic_dump_tree_sub(state, l->block_ref_to,
				      indent_level + indent_add);
		cursor_position = 0;
	}
}
					   struct btrfsic_dev_state *dev_state,
					   u64 dev_bytenr)
{
	struct btrfs_fs_info *fs_info = state->fs_info;
	struct btrfsic_block_data_ctx block_ctx;
	int num_copies;
	int mirror_num;
	int match = 0;
	int ret;

	num_copies = btrfs_num_copies(fs_info, bytenr, state->metablock_size);

	for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
		ret = btrfsic_map_block(state, bytenr, state->metablock_size,
					&block_ctx, mirror_num);
		if (ret) {
			pr_info("btrfsic: btrfsic_map_block(logical @%llu, mirror %d) failed!\n",
			       bytenr, mirror_num);
			continue;
		}

		if (dev_state->bdev == block_ctx.dev->bdev &&
		    dev_bytenr == block_ctx.dev_bytenr) {
			match++;
			btrfsic_release_block_ctx(&block_ctx);
			break;
		}
		btrfsic_release_block_ctx(&block_ctx);
	}

	if (WARN_ON(!match)) {
		pr_info("btrfs: attempt to write M-block which contains logical bytenr that doesn't map to dev+physical bytenr of submit_bio, buffer->log_bytenr=%llu, submit_bio(bdev=%s, phys_bytenr=%llu)!\n",
		       bytenr, dev_state->name, dev_bytenr);
		for (mirror_num = 1; mirror_num <= num_copies; mirror_num++) {
			ret = btrfsic_map_block(state, bytenr,
						state->metablock_size,
						&block_ctx, mirror_num);
			if (ret)
				continue;

			pr_info("Read logical bytenr @%llu maps to (%s/%llu/%d)\n",
			       bytenr, block_ctx.dev->name,
			       block_ctx.dev_bytenr, mirror_num);
		}
	}
}
