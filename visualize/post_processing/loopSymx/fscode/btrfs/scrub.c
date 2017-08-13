
static void __scrub_blocked_if_needed(struct btrfs_fs_info *fs_info)
{
	while (atomic_read(&fs_info->scrub_pause_req)) {
		mutex_unlock(&fs_info->scrub_lock);
		wait_event(fs_info->scrub_pause_wait,
		   atomic_read(&fs_info->scrub_pause_req) == 0);
		mutex_lock(&fs_info->scrub_lock);
	}
}
		struct btrfs_full_stripe_locks_tree *locks_root,
		u64 fstripe_logical)
{
	struct rb_node **p;
	struct rb_node *parent = NULL;
	struct full_stripe_lock *entry;
	struct full_stripe_lock *ret;

	WARN_ON(!mutex_is_locked(&locks_root->lock));

	p = &locks_root->root.rb_node;
	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct full_stripe_lock, node);
		if (fstripe_logical < entry->logical) {
			p = &(*p)->rb_left;
		} else if (fstripe_logical > entry->logical) {
			p = &(*p)->rb_right;
		} else {
			entry->refs++;
			return entry;
		}
	}

	/* Insert new lock */
	ret = kmalloc(sizeof(*ret), GFP_KERNEL);
	if (!ret)
		return ERR_PTR(-ENOMEM);
	ret->logical = fstripe_logical;
	ret->refs = 1;
	mutex_init(&ret->mutex);

	rb_link_node(&ret->node, parent, p);
	rb_insert_color(&ret->node, &locks_root->root);
	return ret;
}
		struct btrfs_full_stripe_locks_tree *locks_root,
		u64 fstripe_logical)
{
	struct rb_node *node;
	struct full_stripe_lock *entry;

	WARN_ON(!mutex_is_locked(&locks_root->lock));

	node = locks_root->root.rb_node;
	while (node) {
		entry = rb_entry(node, struct full_stripe_lock, node);
		if (fstripe_logical < entry->logical)
			node = node->rb_left;
		else if (fstripe_logical > entry->logical)
			node = node->rb_right;
		else
			return entry;
	}
	return NULL;
}

static void scrub_free_csums(struct scrub_ctx *sctx)
{
	while (!list_empty(&sctx->csum_list)) {
		struct btrfs_ordered_sum *sum;
		sum = list_first_entry(&sctx->csum_list,
				       struct btrfs_ordered_sum, list);
		list_del(&sum->list);
		kfree(sum);
	}
}

static noinline_for_stack void scrub_free_ctx(struct scrub_ctx *sctx)
{
	int i;

	if (!sctx)
		return;

	scrub_free_wr_ctx(&sctx->wr_ctx);

	/* this can happen when scrub is cancelled */
	if (sctx->curr != -1) {
		struct scrub_bio *sbio = sctx->bios[sctx->curr];

		for (i = 0; i < sbio->page_count; i++) {
			WARN_ON(!sbio->pagev[i]->page);
			scrub_block_put(sbio->pagev[i]->sblock);
		}
		bio_put(sbio->bio);
	}

	for (i = 0; i < SCRUB_BIOS_PER_SCTX; ++i) {
		struct scrub_bio *sbio = sctx->bios[i];

		if (!sbio)
			break;
		kfree(sbio);
	}

	scrub_free_csums(sctx);
	kfree(sctx);
}
static noinline_for_stack
struct scrub_ctx *scrub_setup_ctx(struct btrfs_device *dev, int is_dev_replace)
{
	struct scrub_ctx *sctx;
	int		i;
	struct btrfs_fs_info *fs_info = dev->fs_info;
	int ret;

	sctx = kzalloc(sizeof(*sctx), GFP_KERNEL);
	if (!sctx)
		goto nomem;
	refcount_set(&sctx->refs, 1);
	sctx->is_dev_replace = is_dev_replace;
	sctx->pages_per_rd_bio = SCRUB_PAGES_PER_RD_BIO;
	sctx->curr = -1;
	sctx->fs_info = dev->fs_info;
	for (i = 0; i < SCRUB_BIOS_PER_SCTX; ++i) {
		struct scrub_bio *sbio;

		sbio = kzalloc(sizeof(*sbio), GFP_KERNEL);
		if (!sbio)
			goto nomem;
		sctx->bios[i] = sbio;

		sbio->index = i;
		sbio->sctx = sctx;
		sbio->page_count = 0;
		btrfs_init_work(&sbio->work, btrfs_scrub_helper,
				scrub_bio_end_io_worker, NULL, NULL);

		if (i != SCRUB_BIOS_PER_SCTX - 1)
			sctx->bios[i]->next_free = i + 1;
		else
			sctx->bios[i]->next_free = -1;
	}
	sctx->first_free = 0;
	sctx->nodesize = fs_info->nodesize;
	sctx->sectorsize = fs_info->sectorsize;
	atomic_set(&sctx->bios_in_flight, 0);
	atomic_set(&sctx->workers_pending, 0);
	atomic_set(&sctx->cancel_req, 0);
	sctx->csum_size = btrfs_super_csum_size(fs_info->super_copy);
	INIT_LIST_HEAD(&sctx->csum_list);

	spin_lock_init(&sctx->list_lock);
	spin_lock_init(&sctx->stat_lock);
	init_waitqueue_head(&sctx->list_wait);

	ret = scrub_setup_wr_ctx(&sctx->wr_ctx,
				 fs_info->dev_replace.tgtdev, is_dev_replace);
	if (ret) {
		scrub_free_ctx(sctx);
		return ERR_PTR(ret);
	}
	return sctx;

nomem:
	scrub_free_ctx(sctx);
	return ERR_PTR(-ENOMEM);
}
static int scrub_print_warning_inode(u64 inum, u64 offset, u64 root,
				     void *warn_ctx)
{
	u64 isize;
	u32 nlink;
	int ret;
	int i;
	struct extent_buffer *eb;
	struct btrfs_inode_item *inode_item;
	struct scrub_warning *swarn = warn_ctx;
	struct btrfs_fs_info *fs_info = swarn->dev->fs_info;
	struct inode_fs_paths *ipath = NULL;
	struct btrfs_root *local_root;
	struct btrfs_key root_key;
	struct btrfs_key key;

	root_key.objectid = root;
	root_key.type = BTRFS_ROOT_ITEM_KEY;
	root_key.offset = (u64)-1;
	local_root = btrfs_read_fs_root_no_name(fs_info, &root_key);
	if (IS_ERR(local_root)) {
		ret = PTR_ERR(local_root);
		goto err;
	}

	/*
	 * this makes the path point to (inum INODE_ITEM ioff)
	 */
	key.objectid = inum;
	key.type = BTRFS_INODE_ITEM_KEY;
	key.offset = 0;

	ret = btrfs_search_slot(NULL, local_root, &key, swarn->path, 0, 0);
	if (ret) {
		btrfs_release_path(swarn->path);
		goto err;
	}

	eb = swarn->path->nodes[0];
	inode_item = btrfs_item_ptr(eb, swarn->path->slots[0],
					struct btrfs_inode_item);
	isize = btrfs_inode_size(eb, inode_item);
	nlink = btrfs_inode_nlink(eb, inode_item);
	btrfs_release_path(swarn->path);

	ipath = init_ipath(4096, local_root, swarn->path);
	if (IS_ERR(ipath)) {
		ret = PTR_ERR(ipath);
		ipath = NULL;
		goto err;
	}
	ret = paths_from_inode(inum, ipath);

	if (ret < 0)
		goto err;

	/*
	 * we deliberately ignore the bit ipath might have been too small to
	 * hold all of the paths here
	 */
	for (i = 0; i < ipath->fspath->elem_cnt; ++i)
		btrfs_warn_in_rcu(fs_info,
				  "%s at logical %llu on dev %s, sector %llu, root %llu, inode %llu, offset %llu, length %llu, links %u (path: %s)",
				  swarn->errstr, swarn->logical,
				  rcu_str_deref(swarn->dev->name),
				  (unsigned long long)swarn->sector,
				  root, inum, offset,
				  min(isize - offset, (u64)PAGE_SIZE), nlink,
				  (char *)(unsigned long)ipath->fspath->val[i]);

	free_ipath(ipath);
	return 0;

err:
	btrfs_warn_in_rcu(fs_info,
			  "%s at logical %llu on dev %s, sector %llu, root %llu, inode %llu, offset %llu: path resolving failed with ret=%d",
			  swarn->errstr, swarn->logical,
			  rcu_str_deref(swarn->dev->name),
			  (unsigned long long)swarn->sector,
			  root, inum, offset, ret);

	free_ipath(ipath);
	return 0;
}

static void scrub_print_warning(const char *errstr, struct scrub_block *sblock)
{
	struct btrfs_device *dev;
	struct btrfs_fs_info *fs_info;
	struct btrfs_path *path;
	struct btrfs_key found_key;
	struct extent_buffer *eb;
	struct btrfs_extent_item *ei;
	struct scrub_warning swarn;
	unsigned long ptr = 0;
	u64 extent_item_pos;
	u64 flags = 0;
	u64 ref_root;
	u32 item_size;
	u8 ref_level = 0;
	int ret;

	WARN_ON(sblock->page_count < 1);
	dev = sblock->pagev[0]->dev;
	fs_info = sblock->sctx->fs_info;

	path = btrfs_alloc_path();
	if (!path)
		return;

	swarn.sector = (sblock->pagev[0]->physical) >> 9;
	swarn.logical = sblock->pagev[0]->logical;
	swarn.errstr = errstr;
	swarn.dev = NULL;

	ret = extent_from_logical(fs_info, swarn.logical, path, &found_key,
				  &flags);
	if (ret < 0)
		goto out;

	extent_item_pos = swarn.logical - found_key.objectid;
	swarn.extent_item_size = found_key.offset;

	eb = path->nodes[0];
	ei = btrfs_item_ptr(eb, path->slots[0], struct btrfs_extent_item);
	item_size = btrfs_item_size_nr(eb, path->slots[0]);

	if (flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) {
		do {
			ret = tree_backref_for_extent(&ptr, eb, &found_key, ei,
						      item_size, &ref_root,
						      &ref_level);
			btrfs_warn_in_rcu(fs_info,
				"%s at logical %llu on dev %s, sector %llu: metadata %s (level %d) in tree %llu",
				errstr, swarn.logical,
				rcu_str_deref(dev->name),
				(unsigned long long)swarn.sector,
				ref_level ? "node" : "leaf",
				ret < 0 ? -1 : ref_level,
				ret < 0 ? -1 : ref_root);
		} while (ret != 1);
		btrfs_release_path(path);
	} else {
		btrfs_release_path(path);
		swarn.path = path;
		swarn.dev = dev;
		iterate_extent_inodes(fs_info, found_key.objectid,
					extent_item_pos, 1,
					scrub_print_warning_inode, &swarn);
	}

out:
	btrfs_free_path(path);
}
 */
static int scrub_handle_errored_block(struct scrub_block *sblock_to_check)
{
	struct scrub_ctx *sctx = sblock_to_check->sctx;
	struct btrfs_device *dev;
	struct btrfs_fs_info *fs_info;
	u64 length;
	u64 logical;
	unsigned int failed_mirror_index;
	unsigned int is_metadata;
	unsigned int have_csum;
	struct scrub_block *sblocks_for_recheck; /* holds one for each mirror */
	struct scrub_block *sblock_bad;
	int ret;
	int mirror_index;
	int page_num;
	int success;
	bool full_stripe_locked;
	static DEFINE_RATELIMIT_STATE(_rs, DEFAULT_RATELIMIT_INTERVAL,
				      DEFAULT_RATELIMIT_BURST);

	BUG_ON(sblock_to_check->page_count < 1);
	fs_info = sctx->fs_info;
	if (sblock_to_check->pagev[0]->flags & BTRFS_EXTENT_FLAG_SUPER) {
		/*
		 * if we find an error in a super block, we just report it.
		 * They will get written with the next transaction commit
		 * anyway
		 */
		spin_lock(&sctx->stat_lock);
		++sctx->stat.super_errors;
		spin_unlock(&sctx->stat_lock);
		return 0;
	}
	length = sblock_to_check->page_count * PAGE_SIZE;
	logical = sblock_to_check->pagev[0]->logical;
	BUG_ON(sblock_to_check->pagev[0]->mirror_num < 1);
	failed_mirror_index = sblock_to_check->pagev[0]->mirror_num - 1;
	is_metadata = !(sblock_to_check->pagev[0]->flags &
			BTRFS_EXTENT_FLAG_DATA);
	have_csum = sblock_to_check->pagev[0]->have_csum;
	dev = sblock_to_check->pagev[0]->dev;

	/*
	 * For RAID5/6, race can happen for a different device scrub thread.
	 * For data corruption, Parity and Data threads will both try
	 * to recovery the data.
	 * Race can lead to doubly added csum error, or even unrecoverable
	 * error.
	 */
	ret = lock_full_stripe(fs_info, logical, &full_stripe_locked);
	if (ret < 0) {
		spin_lock(&sctx->stat_lock);
		if (ret == -ENOMEM)
			sctx->stat.malloc_errors++;
		sctx->stat.read_errors++;
		sctx->stat.uncorrectable_errors++;
		spin_unlock(&sctx->stat_lock);
		return ret;
	}

	if (sctx->is_dev_replace && !is_metadata && !have_csum) {
		sblocks_for_recheck = NULL;
		goto nodatasum_case;
	}

	/*
	 * read all mirrors one after the other. This includes to
	 * re-read the extent or metadata block that failed (that was
	 * the cause that this fixup code is called) another time,
	 * page by page this time in order to know which pages
	 * caused I/O errors and which ones are good (for all mirrors).
	 * It is the goal to handle the situation when more than one
	 * mirror contains I/O errors, but the errors do not
	 * overlap, i.e. the data can be repaired by selecting the
	 * pages from those mirrors without I/O error on the
	 * particular pages. One example (with blocks >= 2 * PAGE_SIZE)
	 * would be that mirror #1 has an I/O error on the first page,
	 * the second page is good, and mirror #2 has an I/O error on
	 * the second page, but the first page is good.
	 * Then the first page of the first mirror can be repaired by
	 * taking the first page of the second mirror, and the
	 * second page of the second mirror can be repaired by
	 * copying the contents of the 2nd page of the 1st mirror.
	 * One more note: if the pages of one mirror contain I/O
	 * errors, the checksum cannot be verified. In order to get
	 * the best data for repairing, the first attempt is to find
	 * a mirror without I/O errors and with a validated checksum.
	 * Only if this is not possible, the pages are picked from
	 * mirrors with I/O errors without considering the checksum.
	 * If the latter is the case, at the end, the checksum of the
	 * repaired area is verified in order to correctly maintain
	 * the statistics.
	 */

	sblocks_for_recheck = kcalloc(BTRFS_MAX_MIRRORS,
				      sizeof(*sblocks_for_recheck), GFP_NOFS);
	if (!sblocks_for_recheck) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.malloc_errors++;
		sctx->stat.read_errors++;
		sctx->stat.uncorrectable_errors++;
		spin_unlock(&sctx->stat_lock);
		btrfs_dev_stat_inc_and_print(dev, BTRFS_DEV_STAT_READ_ERRS);
		goto out;
	}

	/* setup the context, map the logical blocks and alloc the pages */
	ret = scrub_setup_recheck_block(sblock_to_check, sblocks_for_recheck);
	if (ret) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.read_errors++;
		sctx->stat.uncorrectable_errors++;
		spin_unlock(&sctx->stat_lock);
		btrfs_dev_stat_inc_and_print(dev, BTRFS_DEV_STAT_READ_ERRS);
		goto out;
	}
	BUG_ON(failed_mirror_index >= BTRFS_MAX_MIRRORS);
	sblock_bad = sblocks_for_recheck + failed_mirror_index;

	/* build and submit the bios for the failed mirror, check checksums */
	scrub_recheck_block(fs_info, sblock_bad, 1);

	if (!sblock_bad->header_error && !sblock_bad->checksum_error &&
	    sblock_bad->no_io_error_seen) {
		/*
		 * the error disappeared after reading page by page, or
		 * the area was part of a huge bio and other parts of the
		 * bio caused I/O errors, or the block layer merged several
		 * read requests into one and the error is caused by a
		 * different bio (usually one of the two latter cases is
		 * the cause)
		 */
		spin_lock(&sctx->stat_lock);
		sctx->stat.unverified_errors++;
		sblock_to_check->data_corrected = 1;
		spin_unlock(&sctx->stat_lock);

		if (sctx->is_dev_replace)
			scrub_write_block_to_dev_replace(sblock_bad);
		goto out;
	}

	if (!sblock_bad->no_io_error_seen) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.read_errors++;
		spin_unlock(&sctx->stat_lock);
		if (__ratelimit(&_rs))
			scrub_print_warning("i/o error", sblock_to_check);
		btrfs_dev_stat_inc_and_print(dev, BTRFS_DEV_STAT_READ_ERRS);
	} else if (sblock_bad->checksum_error) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.csum_errors++;
		spin_unlock(&sctx->stat_lock);
		if (__ratelimit(&_rs))
			scrub_print_warning("checksum error", sblock_to_check);
		btrfs_dev_stat_inc_and_print(dev,
					     BTRFS_DEV_STAT_CORRUPTION_ERRS);
	} else if (sblock_bad->header_error) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.verify_errors++;
		spin_unlock(&sctx->stat_lock);
		if (__ratelimit(&_rs))
			scrub_print_warning("checksum/header error",
					    sblock_to_check);
		if (sblock_bad->generation_error)
			btrfs_dev_stat_inc_and_print(dev,
				BTRFS_DEV_STAT_GENERATION_ERRS);
		else
			btrfs_dev_stat_inc_and_print(dev,
				BTRFS_DEV_STAT_CORRUPTION_ERRS);
	}

	if (sctx->readonly) {
		ASSERT(!sctx->is_dev_replace);
		goto out;
	}

	if (!is_metadata && !have_csum) {
		struct scrub_fixup_nodatasum *fixup_nodatasum;

		WARN_ON(sctx->is_dev_replace);

nodatasum_case:

		/*
		 * !is_metadata and !have_csum, this means that the data
		 * might not be COWed, that it might be modified
		 * concurrently. The general strategy to work on the
		 * commit root does not help in the case when COW is not
		 * used.
		 */
		fixup_nodatasum = kzalloc(sizeof(*fixup_nodatasum), GFP_NOFS);
		if (!fixup_nodatasum)
			goto did_not_correct_error;
		fixup_nodatasum->sctx = sctx;
		fixup_nodatasum->dev = dev;
		fixup_nodatasum->logical = logical;
		fixup_nodatasum->root = fs_info->extent_root;
		fixup_nodatasum->mirror_num = failed_mirror_index + 1;
		scrub_pending_trans_workers_inc(sctx);
		btrfs_init_work(&fixup_nodatasum->work, btrfs_scrub_helper,
				scrub_fixup_nodatasum, NULL, NULL);
		btrfs_queue_work(fs_info->scrub_workers,
				 &fixup_nodatasum->work);
		goto out;
	}

	/*
	 * now build and submit the bios for the other mirrors, check
	 * checksums.
	 * First try to pick the mirror which is completely without I/O
	 * errors and also does not have a checksum error.
	 * If one is found, and if a checksum is present, the full block
	 * that is known to contain an error is rewritten. Afterwards
	 * the block is known to be corrected.
	 * If a mirror is found which is completely correct, and no
	 * checksum is present, only those pages are rewritten that had
	 * an I/O error in the block to be repaired, since it cannot be
	 * determined, which copy of the other pages is better (and it
	 * could happen otherwise that a correct page would be
	 * overwritten by a bad one).
	 */
	for (mirror_index = 0;
	     mirror_index < BTRFS_MAX_MIRRORS &&
	     sblocks_for_recheck[mirror_index].page_count > 0;
	     mirror_index++) {
		struct scrub_block *sblock_other;

		if (mirror_index == failed_mirror_index)
			continue;
		sblock_other = sblocks_for_recheck + mirror_index;

		/* build and submit the bios, check checksums */
		scrub_recheck_block(fs_info, sblock_other, 0);

		if (!sblock_other->header_error &&
		    !sblock_other->checksum_error &&
		    sblock_other->no_io_error_seen) {
			if (sctx->is_dev_replace) {
				scrub_write_block_to_dev_replace(sblock_other);
				goto corrected_error;
			} else {
				ret = scrub_repair_block_from_good_copy(
						sblock_bad, sblock_other);
				if (!ret)
					goto corrected_error;
			}
		}
	}

	if (sblock_bad->no_io_error_seen && !sctx->is_dev_replace)
		goto did_not_correct_error;

	/*
	 * In case of I/O errors in the area that is supposed to be
	 * repaired, continue by picking good copies of those pages.
	 * Select the good pages from mirrors to rewrite bad pages from
	 * the area to fix. Afterwards verify the checksum of the block
	 * that is supposed to be repaired. This verification step is
	 * only done for the purpose of statistic counting and for the
	 * final scrub report, whether errors remain.
	 * A perfect algorithm could make use of the checksum and try
	 * all possible combinations of pages from the different mirrors
	 * until the checksum verification succeeds. For example, when
	 * the 2nd page of mirror #1 faces I/O errors, and the 2nd page
	 * of mirror #2 is readable but the final checksum test fails,
	 * then the 2nd page of mirror #3 could be tried, whether now
	 * the final checksum succeeds. But this would be a rare
	 * exception and is therefore not implemented. At least it is
	 * avoided that the good copy is overwritten.
	 * A more useful improvement would be to pick the sectors
	 * without I/O error based on sector sizes (512 bytes on legacy
	 * disks) instead of on PAGE_SIZE. Then maybe 512 byte of one
	 * mirror could be repaired by taking 512 byte of a different
	 * mirror, even if other 512 byte sectors in the same PAGE_SIZE
	 * area are unreadable.
	 */
	success = 1;
	for (page_num = 0; page_num < sblock_bad->page_count;
	     page_num++) {
		struct scrub_page *page_bad = sblock_bad->pagev[page_num];
		struct scrub_block *sblock_other = NULL;

		/* skip no-io-error page in scrub */
		if (!page_bad->io_error && !sctx->is_dev_replace)
			continue;

		/* try to find no-io-error page in mirrors */
		if (page_bad->io_error) {
			for (mirror_index = 0;
			     mirror_index < BTRFS_MAX_MIRRORS &&
			     sblocks_for_recheck[mirror_index].page_count > 0;
			     mirror_index++) {
				if (!sblocks_for_recheck[mirror_index].
				    pagev[page_num]->io_error) {
					sblock_other = sblocks_for_recheck +
						       mirror_index;
					break;
				}
			}
			if (!sblock_other)
				success = 0;
		}

		if (sctx->is_dev_replace) {
			/*
			 * did not find a mirror to fetch the page
			 * from. scrub_write_page_to_dev_replace()
			 * handles this case (page->io_error), by
			 * filling the block with zeros before
			 * submitting the write request
			 */
			if (!sblock_other)
				sblock_other = sblock_bad;

			if (scrub_write_page_to_dev_replace(sblock_other,
							    page_num) != 0) {
				btrfs_dev_replace_stats_inc(
					&fs_info->dev_replace.num_write_errors);
				success = 0;
			}
		} else if (sblock_other) {
			ret = scrub_repair_page_from_good_copy(sblock_bad,
							       sblock_other,
							       page_num, 0);
			if (0 == ret)
				page_bad->io_error = 0;
			else
				success = 0;
		}
	}

	if (success && !sctx->is_dev_replace) {
		if (is_metadata || have_csum) {
			/*
			 * need to verify the checksum now that all
			 * sectors on disk are repaired (the write
			 * request for data to be repaired is on its way).
			 * Just be lazy and use scrub_recheck_block()
			 * which re-reads the data before the checksum
			 * is verified, but most likely the data comes out
			 * of the page cache.
			 */
			scrub_recheck_block(fs_info, sblock_bad, 1);
			if (!sblock_bad->header_error &&
			    !sblock_bad->checksum_error &&
			    sblock_bad->no_io_error_seen)
				goto corrected_error;
			else
				goto did_not_correct_error;
		} else {
corrected_error:
			spin_lock(&sctx->stat_lock);
			sctx->stat.corrected_errors++;
			sblock_to_check->data_corrected = 1;
			spin_unlock(&sctx->stat_lock);
			btrfs_err_rl_in_rcu(fs_info,
				"fixed up error at logical %llu on dev %s",
				logical, rcu_str_deref(dev->name));
		}
	} else {
did_not_correct_error:
		spin_lock(&sctx->stat_lock);
		sctx->stat.uncorrectable_errors++;
		spin_unlock(&sctx->stat_lock);
		btrfs_err_rl_in_rcu(fs_info,
			"unable to fixup (regular) error at logical %llu on dev %s",
			logical, rcu_str_deref(dev->name));
	}

out:
	if (sblocks_for_recheck) {
		for (mirror_index = 0; mirror_index < BTRFS_MAX_MIRRORS;
		     mirror_index++) {
			struct scrub_block *sblock = sblocks_for_recheck +
						     mirror_index;
			struct scrub_recover *recover;
			int page_index;

			for (page_index = 0; page_index < sblock->page_count;
			     page_index++) {
				sblock->pagev[page_index]->sblock = NULL;
				recover = sblock->pagev[page_index]->recover;
				if (recover) {
					scrub_put_recover(fs_info, recover);
					sblock->pagev[page_index]->recover =
									NULL;
				}
				scrub_page_put(sblock->pagev[page_index]);
			}
		}
		kfree(sblocks_for_recheck);
	}

	ret = unlock_full_stripe(fs_info, logical, full_stripe_locked);
	if (ret < 0)
		return ret;
	return 0;
}
						 int *stripe_index,
						 u64 *stripe_offset)
{
	int i;

	if (map_type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		/* RAID5/6 */
		for (i = 0; i < nstripes; i++) {
			if (raid_map[i] == RAID6_Q_STRIPE ||
			    raid_map[i] == RAID5_P_STRIPE)
				continue;

			if (logical >= raid_map[i] &&
			    logical < raid_map[i] + mapped_length)
				break;
		}

		*stripe_index = i;
		*stripe_offset = logical - raid_map[i];
	} else {
		/* The other RAID type */
		*stripe_index = mirror;
		*stripe_offset = 0;
	}
}
static int scrub_setup_recheck_block(struct scrub_block *original_sblock,
				     struct scrub_block *sblocks_for_recheck)
{
	struct scrub_ctx *sctx = original_sblock->sctx;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	u64 length = original_sblock->page_count * PAGE_SIZE;
	u64 logical = original_sblock->pagev[0]->logical;
	u64 generation = original_sblock->pagev[0]->generation;
	u64 flags = original_sblock->pagev[0]->flags;
	u64 have_csum = original_sblock->pagev[0]->have_csum;
	struct scrub_recover *recover;
	struct btrfs_bio *bbio;
	u64 sublen;
	u64 mapped_length;
	u64 stripe_offset;
	int stripe_index;
	int page_index = 0;
	int mirror_index;
	int nmirrors;
	int ret;

	/*
	 * note: the two members refs and outstanding_pages
	 * are not used (and not set) in the blocks that are used for
	 * the recheck procedure
	 */

	while (length > 0) {
		sublen = min_t(u64, length, PAGE_SIZE);
		mapped_length = sublen;
		bbio = NULL;

		/*
		 * with a length of PAGE_SIZE, each returned stripe
		 * represents one mirror
		 */
		btrfs_bio_counter_inc_blocked(fs_info);
		ret = btrfs_map_sblock(fs_info, BTRFS_MAP_GET_READ_MIRRORS,
				logical, &mapped_length, &bbio);
		if (ret || !bbio || mapped_length < sublen) {
			btrfs_put_bbio(bbio);
			btrfs_bio_counter_dec(fs_info);
			return -EIO;
		}

		recover = kzalloc(sizeof(struct scrub_recover), GFP_NOFS);
		if (!recover) {
			btrfs_put_bbio(bbio);
			btrfs_bio_counter_dec(fs_info);
			return -ENOMEM;
		}

		refcount_set(&recover->refs, 1);
		recover->bbio = bbio;
		recover->map_length = mapped_length;

		BUG_ON(page_index >= SCRUB_MAX_PAGES_PER_BLOCK);

		nmirrors = min(scrub_nr_raid_mirrors(bbio), BTRFS_MAX_MIRRORS);

		for (mirror_index = 0; mirror_index < nmirrors;
		     mirror_index++) {
			struct scrub_block *sblock;
			struct scrub_page *page;

			sblock = sblocks_for_recheck + mirror_index;
			sblock->sctx = sctx;

			page = kzalloc(sizeof(*page), GFP_NOFS);
			if (!page) {
leave_nomem:
				spin_lock(&sctx->stat_lock);
				sctx->stat.malloc_errors++;
				spin_unlock(&sctx->stat_lock);
				scrub_put_recover(fs_info, recover);
				return -ENOMEM;
			}
			scrub_page_get(page);
			sblock->pagev[page_index] = page;
			page->sblock = sblock;
			page->flags = flags;
			page->generation = generation;
			page->logical = logical;
			page->have_csum = have_csum;
			if (have_csum)
				memcpy(page->csum,
				       original_sblock->pagev[0]->csum,
				       sctx->csum_size);

			scrub_stripe_index_and_offset(logical,
						      bbio->map_type,
						      bbio->raid_map,
						      mapped_length,
						      bbio->num_stripes -
						      bbio->num_tgtdevs,
						      mirror_index,
						      &stripe_index,
						      &stripe_offset);
			page->physical = bbio->stripes[stripe_index].physical +
					 stripe_offset;
			page->dev = bbio->stripes[stripe_index].dev;

			BUG_ON(page_index >= original_sblock->page_count);
			page->physical_for_dev_replace =
				original_sblock->pagev[page_index]->
				physical_for_dev_replace;
			/* for missing devices, dev->bdev is NULL */
			page->mirror_num = mirror_index + 1;
			sblock->page_count++;
			page->page = alloc_page(GFP_NOFS);
			if (!page->page)
				goto leave_nomem;

			scrub_get_recover(recover);
			page->recover = recover;
		}
		scrub_put_recover(fs_info, recover);
		length -= sublen;
		logical += sublen;
		page_index++;
	}

	return 0;
}
				struct scrub_block *sblock,
				int retry_failed_mirror)
{
	int page_num;

	sblock->no_io_error_seen = 1;

	for (page_num = 0; page_num < sblock->page_count; page_num++) {
		struct bio *bio;
		struct scrub_page *page = sblock->pagev[page_num];

		if (page->dev->bdev == NULL) {
			page->io_error = 1;
			sblock->no_io_error_seen = 0;
			continue;
		}

		WARN_ON(!page->page);
		bio = btrfs_io_bio_alloc(GFP_NOFS, 1);
		if (!bio) {
			page->io_error = 1;
			sblock->no_io_error_seen = 0;
			continue;
		}
		bio->bi_bdev = page->dev->bdev;

		bio_add_page(bio, page->page, PAGE_SIZE, 0);
		if (!retry_failed_mirror && scrub_is_page_on_raid56(page)) {
			if (scrub_submit_raid56_bio_wait(fs_info, bio, page)) {
				page->io_error = 1;
				sblock->no_io_error_seen = 0;
			}
		} else {
			bio->bi_iter.bi_sector = page->physical >> 9;
			bio_set_op_attrs(bio, REQ_OP_READ, 0);

			if (btrfsic_submit_bio_wait(bio)) {
				page->io_error = 1;
				sblock->no_io_error_seen = 0;
			}
		}

		bio_put(bio);
	}

	if (sblock->no_io_error_seen)
		scrub_recheck_block_checksum(sblock);
}
static int scrub_repair_block_from_good_copy(struct scrub_block *sblock_bad,
					     struct scrub_block *sblock_good)
{
	int page_num;
	int ret = 0;

	for (page_num = 0; page_num < sblock_bad->page_count; page_num++) {
		int ret_sub;

		ret_sub = scrub_repair_page_from_good_copy(sblock_bad,
							   sblock_good,
							   page_num, 1);
		if (ret_sub)
			ret = ret_sub;
	}

	return ret;
}

static void scrub_write_block_to_dev_replace(struct scrub_block *sblock)
{
	struct btrfs_fs_info *fs_info = sblock->sctx->fs_info;
	int page_num;

	/*
	 * This block is used for the check of the parity on the source device,
	 * so the data needn't be written into the destination device.
	 */
	if (sblock->sparity)
		return;

	for (page_num = 0; page_num < sblock->page_count; page_num++) {
		int ret;

		ret = scrub_write_page_to_dev_replace(sblock, page_num);
		if (ret)
			btrfs_dev_replace_stats_inc(
				&fs_info->dev_replace.num_write_errors);
	}
}

static void scrub_wr_bio_end_io_worker(struct btrfs_work *work)
{
	struct scrub_bio *sbio = container_of(work, struct scrub_bio, work);
	struct scrub_ctx *sctx = sbio->sctx;
	int i;

	WARN_ON(sbio->page_count > SCRUB_PAGES_PER_WR_BIO);
	if (sbio->err) {
		struct btrfs_dev_replace *dev_replace =
			&sbio->sctx->fs_info->dev_replace;

		for (i = 0; i < sbio->page_count; i++) {
			struct scrub_page *spage = sbio->pagev[i];

			spage->io_error = 1;
			btrfs_dev_replace_stats_inc(&dev_replace->
						    num_write_errors);
		}
	}

	for (i = 0; i < sbio->page_count; i++)
		scrub_page_put(sbio->pagev[i]);

	bio_put(sbio->bio);
	kfree(sbio);
	scrub_pending_bio_dec(sctx);
}

static int scrub_checksum_data(struct scrub_block *sblock)
{
	struct scrub_ctx *sctx = sblock->sctx;
	u8 csum[BTRFS_CSUM_SIZE];
	u8 *on_disk_csum;
	struct page *page;
	void *buffer;
	u32 crc = ~(u32)0;
	u64 len;
	int index;

	BUG_ON(sblock->page_count < 1);
	if (!sblock->pagev[0]->have_csum)
		return 0;

	on_disk_csum = sblock->pagev[0]->csum;
	page = sblock->pagev[0]->page;
	buffer = kmap_atomic(page);

	len = sctx->sectorsize;
	index = 0;
	for (;;) {
		u64 l = min_t(u64, len, PAGE_SIZE);

		crc = btrfs_csum_data(buffer, crc, l);
		kunmap_atomic(buffer);
		len -= l;
		if (len == 0)
			break;
		index++;
		BUG_ON(index >= sblock->page_count);
		BUG_ON(!sblock->pagev[index]->page);
		page = sblock->pagev[index]->page;
		buffer = kmap_atomic(page);
	}

	btrfs_csum_final(crc, csum);
	if (memcmp(csum, on_disk_csum, sctx->csum_size))
		sblock->checksum_error = 1;

	return sblock->checksum_error;
}

static int scrub_checksum_tree_block(struct scrub_block *sblock)
{
	struct scrub_ctx *sctx = sblock->sctx;
	struct btrfs_header *h;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	u8 calculated_csum[BTRFS_CSUM_SIZE];
	u8 on_disk_csum[BTRFS_CSUM_SIZE];
	struct page *page;
	void *mapped_buffer;
	u64 mapped_size;
	void *p;
	u32 crc = ~(u32)0;
	u64 len;
	int index;

	BUG_ON(sblock->page_count < 1);
	page = sblock->pagev[0]->page;
	mapped_buffer = kmap_atomic(page);
	h = (struct btrfs_header *)mapped_buffer;
	memcpy(on_disk_csum, h->csum, sctx->csum_size);

	/*
	 * we don't use the getter functions here, as we
	 * a) don't have an extent buffer and
	 * b) the page is already kmapped
	 */
	if (sblock->pagev[0]->logical != btrfs_stack_header_bytenr(h))
		sblock->header_error = 1;

	if (sblock->pagev[0]->generation != btrfs_stack_header_generation(h)) {
		sblock->header_error = 1;
		sblock->generation_error = 1;
	}

	if (!scrub_check_fsid(h->fsid, sblock->pagev[0]))
		sblock->header_error = 1;

	if (memcmp(h->chunk_tree_uuid, fs_info->chunk_tree_uuid,
		   BTRFS_UUID_SIZE))
		sblock->header_error = 1;

	len = sctx->nodesize - BTRFS_CSUM_SIZE;
	mapped_size = PAGE_SIZE - BTRFS_CSUM_SIZE;
	p = ((u8 *)mapped_buffer) + BTRFS_CSUM_SIZE;
	index = 0;
	for (;;) {
		u64 l = min_t(u64, len, mapped_size);

		crc = btrfs_csum_data(p, crc, l);
		kunmap_atomic(mapped_buffer);
		len -= l;
		if (len == 0)
			break;
		index++;
		BUG_ON(index >= sblock->page_count);
		BUG_ON(!sblock->pagev[index]->page);
		page = sblock->pagev[index]->page;
		mapped_buffer = kmap_atomic(page);
		mapped_size = PAGE_SIZE;
		p = mapped_buffer;
	}

	btrfs_csum_final(crc, calculated_csum);
	if (memcmp(calculated_csum, on_disk_csum, sctx->csum_size))
		sblock->checksum_error = 1;

	return sblock->header_error || sblock->checksum_error;
}

static int scrub_checksum_super(struct scrub_block *sblock)
{
	struct btrfs_super_block *s;
	struct scrub_ctx *sctx = sblock->sctx;
	u8 calculated_csum[BTRFS_CSUM_SIZE];
	u8 on_disk_csum[BTRFS_CSUM_SIZE];
	struct page *page;
	void *mapped_buffer;
	u64 mapped_size;
	void *p;
	u32 crc = ~(u32)0;
	int fail_gen = 0;
	int fail_cor = 0;
	u64 len;
	int index;

	BUG_ON(sblock->page_count < 1);
	page = sblock->pagev[0]->page;
	mapped_buffer = kmap_atomic(page);
	s = (struct btrfs_super_block *)mapped_buffer;
	memcpy(on_disk_csum, s->csum, sctx->csum_size);

	if (sblock->pagev[0]->logical != btrfs_super_bytenr(s))
		++fail_cor;

	if (sblock->pagev[0]->generation != btrfs_super_generation(s))
		++fail_gen;

	if (!scrub_check_fsid(s->fsid, sblock->pagev[0]))
		++fail_cor;

	len = BTRFS_SUPER_INFO_SIZE - BTRFS_CSUM_SIZE;
	mapped_size = PAGE_SIZE - BTRFS_CSUM_SIZE;
	p = ((u8 *)mapped_buffer) + BTRFS_CSUM_SIZE;
	index = 0;
	for (;;) {
		u64 l = min_t(u64, len, mapped_size);

		crc = btrfs_csum_data(p, crc, l);
		kunmap_atomic(mapped_buffer);
		len -= l;
		if (len == 0)
			break;
		index++;
		BUG_ON(index >= sblock->page_count);
		BUG_ON(!sblock->pagev[index]->page);
		page = sblock->pagev[index]->page;
		mapped_buffer = kmap_atomic(page);
		mapped_size = PAGE_SIZE;
		p = mapped_buffer;
	}

	btrfs_csum_final(crc, calculated_csum);
	if (memcmp(calculated_csum, on_disk_csum, sctx->csum_size))
		++fail_cor;

	if (fail_cor + fail_gen) {
		/*
		 * if we find an error in a super block, we just report it.
		 * They will get written with the next transaction commit
		 * anyway
		 */
		spin_lock(&sctx->stat_lock);
		++sctx->stat.super_errors;
		spin_unlock(&sctx->stat_lock);
		if (fail_cor)
			btrfs_dev_stat_inc_and_print(sblock->pagev[0]->dev,
				BTRFS_DEV_STAT_CORRUPTION_ERRS);
		else
			btrfs_dev_stat_inc_and_print(sblock->pagev[0]->dev,
				BTRFS_DEV_STAT_GENERATION_ERRS);
	}

	return fail_cor + fail_gen;
}

static void scrub_block_put(struct scrub_block *sblock)
{
	if (refcount_dec_and_test(&sblock->refs)) {
		int i;

		if (sblock->sparity)
			scrub_parity_put(sblock->sparity);

		for (i = 0; i < sblock->page_count; i++)
			scrub_page_put(sblock->pagev[i]);
		kfree(sblock);
	}
}
static int scrub_add_page_to_rd_bio(struct scrub_ctx *sctx,
				    struct scrub_page *spage)
{
	struct scrub_block *sblock = spage->sblock;
	struct scrub_bio *sbio;
	int ret;

again:
	/*
	 * grab a fresh bio or wait for one to become available
	 */
	while (sctx->curr == -1) {
		spin_lock(&sctx->list_lock);
		sctx->curr = sctx->first_free;
		if (sctx->curr != -1) {
			sctx->first_free = sctx->bios[sctx->curr]->next_free;
			sctx->bios[sctx->curr]->next_free = -1;
			sctx->bios[sctx->curr]->page_count = 0;
			spin_unlock(&sctx->list_lock);
		} else {
			spin_unlock(&sctx->list_lock);
			wait_event(sctx->list_wait, sctx->first_free != -1);
		}
	}
	sbio = sctx->bios[sctx->curr];
	if (sbio->page_count == 0) {
		struct bio *bio;

		sbio->physical = spage->physical;
		sbio->logical = spage->logical;
		sbio->dev = spage->dev;
		bio = sbio->bio;
		if (!bio) {
			bio = btrfs_io_bio_alloc(GFP_KERNEL,
					sctx->pages_per_rd_bio);
			if (!bio)
				return -ENOMEM;
			sbio->bio = bio;
		}

		bio->bi_private = sbio;
		bio->bi_end_io = scrub_bio_end_io;
		bio->bi_bdev = sbio->dev->bdev;
		bio->bi_iter.bi_sector = sbio->physical >> 9;
		bio_set_op_attrs(bio, REQ_OP_READ, 0);
		sbio->err = 0;
	} else if (sbio->physical + sbio->page_count * PAGE_SIZE !=
		   spage->physical ||
		   sbio->logical + sbio->page_count * PAGE_SIZE !=
		   spage->logical ||
		   sbio->dev != spage->dev) {
		scrub_submit(sctx);
		goto again;
	}

	sbio->pagev[sbio->page_count] = spage;
	ret = bio_add_page(sbio->bio, spage->page, PAGE_SIZE, 0);
	if (ret != PAGE_SIZE) {
		if (sbio->page_count < 1) {
			bio_put(sbio->bio);
			sbio->bio = NULL;
			return -EIO;
		}
		scrub_submit(sctx);
		goto again;
	}

	scrub_block_get(sblock); /* one for the page added to the bio */
	atomic_inc(&sblock->outstanding_pages);
	sbio->page_count++;
	if (sbio->page_count == sctx->pages_per_rd_bio)
		scrub_submit(sctx);

	return 0;
}

static void scrub_missing_raid56_pages(struct scrub_block *sblock)
{
	struct scrub_ctx *sctx = sblock->sctx;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	u64 length = sblock->page_count * PAGE_SIZE;
	u64 logical = sblock->pagev[0]->logical;
	struct btrfs_bio *bbio = NULL;
	struct bio *bio;
	struct btrfs_raid_bio *rbio;
	int ret;
	int i;

	btrfs_bio_counter_inc_blocked(fs_info);
	ret = btrfs_map_sblock(fs_info, BTRFS_MAP_GET_READ_MIRRORS, logical,
			&length, &bbio);
	if (ret || !bbio || !bbio->raid_map)
		goto bbio_out;

	if (WARN_ON(!sctx->is_dev_replace ||
		    !(bbio->map_type & BTRFS_BLOCK_GROUP_RAID56_MASK))) {
		/*
		 * We shouldn't be scrubbing a missing device. Even for dev
		 * replace, we should only get here for RAID 5/6. We either
		 * managed to mount something with no mirrors remaining or
		 * there's a bug in scrub_remap_extent()/btrfs_map_block().
		 */
		goto bbio_out;
	}

	bio = btrfs_io_bio_alloc(GFP_NOFS, 0);
	if (!bio)
		goto bbio_out;

	bio->bi_iter.bi_sector = logical >> 9;
	bio->bi_private = sblock;
	bio->bi_end_io = scrub_missing_raid56_end_io;

	rbio = raid56_alloc_missing_rbio(fs_info, bio, bbio, length);
	if (!rbio)
		goto rbio_out;

	for (i = 0; i < sblock->page_count; i++) {
		struct scrub_page *spage = sblock->pagev[i];

		raid56_add_scrub_pages(rbio, spage->page, spage->logical);
	}

	btrfs_init_work(&sblock->work, btrfs_scrub_helper,
			scrub_missing_raid56_worker, NULL, NULL);
	scrub_block_get(sblock);
	scrub_pending_bio_inc(sctx);
	raid56_submit_missing_rbio(rbio);
	return;

rbio_out:
	bio_put(bio);
bbio_out:
	btrfs_bio_counter_dec(fs_info);
	btrfs_put_bbio(bbio);
	spin_lock(&sctx->stat_lock);
	sctx->stat.malloc_errors++;
	spin_unlock(&sctx->stat_lock);
}
		       u64 gen, int mirror_num, u8 *csum, int force,
		       u64 physical_for_dev_replace)
{
	struct scrub_block *sblock;
	int index;

	sblock = kzalloc(sizeof(*sblock), GFP_KERNEL);
	if (!sblock) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.malloc_errors++;
		spin_unlock(&sctx->stat_lock);
		return -ENOMEM;
	}

	/* one ref inside this function, plus one for each page added to
	 * a bio later on */
	refcount_set(&sblock->refs, 1);
	sblock->sctx = sctx;
	sblock->no_io_error_seen = 1;

	for (index = 0; len > 0; index++) {
		struct scrub_page *spage;
		u64 l = min_t(u64, len, PAGE_SIZE);

		spage = kzalloc(sizeof(*spage), GFP_KERNEL);
		if (!spage) {
leave_nomem:
			spin_lock(&sctx->stat_lock);
			sctx->stat.malloc_errors++;
			spin_unlock(&sctx->stat_lock);
			scrub_block_put(sblock);
			return -ENOMEM;
		}
		BUG_ON(index >= SCRUB_MAX_PAGES_PER_BLOCK);
		scrub_page_get(spage);
		sblock->pagev[index] = spage;
		spage->sblock = sblock;
		spage->dev = dev;
		spage->flags = flags;
		spage->generation = gen;
		spage->logical = logical;
		spage->physical = physical;
		spage->physical_for_dev_replace = physical_for_dev_replace;
		spage->mirror_num = mirror_num;
		if (csum) {
			spage->have_csum = 1;
			memcpy(spage->csum, csum, sctx->csum_size);
		} else {
			spage->have_csum = 0;
		}
		sblock->page_count++;
		spage->page = alloc_page(GFP_KERNEL);
		if (!spage->page)
			goto leave_nomem;
		len -= l;
		logical += l;
		physical += l;
		physical_for_dev_replace += l;
	}

	WARN_ON(sblock->page_count == 0);
	if (dev->missing) {
		/*
		 * This case should only be hit for RAID 5/6 device replace. See
		 * the comment in scrub_missing_raid56_pages() for details.
		 */
		scrub_missing_raid56_pages(sblock);
	} else {
		for (index = 0; index < sblock->page_count; index++) {
			struct scrub_page *spage = sblock->pagev[index];
			int ret;

			ret = scrub_add_page_to_rd_bio(sctx, spage);
			if (ret) {
				scrub_block_put(sblock);
				return ret;
			}
		}

		if (force)
			scrub_submit(sctx);
	}

	/* last one frees, either here or in bio completion for last page */
	scrub_block_put(sblock);
	return 0;
}

static void scrub_bio_end_io_worker(struct btrfs_work *work)
{
	struct scrub_bio *sbio = container_of(work, struct scrub_bio, work);
	struct scrub_ctx *sctx = sbio->sctx;
	int i;

	BUG_ON(sbio->page_count > SCRUB_PAGES_PER_RD_BIO);
	if (sbio->err) {
		for (i = 0; i < sbio->page_count; i++) {
			struct scrub_page *spage = sbio->pagev[i];

			spage->io_error = 1;
			spage->sblock->no_io_error_seen = 0;
		}
	}

	/* now complete the scrub_block items that have all pages completed */
	for (i = 0; i < sbio->page_count; i++) {
		struct scrub_page *spage = sbio->pagev[i];
		struct scrub_block *sblock = spage->sblock;

		if (atomic_dec_and_test(&sblock->outstanding_pages))
			scrub_block_complete(sblock);
		scrub_block_put(sblock);
	}

	bio_put(sbio->bio);
	sbio->bio = NULL;
	spin_lock(&sctx->list_lock);
	sbio->next_free = sctx->first_free;
	sctx->first_free = sbio->index;
	spin_unlock(&sctx->list_lock);

	if (sctx->is_dev_replace &&
	    atomic_read(&sctx->wr_ctx.flush_all_writes)) {
		mutex_lock(&sctx->wr_ctx.wr_lock);
		scrub_wr_submit(sctx);
		mutex_unlock(&sctx->wr_ctx.wr_lock);
	}

	scrub_pending_bio_dec(sctx);
}

static int scrub_find_csum(struct scrub_ctx *sctx, u64 logical, u8 *csum)
{
	struct btrfs_ordered_sum *sum = NULL;
	unsigned long index;
	unsigned long num_sectors;

	while (!list_empty(&sctx->csum_list)) {
		sum = list_first_entry(&sctx->csum_list,
				       struct btrfs_ordered_sum, list);
		if (sum->bytenr > logical)
			return 0;
		if (sum->bytenr + sum->len > logical)
			break;

		++sctx->stat.csum_discards;
		list_del(&sum->list);
		kfree(sum);
		sum = NULL;
	}
	if (!sum)
		return 0;

	index = ((u32)(logical - sum->bytenr)) / sctx->sectorsize;
	num_sectors = sum->len / sctx->sectorsize;
	memcpy(csum, sum->sums + index, sctx->csum_size);
	if (index == num_sectors - 1) {
		list_del(&sum->list);
		kfree(sum);
	}
	return 1;
}
			u64 physical, struct btrfs_device *dev, u64 flags,
			u64 gen, int mirror_num, u64 physical_for_dev_replace)
{
	int ret;
	u8 csum[BTRFS_CSUM_SIZE];
	u32 blocksize;

	if (flags & BTRFS_EXTENT_FLAG_DATA) {
		blocksize = sctx->sectorsize;
		spin_lock(&sctx->stat_lock);
		sctx->stat.data_extents_scrubbed++;
		sctx->stat.data_bytes_scrubbed += len;
		spin_unlock(&sctx->stat_lock);
	} else if (flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) {
		blocksize = sctx->nodesize;
		spin_lock(&sctx->stat_lock);
		sctx->stat.tree_extents_scrubbed++;
		sctx->stat.tree_bytes_scrubbed += len;
		spin_unlock(&sctx->stat_lock);
	} else {
		blocksize = sctx->sectorsize;
		WARN_ON(1);
	}

	while (len) {
		u64 l = min_t(u64, len, blocksize);
		int have_csum = 0;

		if (flags & BTRFS_EXTENT_FLAG_DATA) {
			/* push csums to sbio */
			have_csum = scrub_find_csum(sctx, logical, csum);
			if (have_csum == 0)
				++sctx->stat.no_csum;
			if (sctx->is_dev_replace && !have_csum) {
				ret = copy_nocow_pages(sctx, logical, l,
						       mirror_num,
						      physical_for_dev_replace);
				goto behind_scrub_pages;
			}
		}
		ret = scrub_pages(sctx, logical, l, physical, dev, flags, gen,
				  mirror_num, have_csum ? csum : NULL, 0,
				  physical_for_dev_replace);
behind_scrub_pages:
		if (ret)
			return ret;
		len -= l;
		logical += l;
		physical += l;
		physical_for_dev_replace += l;
	}
	return 0;
}
				  u64 physical, struct btrfs_device *dev,
				  u64 flags, u64 gen, int mirror_num, u8 *csum)
{
	struct scrub_ctx *sctx = sparity->sctx;
	struct scrub_block *sblock;
	int index;

	sblock = kzalloc(sizeof(*sblock), GFP_KERNEL);
	if (!sblock) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.malloc_errors++;
		spin_unlock(&sctx->stat_lock);
		return -ENOMEM;
	}

	/* one ref inside this function, plus one for each page added to
	 * a bio later on */
	refcount_set(&sblock->refs, 1);
	sblock->sctx = sctx;
	sblock->no_io_error_seen = 1;
	sblock->sparity = sparity;
	scrub_parity_get(sparity);

	for (index = 0; len > 0; index++) {
		struct scrub_page *spage;
		u64 l = min_t(u64, len, PAGE_SIZE);

		spage = kzalloc(sizeof(*spage), GFP_KERNEL);
		if (!spage) {
leave_nomem:
			spin_lock(&sctx->stat_lock);
			sctx->stat.malloc_errors++;
			spin_unlock(&sctx->stat_lock);
			scrub_block_put(sblock);
			return -ENOMEM;
		}
		BUG_ON(index >= SCRUB_MAX_PAGES_PER_BLOCK);
		/* For scrub block */
		scrub_page_get(spage);
		sblock->pagev[index] = spage;
		/* For scrub parity */
		scrub_page_get(spage);
		list_add_tail(&spage->list, &sparity->spages);
		spage->sblock = sblock;
		spage->dev = dev;
		spage->flags = flags;
		spage->generation = gen;
		spage->logical = logical;
		spage->physical = physical;
		spage->mirror_num = mirror_num;
		if (csum) {
			spage->have_csum = 1;
			memcpy(spage->csum, csum, sctx->csum_size);
		} else {
			spage->have_csum = 0;
		}
		sblock->page_count++;
		spage->page = alloc_page(GFP_KERNEL);
		if (!spage->page)
			goto leave_nomem;
		len -= l;
		logical += l;
		physical += l;
	}

	WARN_ON(sblock->page_count == 0);
	for (index = 0; index < sblock->page_count; index++) {
		struct scrub_page *spage = sblock->pagev[index];
		int ret;

		ret = scrub_add_page_to_rd_bio(sctx, spage);
		if (ret) {
			scrub_block_put(sblock);
			return ret;
		}
	}

	/* last one frees, either here or in bio completion for last page */
	scrub_block_put(sblock);
	return 0;
}
				   u64 physical, struct btrfs_device *dev,
				   u64 flags, u64 gen, int mirror_num)
{
	struct scrub_ctx *sctx = sparity->sctx;
	int ret;
	u8 csum[BTRFS_CSUM_SIZE];
	u32 blocksize;

	if (dev->missing) {
		scrub_parity_mark_sectors_error(sparity, logical, len);
		return 0;
	}

	if (flags & BTRFS_EXTENT_FLAG_DATA) {
		blocksize = sctx->sectorsize;
	} else if (flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) {
		blocksize = sctx->nodesize;
	} else {
		blocksize = sctx->sectorsize;
		WARN_ON(1);
	}

	while (len) {
		u64 l = min_t(u64, len, blocksize);
		int have_csum = 0;

		if (flags & BTRFS_EXTENT_FLAG_DATA) {
			/* push csums to sbio */
			have_csum = scrub_find_csum(sctx, logical, csum);
			if (have_csum == 0)
				goto skip;
		}
		ret = scrub_pages_for_parity(sparity, logical, l, physical, dev,
					     flags, gen, mirror_num,
					     have_csum ? csum : NULL);
		if (ret)
			return ret;
skip:
		len -= l;
		logical += l;
		physical += l;
	}
	return 0;
}
				   struct map_lookup *map, u64 *offset,
				   u64 *stripe_start)
{
	int i;
	int j = 0;
	u64 stripe_nr;
	u64 last_offset;
	u32 stripe_index;
	u32 rot;

	last_offset = (physical - map->stripes[num].physical) *
		      nr_data_stripes(map);
	if (stripe_start)
		*stripe_start = last_offset;

	*offset = last_offset;
	for (i = 0; i < nr_data_stripes(map); i++) {
		*offset = last_offset + i * map->stripe_len;

		stripe_nr = div64_u64(*offset, map->stripe_len);
		stripe_nr = div_u64(stripe_nr, nr_data_stripes(map));

		/* Work out the disk rotation on this stripe-set */
		stripe_nr = div_u64_rem(stripe_nr, map->num_stripes, &rot);
		/* calculate which stripe this data locates */
		rot += i;
		stripe_index = rot % map->num_stripes;
		if (stripe_index == num)
			return 0;
		if (stripe_index < num)
			j++;
	}
	*offset = last_offset + j * map->stripe_len;
	return 1;
}
						  u64 logic_start,
						  u64 logic_end)
{
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_root *csum_root = fs_info->csum_root;
	struct btrfs_extent_item *extent;
	struct btrfs_bio *bbio = NULL;
	u64 flags;
	int ret;
	int slot;
	struct extent_buffer *l;
	struct btrfs_key key;
	u64 generation;
	u64 extent_logical;
	u64 extent_physical;
	u64 extent_len;
	u64 mapped_length;
	struct btrfs_device *extent_dev;
	struct scrub_parity *sparity;
	int nsectors;
	int bitmap_len;
	int extent_mirror_num;
	int stop_loop = 0;

	nsectors = div_u64(map->stripe_len, fs_info->sectorsize);
	bitmap_len = scrub_calc_parity_bitmap_len(nsectors);
	sparity = kzalloc(sizeof(struct scrub_parity) + 2 * bitmap_len,
			  GFP_NOFS);
	if (!sparity) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.malloc_errors++;
		spin_unlock(&sctx->stat_lock);
		return -ENOMEM;
	}

	sparity->stripe_len = map->stripe_len;
	sparity->nsectors = nsectors;
	sparity->sctx = sctx;
	sparity->scrub_dev = sdev;
	sparity->logic_start = logic_start;
	sparity->logic_end = logic_end;
	refcount_set(&sparity->refs, 1);
	INIT_LIST_HEAD(&sparity->spages);
	sparity->dbitmap = sparity->bitmap;
	sparity->ebitmap = (void *)sparity->bitmap + bitmap_len;

	ret = 0;
	while (logic_start < logic_end) {
		if (btrfs_fs_incompat(fs_info, SKINNY_METADATA))
			key.type = BTRFS_METADATA_ITEM_KEY;
		else
			key.type = BTRFS_EXTENT_ITEM_KEY;
		key.objectid = logic_start;
		key.offset = (u64)-1;

		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0)
			goto out;

		if (ret > 0) {
			ret = btrfs_previous_extent_item(root, path, 0);
			if (ret < 0)
				goto out;
			if (ret > 0) {
				btrfs_release_path(path);
				ret = btrfs_search_slot(NULL, root, &key,
							path, 0, 0);
				if (ret < 0)
					goto out;
			}
		}

		stop_loop = 0;
		while (1) {
			u64 bytes;

			l = path->nodes[0];
			slot = path->slots[0];
			if (slot >= btrfs_header_nritems(l)) {
				ret = btrfs_next_leaf(root, path);
				if (ret == 0)
					continue;
				if (ret < 0)
					goto out;

				stop_loop = 1;
				break;
			}
			btrfs_item_key_to_cpu(l, &key, slot);

			if (key.type != BTRFS_EXTENT_ITEM_KEY &&
			    key.type != BTRFS_METADATA_ITEM_KEY)
				goto next;

			if (key.type == BTRFS_METADATA_ITEM_KEY)
				bytes = fs_info->nodesize;
			else
				bytes = key.offset;

			if (key.objectid + bytes <= logic_start)
				goto next;

			if (key.objectid >= logic_end) {
				stop_loop = 1;
				break;
			}

			while (key.objectid >= logic_start + map->stripe_len)
				logic_start += map->stripe_len;

			extent = btrfs_item_ptr(l, slot,
						struct btrfs_extent_item);
			flags = btrfs_extent_flags(l, extent);
			generation = btrfs_extent_generation(l, extent);

			if ((flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) &&
			    (key.objectid < logic_start ||
			     key.objectid + bytes >
			     logic_start + map->stripe_len)) {
				btrfs_err(fs_info,
					  "scrub: tree block %llu spanning stripes, ignored. logical=%llu",
					  key.objectid, logic_start);
				spin_lock(&sctx->stat_lock);
				sctx->stat.uncorrectable_errors++;
				spin_unlock(&sctx->stat_lock);
				goto next;
			}
again:
			extent_logical = key.objectid;
			extent_len = bytes;

			if (extent_logical < logic_start) {
				extent_len -= logic_start - extent_logical;
				extent_logical = logic_start;
			}

			if (extent_logical + extent_len >
			    logic_start + map->stripe_len)
				extent_len = logic_start + map->stripe_len -
					     extent_logical;

			scrub_parity_mark_sectors_data(sparity, extent_logical,
						       extent_len);

			mapped_length = extent_len;
			bbio = NULL;
			ret = btrfs_map_block(fs_info, BTRFS_MAP_READ,
					extent_logical, &mapped_length, &bbio,
					0);
			if (!ret) {
				if (!bbio || mapped_length < extent_len)
					ret = -EIO;
			}
			if (ret) {
				btrfs_put_bbio(bbio);
				goto out;
			}
			extent_physical = bbio->stripes[0].physical;
			extent_mirror_num = bbio->mirror_num;
			extent_dev = bbio->stripes[0].dev;
			btrfs_put_bbio(bbio);

			ret = btrfs_lookup_csums_range(csum_root,
						extent_logical,
						extent_logical + extent_len - 1,
						&sctx->csum_list, 1);
			if (ret)
				goto out;

			ret = scrub_extent_for_parity(sparity, extent_logical,
						      extent_len,
						      extent_physical,
						      extent_dev, flags,
						      generation,
						      extent_mirror_num);

			scrub_free_csums(sctx);

			if (ret)
				goto out;

			if (extent_logical + extent_len <
			    key.objectid + bytes) {
				logic_start += map->stripe_len;

				if (logic_start >= logic_end) {
					stop_loop = 1;
					break;
				}

				if (logic_start < key.objectid + bytes) {
					cond_resched();
					goto again;
				}
			}
next:
			path->slots[0]++;
		}

		btrfs_release_path(path);

		if (stop_loop)
			break;

		logic_start += map->stripe_len;
	}
out:
	if (ret < 0)
		scrub_parity_mark_sectors_error(sparity, logic_start,
						logic_end - logic_start);
	scrub_parity_put(sparity);
	scrub_submit(sctx);
	mutex_lock(&sctx->wr_ctx.wr_lock);
	scrub_wr_submit(sctx);
	mutex_unlock(&sctx->wr_ctx.wr_lock);

	btrfs_release_path(path);
	return ret < 0 ? ret : 0;
}
					   int num, u64 base, u64 length,
					   int is_dev_replace)
{
	struct btrfs_path *path, *ppath;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	struct btrfs_root *root = fs_info->extent_root;
	struct btrfs_root *csum_root = fs_info->csum_root;
	struct btrfs_extent_item *extent;
	struct blk_plug plug;
	u64 flags;
	int ret;
	int slot;
	u64 nstripes;
	struct extent_buffer *l;
	u64 physical;
	u64 logical;
	u64 logic_end;
	u64 physical_end;
	u64 generation;
	int mirror_num;
	struct reada_control *reada1;
	struct reada_control *reada2;
	struct btrfs_key key;
	struct btrfs_key key_end;
	u64 increment = map->stripe_len;
	u64 offset;
	u64 extent_logical;
	u64 extent_physical;
	u64 extent_len;
	u64 stripe_logical;
	u64 stripe_end;
	struct btrfs_device *extent_dev;
	int extent_mirror_num;
	int stop_loop = 0;

	physical = map->stripes[num].physical;
	offset = 0;
	nstripes = div64_u64(length, map->stripe_len);
	if (map->type & BTRFS_BLOCK_GROUP_RAID0) {
		offset = map->stripe_len * num;
		increment = map->stripe_len * map->num_stripes;
		mirror_num = 1;
	} else if (map->type & BTRFS_BLOCK_GROUP_RAID10) {
		int factor = map->num_stripes / map->sub_stripes;
		offset = map->stripe_len * (num / map->sub_stripes);
		increment = map->stripe_len * factor;
		mirror_num = num % map->sub_stripes + 1;
	} else if (map->type & BTRFS_BLOCK_GROUP_RAID1) {
		increment = map->stripe_len;
		mirror_num = num % map->num_stripes + 1;
	} else if (map->type & BTRFS_BLOCK_GROUP_DUP) {
		increment = map->stripe_len;
		mirror_num = num % map->num_stripes + 1;
	} else if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		get_raid56_logic_offset(physical, num, map, &offset, NULL);
		increment = map->stripe_len * nr_data_stripes(map);
		mirror_num = 1;
	} else {
		increment = map->stripe_len;
		mirror_num = 1;
	}

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	ppath = btrfs_alloc_path();
	if (!ppath) {
		btrfs_free_path(path);
		return -ENOMEM;
	}

	/*
	 * work on commit root. The related disk blocks are static as
	 * long as COW is applied. This means, it is save to rewrite
	 * them to repair disk errors without any race conditions
	 */
	path->search_commit_root = 1;
	path->skip_locking = 1;

	ppath->search_commit_root = 1;
	ppath->skip_locking = 1;
	/*
	 * trigger the readahead for extent tree csum tree and wait for
	 * completion. During readahead, the scrub is officially paused
	 * to not hold off transaction commits
	 */
	logical = base + offset;
	physical_end = physical + nstripes * map->stripe_len;
	if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		get_raid56_logic_offset(physical_end, num,
					map, &logic_end, NULL);
		logic_end += base;
	} else {
		logic_end = logical + increment * nstripes;
	}
	wait_event(sctx->list_wait,
		   atomic_read(&sctx->bios_in_flight) == 0);
	scrub_blocked_if_needed(fs_info);

	/* FIXME it might be better to start readahead at commit root */
	key.objectid = logical;
	key.type = BTRFS_EXTENT_ITEM_KEY;
	key.offset = (u64)0;
	key_end.objectid = logic_end;
	key_end.type = BTRFS_METADATA_ITEM_KEY;
	key_end.offset = (u64)-1;
	reada1 = btrfs_reada_add(root, &key, &key_end);

	key.objectid = BTRFS_EXTENT_CSUM_OBJECTID;
	key.type = BTRFS_EXTENT_CSUM_KEY;
	key.offset = logical;
	key_end.objectid = BTRFS_EXTENT_CSUM_OBJECTID;
	key_end.type = BTRFS_EXTENT_CSUM_KEY;
	key_end.offset = logic_end;
	reada2 = btrfs_reada_add(csum_root, &key, &key_end);

	if (!IS_ERR(reada1))
		btrfs_reada_wait(reada1);
	if (!IS_ERR(reada2))
		btrfs_reada_wait(reada2);


	/*
	 * collect all data csums for the stripe to avoid seeking during
	 * the scrub. This might currently (crc32) end up to be about 1MB
	 */
	blk_start_plug(&plug);

	/*
	 * now find all extents for each stripe and scrub them
	 */
	ret = 0;
	while (physical < physical_end) {
		/*
		 * canceled?
		 */
		if (atomic_read(&fs_info->scrub_cancel_req) ||
		    atomic_read(&sctx->cancel_req)) {
			ret = -ECANCELED;
			goto out;
		}
		/*
		 * check to see if we have to pause
		 */
		if (atomic_read(&fs_info->scrub_pause_req)) {
			/* push queued extents */
			atomic_set(&sctx->wr_ctx.flush_all_writes, 1);
			scrub_submit(sctx);
			mutex_lock(&sctx->wr_ctx.wr_lock);
			scrub_wr_submit(sctx);
			mutex_unlock(&sctx->wr_ctx.wr_lock);
			wait_event(sctx->list_wait,
				   atomic_read(&sctx->bios_in_flight) == 0);
			atomic_set(&sctx->wr_ctx.flush_all_writes, 0);
			scrub_blocked_if_needed(fs_info);
		}

		if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
			ret = get_raid56_logic_offset(physical, num, map,
						      &logical,
						      &stripe_logical);
			logical += base;
			if (ret) {
				/* it is parity strip */
				stripe_logical += base;
				stripe_end = stripe_logical + increment;
				ret = scrub_raid56_parity(sctx, map, scrub_dev,
							  ppath, stripe_logical,
							  stripe_end);
				if (ret)
					goto out;
				goto skip;
			}
		}

		if (btrfs_fs_incompat(fs_info, SKINNY_METADATA))
			key.type = BTRFS_METADATA_ITEM_KEY;
		else
			key.type = BTRFS_EXTENT_ITEM_KEY;
		key.objectid = logical;
		key.offset = (u64)-1;

		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0)
			goto out;

		if (ret > 0) {
			ret = btrfs_previous_extent_item(root, path, 0);
			if (ret < 0)
				goto out;
			if (ret > 0) {
				/* there's no smaller item, so stick with the
				 * larger one */
				btrfs_release_path(path);
				ret = btrfs_search_slot(NULL, root, &key,
							path, 0, 0);
				if (ret < 0)
					goto out;
			}
		}

		stop_loop = 0;
		while (1) {
			u64 bytes;

			l = path->nodes[0];
			slot = path->slots[0];
			if (slot >= btrfs_header_nritems(l)) {
				ret = btrfs_next_leaf(root, path);
				if (ret == 0)
					continue;
				if (ret < 0)
					goto out;

				stop_loop = 1;
				break;
			}
			btrfs_item_key_to_cpu(l, &key, slot);

			if (key.type != BTRFS_EXTENT_ITEM_KEY &&
			    key.type != BTRFS_METADATA_ITEM_KEY)
				goto next;

			if (key.type == BTRFS_METADATA_ITEM_KEY)
				bytes = fs_info->nodesize;
			else
				bytes = key.offset;

			if (key.objectid + bytes <= logical)
				goto next;

			if (key.objectid >= logical + map->stripe_len) {
				/* out of this device extent */
				if (key.objectid >= logic_end)
					stop_loop = 1;
				break;
			}

			extent = btrfs_item_ptr(l, slot,
						struct btrfs_extent_item);
			flags = btrfs_extent_flags(l, extent);
			generation = btrfs_extent_generation(l, extent);

			if ((flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) &&
			    (key.objectid < logical ||
			     key.objectid + bytes >
			     logical + map->stripe_len)) {
				btrfs_err(fs_info,
					   "scrub: tree block %llu spanning stripes, ignored. logical=%llu",
				       key.objectid, logical);
				spin_lock(&sctx->stat_lock);
				sctx->stat.uncorrectable_errors++;
				spin_unlock(&sctx->stat_lock);
				goto next;
			}

again:
			extent_logical = key.objectid;
			extent_len = bytes;

			/*
			 * trim extent to this stripe
			 */
			if (extent_logical < logical) {
				extent_len -= logical - extent_logical;
				extent_logical = logical;
			}
			if (extent_logical + extent_len >
			    logical + map->stripe_len) {
				extent_len = logical + map->stripe_len -
					     extent_logical;
			}

			extent_physical = extent_logical - logical + physical;
			extent_dev = scrub_dev;
			extent_mirror_num = mirror_num;
			if (is_dev_replace)
				scrub_remap_extent(fs_info, extent_logical,
						   extent_len, &extent_physical,
						   &extent_dev,
						   &extent_mirror_num);

			ret = btrfs_lookup_csums_range(csum_root,
						       extent_logical,
						       extent_logical +
						       extent_len - 1,
						       &sctx->csum_list, 1);
			if (ret)
				goto out;

			ret = scrub_extent(sctx, extent_logical, extent_len,
					   extent_physical, extent_dev, flags,
					   generation, extent_mirror_num,
					   extent_logical - logical + physical);

			scrub_free_csums(sctx);

			if (ret)
				goto out;

			if (extent_logical + extent_len <
			    key.objectid + bytes) {
				if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
					/*
					 * loop until we find next data stripe
					 * or we have finished all stripes.
					 */
loop:
					physical += map->stripe_len;
					ret = get_raid56_logic_offset(physical,
							num, map, &logical,
							&stripe_logical);
					logical += base;

					if (ret && physical < physical_end) {
						stripe_logical += base;
						stripe_end = stripe_logical +
								increment;
						ret = scrub_raid56_parity(sctx,
							map, scrub_dev, ppath,
							stripe_logical,
							stripe_end);
						if (ret)
							goto out;
						goto loop;
					}
				} else {
					physical += map->stripe_len;
					logical += increment;
				}
				if (logical < key.objectid + bytes) {
					cond_resched();
					goto again;
				}

				if (physical >= physical_end) {
					stop_loop = 1;
					break;
				}
			}
next:
			path->slots[0]++;
		}
		btrfs_release_path(path);
skip:
		logical += increment;
		physical += map->stripe_len;
		spin_lock(&sctx->stat_lock);
		if (stop_loop)
			sctx->stat.last_physical = map->stripes[num].physical +
						   length;
		else
			sctx->stat.last_physical = physical;
		spin_unlock(&sctx->stat_lock);
		if (stop_loop)
			break;
	}
out:
	/* push queued extents */
	scrub_submit(sctx);
	mutex_lock(&sctx->wr_ctx.wr_lock);
	scrub_wr_submit(sctx);
	mutex_unlock(&sctx->wr_ctx.wr_lock);

	blk_finish_plug(&plug);
	btrfs_free_path(path);
	btrfs_free_path(ppath);
	return ret < 0 ? ret : 0;
}
					  struct btrfs_block_group_cache *cache,
					  int is_dev_replace)
{
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	struct btrfs_mapping_tree *map_tree = &fs_info->mapping_tree;
	struct map_lookup *map;
	struct extent_map *em;
	int i;
	int ret = 0;

	read_lock(&map_tree->map_tree.lock);
	em = lookup_extent_mapping(&map_tree->map_tree, chunk_offset, 1);
	read_unlock(&map_tree->map_tree.lock);

	if (!em) {
		/*
		 * Might have been an unused block group deleted by the cleaner
		 * kthread or relocation.
		 */
		spin_lock(&cache->lock);
		if (!cache->removed)
			ret = -EINVAL;
		spin_unlock(&cache->lock);

		return ret;
	}

	map = em->map_lookup;
	if (em->start != chunk_offset)
		goto out;

	if (em->len < length)
		goto out;

	for (i = 0; i < map->num_stripes; ++i) {
		if (map->stripes[i].dev->bdev == scrub_dev->bdev &&
		    map->stripes[i].physical == dev_offset) {
			ret = scrub_stripe(sctx, map, scrub_dev, i,
					   chunk_offset, length,
					   is_dev_replace);
			if (ret)
				goto out;
		}
	}
out:
	free_extent_map(em);

	return ret;
}
			   struct btrfs_device *scrub_dev, u64 start, u64 end,
			   int is_dev_replace)
{
	struct btrfs_dev_extent *dev_extent = NULL;
	struct btrfs_path *path;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	struct btrfs_root *root = fs_info->dev_root;
	u64 length;
	u64 chunk_offset;
	int ret = 0;
	int ro_set;
	int slot;
	struct extent_buffer *l;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_block_group_cache *cache;
	struct btrfs_dev_replace *dev_replace = &fs_info->dev_replace;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->reada = READA_FORWARD;
	path->search_commit_root = 1;
	path->skip_locking = 1;

	key.objectid = scrub_dev->devid;
	key.offset = 0ull;
	key.type = BTRFS_DEV_EXTENT_KEY;

	while (1) {
		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0)
			break;
		if (ret > 0) {
			if (path->slots[0] >=
			    btrfs_header_nritems(path->nodes[0])) {
				ret = btrfs_next_leaf(root, path);
				if (ret < 0)
					break;
				if (ret > 0) {
					ret = 0;
					break;
				}
			} else {
				ret = 0;
			}
		}

		l = path->nodes[0];
		slot = path->slots[0];

		btrfs_item_key_to_cpu(l, &found_key, slot);

		if (found_key.objectid != scrub_dev->devid)
			break;

		if (found_key.type != BTRFS_DEV_EXTENT_KEY)
			break;

		if (found_key.offset >= end)
			break;

		if (found_key.offset < key.offset)
			break;

		dev_extent = btrfs_item_ptr(l, slot, struct btrfs_dev_extent);
		length = btrfs_dev_extent_length(l, dev_extent);

		if (found_key.offset + length <= start)
			goto skip;

		chunk_offset = btrfs_dev_extent_chunk_offset(l, dev_extent);

		/*
		 * get a reference on the corresponding block group to prevent
		 * the chunk from going away while we scrub it
		 */
		cache = btrfs_lookup_block_group(fs_info, chunk_offset);

		/* some chunks are removed but not committed to disk yet,
		 * continue scrubbing */
		if (!cache)
			goto skip;

		/*
		 * we need call btrfs_inc_block_group_ro() with scrubs_paused,
		 * to avoid deadlock caused by:
		 * btrfs_inc_block_group_ro()
		 * -> btrfs_wait_for_commit()
		 * -> btrfs_commit_transaction()
		 * -> btrfs_scrub_pause()
		 */
		scrub_pause_on(fs_info);
		ret = btrfs_inc_block_group_ro(fs_info, cache);
		if (!ret && is_dev_replace) {
			/*
			 * If we are doing a device replace wait for any tasks
			 * that started dellaloc right before we set the block
			 * group to RO mode, as they might have just allocated
			 * an extent from it or decided they could do a nocow
			 * write. And if any such tasks did that, wait for their
			 * ordered extents to complete and then commit the
			 * current transaction, so that we can later see the new
			 * extent items in the extent tree - the ordered extents
			 * create delayed data references (for cow writes) when
			 * they complete, which will be run and insert the
			 * corresponding extent items into the extent tree when
			 * we commit the transaction they used when running
			 * inode.c:btrfs_finish_ordered_io(). We later use
			 * the commit root of the extent tree to find extents
			 * to copy from the srcdev into the tgtdev, and we don't
			 * want to miss any new extents.
			 */
			btrfs_wait_block_group_reservations(cache);
			btrfs_wait_nocow_writers(cache);
			ret = btrfs_wait_ordered_roots(fs_info, -1,
						       cache->key.objectid,
						       cache->key.offset);
			if (ret > 0) {
				struct btrfs_trans_handle *trans;

				trans = btrfs_join_transaction(root);
				if (IS_ERR(trans))
					ret = PTR_ERR(trans);
				else
					ret = btrfs_commit_transaction(trans);
				if (ret) {
					scrub_pause_off(fs_info);
					btrfs_put_block_group(cache);
					break;
				}
			}
		}
		scrub_pause_off(fs_info);

		if (ret == 0) {
			ro_set = 1;
		} else if (ret == -ENOSPC) {
			/*
			 * btrfs_inc_block_group_ro return -ENOSPC when it
			 * failed in creating new chunk for metadata.
			 * It is not a problem for scrub/replace, because
			 * metadata are always cowed, and our scrub paused
			 * commit_transactions.
			 */
			ro_set = 0;
		} else {
			btrfs_warn(fs_info,
				   "failed setting block group ro, ret=%d\n",
				   ret);
			btrfs_put_block_group(cache);
			break;
		}

		btrfs_dev_replace_lock(&fs_info->dev_replace, 1);
		dev_replace->cursor_right = found_key.offset + length;
		dev_replace->cursor_left = found_key.offset;
		dev_replace->item_needs_writeback = 1;
		btrfs_dev_replace_unlock(&fs_info->dev_replace, 1);
		ret = scrub_chunk(sctx, scrub_dev, chunk_offset, length,
				  found_key.offset, cache, is_dev_replace);

		/*
		 * flush, submit all pending read and write bios, afterwards
		 * wait for them.
		 * Note that in the dev replace case, a read request causes
		 * write requests that are submitted in the read completion
		 * worker. Therefore in the current situation, it is required
		 * that all write requests are flushed, so that all read and
		 * write requests are really completed when bios_in_flight
		 * changes to 0.
		 */
		atomic_set(&sctx->wr_ctx.flush_all_writes, 1);
		scrub_submit(sctx);
		mutex_lock(&sctx->wr_ctx.wr_lock);
		scrub_wr_submit(sctx);
		mutex_unlock(&sctx->wr_ctx.wr_lock);

		wait_event(sctx->list_wait,
			   atomic_read(&sctx->bios_in_flight) == 0);

		scrub_pause_on(fs_info);

		/*
		 * must be called before we decrease @scrub_paused.
		 * make sure we don't block transaction commit while
		 * we are waiting pending workers finished.
		 */
		wait_event(sctx->list_wait,
			   atomic_read(&sctx->workers_pending) == 0);
		atomic_set(&sctx->wr_ctx.flush_all_writes, 0);

		scrub_pause_off(fs_info);

		btrfs_dev_replace_lock(&fs_info->dev_replace, 1);
		dev_replace->cursor_left = dev_replace->cursor_right;
		dev_replace->item_needs_writeback = 1;
		btrfs_dev_replace_unlock(&fs_info->dev_replace, 1);

		if (ro_set)
			btrfs_dec_block_group_ro(cache);

		/*
		 * We might have prevented the cleaner kthread from deleting
		 * this block group if it was already unused because we raced
		 * and set it to RO mode first. So add it back to the unused
		 * list, otherwise it might not ever be deleted unless a manual
		 * balance is triggered or it becomes used and unused again.
		 */
		spin_lock(&cache->lock);
		if (!cache->removed && !cache->ro && cache->reserved == 0 &&
		    btrfs_block_group_used(&cache->item) == 0) {
			spin_unlock(&cache->lock);
			spin_lock(&fs_info->unused_bgs_lock);
			if (list_empty(&cache->bg_list)) {
				btrfs_get_block_group(cache);
				list_add_tail(&cache->bg_list,
					      &fs_info->unused_bgs);
			}
			spin_unlock(&fs_info->unused_bgs_lock);
		} else {
			spin_unlock(&cache->lock);
		}

		btrfs_put_block_group(cache);
		if (ret)
			break;
		if (is_dev_replace &&
		    atomic64_read(&dev_replace->num_write_errors) > 0) {
			ret = -EIO;
			break;
		}
		if (sctx->stat.malloc_errors > 0) {
			ret = -ENOMEM;
			break;
		}
skip:
		key.offset = found_key.offset + length;
		btrfs_release_path(path);
	}

	btrfs_free_path(path);

	return ret;
}
static noinline_for_stack int scrub_supers(struct scrub_ctx *sctx,
					   struct btrfs_device *scrub_dev)
{
	int	i;
	u64	bytenr;
	u64	gen;
	int	ret;
	struct btrfs_fs_info *fs_info = sctx->fs_info;

	if (test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state))
		return -EIO;

	/* Seed devices of a new filesystem has their own generation. */
	if (scrub_dev->fs_devices != fs_info->fs_devices)
		gen = scrub_dev->generation;
	else
		gen = fs_info->last_trans_committed;

	for (i = 0; i < BTRFS_SUPER_MIRROR_MAX; i++) {
		bytenr = btrfs_sb_offset(i);
		if (bytenr + BTRFS_SUPER_INFO_SIZE >
		    scrub_dev->commit_total_bytes)
			break;

		ret = scrub_pages(sctx, bytenr, BTRFS_SUPER_INFO_SIZE, bytenr,
				  scrub_dev, BTRFS_EXTENT_FLAG_SUPER, gen, i,
				  NULL, 1, bytenr);
		if (ret)
			return ret;
	}
	wait_event(sctx->list_wait, atomic_read(&sctx->bios_in_flight) == 0);

	return 0;
}

void btrfs_scrub_pause(struct btrfs_fs_info *fs_info)
{
	mutex_lock(&fs_info->scrub_lock);
	atomic_inc(&fs_info->scrub_pause_req);
	while (atomic_read(&fs_info->scrubs_paused) !=
	       atomic_read(&fs_info->scrubs_running)) {
		mutex_unlock(&fs_info->scrub_lock);
		wait_event(fs_info->scrub_pause_wait,
			   atomic_read(&fs_info->scrubs_paused) ==
			   atomic_read(&fs_info->scrubs_running));
		mutex_lock(&fs_info->scrub_lock);
	}
	mutex_unlock(&fs_info->scrub_lock);
}

int btrfs_scrub_cancel(struct btrfs_fs_info *fs_info)
{
	mutex_lock(&fs_info->scrub_lock);
	if (!atomic_read(&fs_info->scrubs_running)) {
		mutex_unlock(&fs_info->scrub_lock);
		return -ENOTCONN;
	}

	atomic_inc(&fs_info->scrub_cancel_req);
	while (atomic_read(&fs_info->scrubs_running)) {
		mutex_unlock(&fs_info->scrub_lock);
		wait_event(fs_info->scrub_pause_wait,
			   atomic_read(&fs_info->scrubs_running) == 0);
		mutex_lock(&fs_info->scrub_lock);
	}
	atomic_dec(&fs_info->scrub_cancel_req);
	mutex_unlock(&fs_info->scrub_lock);

	return 0;
}
int btrfs_scrub_cancel_dev(struct btrfs_fs_info *fs_info,
			   struct btrfs_device *dev)
{
	struct scrub_ctx *sctx;

	mutex_lock(&fs_info->scrub_lock);
	sctx = dev->scrub_device;
	if (!sctx) {
		mutex_unlock(&fs_info->scrub_lock);
		return -ENOTCONN;
	}
	atomic_inc(&sctx->cancel_req);
	while (dev->scrub_device) {
		mutex_unlock(&fs_info->scrub_lock);
		wait_event(fs_info->scrub_pause_wait,
			   dev->scrub_device == NULL);
		mutex_lock(&fs_info->scrub_lock);
	}
	mutex_unlock(&fs_info->scrub_lock);

	return 0;
}

static void copy_nocow_pages_worker(struct btrfs_work *work)
{
	struct scrub_copy_nocow_ctx *nocow_ctx =
		container_of(work, struct scrub_copy_nocow_ctx, work);
	struct scrub_ctx *sctx = nocow_ctx->sctx;
	struct btrfs_fs_info *fs_info = sctx->fs_info;
	struct btrfs_root *root = fs_info->extent_root;
	u64 logical = nocow_ctx->logical;
	u64 len = nocow_ctx->len;
	int mirror_num = nocow_ctx->mirror_num;
	u64 physical_for_dev_replace = nocow_ctx->physical_for_dev_replace;
	int ret;
	struct btrfs_trans_handle *trans = NULL;
	struct btrfs_path *path;
	int not_written = 0;

	path = btrfs_alloc_path();
	if (!path) {
		spin_lock(&sctx->stat_lock);
		sctx->stat.malloc_errors++;
		spin_unlock(&sctx->stat_lock);
		not_written = 1;
		goto out;
	}

	trans = btrfs_join_transaction(root);
	if (IS_ERR(trans)) {
		not_written = 1;
		goto out;
	}

	ret = iterate_inodes_from_logical(logical, fs_info, path,
					  record_inode_for_nocow, nocow_ctx);
	if (ret != 0 && ret != -ENOENT) {
		btrfs_warn(fs_info,
			   "iterate_inodes_from_logical() failed: log %llu, phys %llu, len %llu, mir %u, ret %d",
			   logical, physical_for_dev_replace, len, mirror_num,
			   ret);
		not_written = 1;
		goto out;
	}

	btrfs_end_transaction(trans);
	trans = NULL;
	while (!list_empty(&nocow_ctx->inodes)) {
		struct scrub_nocow_inode *entry;
		entry = list_first_entry(&nocow_ctx->inodes,
					 struct scrub_nocow_inode,
					 list);
		list_del_init(&entry->list);
		ret = copy_nocow_pages_for_inode(entry->inum, entry->offset,
						 entry->root, nocow_ctx);
		kfree(entry);
		if (ret == COPY_COMPLETE) {
			ret = 0;
			break;
		} else if (ret) {
			break;
		}
	}
out:
	while (!list_empty(&nocow_ctx->inodes)) {
		struct scrub_nocow_inode *entry;
		entry = list_first_entry(&nocow_ctx->inodes,
					 struct scrub_nocow_inode,
					 list);
		list_del_init(&entry->list);
		kfree(entry);
	}
	if (trans && !IS_ERR(trans))
		btrfs_end_transaction(trans);
	if (not_written)
		btrfs_dev_replace_stats_inc(&fs_info->dev_replace.
					    num_uncorrectable_read_errors);

	btrfs_free_path(path);
	kfree(nocow_ctx);

	scrub_pending_trans_workers_dec(sctx);
}
static int copy_nocow_pages_for_inode(u64 inum, u64 offset, u64 root,
				      struct scrub_copy_nocow_ctx *nocow_ctx)
{
	struct btrfs_fs_info *fs_info = nocow_ctx->sctx->fs_info;
	struct btrfs_key key;
	struct inode *inode;
	struct page *page;
	struct btrfs_root *local_root;
	struct extent_io_tree *io_tree;
	u64 physical_for_dev_replace;
	u64 nocow_ctx_logical;
	u64 len = nocow_ctx->len;
	unsigned long index;
	int srcu_index;
	int ret = 0;
	int err = 0;

	key.objectid = root;
	key.type = BTRFS_ROOT_ITEM_KEY;
	key.offset = (u64)-1;

	srcu_index = srcu_read_lock(&fs_info->subvol_srcu);

	local_root = btrfs_read_fs_root_no_name(fs_info, &key);
	if (IS_ERR(local_root)) {
		srcu_read_unlock(&fs_info->subvol_srcu, srcu_index);
		return PTR_ERR(local_root);
	}

	key.type = BTRFS_INODE_ITEM_KEY;
	key.objectid = inum;
	key.offset = 0;
	inode = btrfs_iget(fs_info->sb, &key, local_root, NULL);
	srcu_read_unlock(&fs_info->subvol_srcu, srcu_index);
	if (IS_ERR(inode))
		return PTR_ERR(inode);

	/* Avoid truncate/dio/punch hole.. */
	inode_lock(inode);
	inode_dio_wait(inode);

	physical_for_dev_replace = nocow_ctx->physical_for_dev_replace;
	io_tree = &BTRFS_I(inode)->io_tree;
	nocow_ctx_logical = nocow_ctx->logical;

	ret = check_extent_to_block(BTRFS_I(inode), offset, len,
			nocow_ctx_logical);
	if (ret) {
		ret = ret > 0 ? 0 : ret;
		goto out;
	}

	while (len >= PAGE_SIZE) {
		index = offset >> PAGE_SHIFT;
again:
		page = find_or_create_page(inode->i_mapping, index, GFP_NOFS);
		if (!page) {
			btrfs_err(fs_info, "find_or_create_page() failed");
			ret = -ENOMEM;
			goto out;
		}

		if (PageUptodate(page)) {
			if (PageDirty(page))
				goto next_page;
		} else {
			ClearPageError(page);
			err = extent_read_full_page(io_tree, page,
							   btrfs_get_extent,
							   nocow_ctx->mirror_num);
			if (err) {
				ret = err;
				goto next_page;
			}

			lock_page(page);
			/*
			 * If the page has been remove from the page cache,
			 * the data on it is meaningless, because it may be
			 * old one, the new data may be written into the new
			 * page in the page cache.
			 */
			if (page->mapping != inode->i_mapping) {
				unlock_page(page);
				put_page(page);
				goto again;
			}
			if (!PageUptodate(page)) {
				ret = -EIO;
				goto next_page;
			}
		}

		ret = check_extent_to_block(BTRFS_I(inode), offset, len,
					    nocow_ctx_logical);
		if (ret) {
			ret = ret > 0 ? 0 : ret;
			goto next_page;
		}

		err = write_page_nocow(nocow_ctx->sctx,
				       physical_for_dev_replace, page);
		if (err)
			ret = err;
next_page:
		unlock_page(page);
		put_page(page);

		if (ret)
			break;

		offset += PAGE_SIZE;
		physical_for_dev_replace += PAGE_SIZE;
		nocow_ctx_logical += PAGE_SIZE;
		len -= PAGE_SIZE;
	}
	ret = COPY_COMPLETE;
out:
	inode_unlock(inode);
	iput(inode);
	return ret;
}
