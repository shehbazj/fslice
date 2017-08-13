 */
int btrfs_alloc_stripe_hash_table(struct btrfs_fs_info *info)
{
	struct btrfs_stripe_hash_table *table;
	struct btrfs_stripe_hash_table *x;
	struct btrfs_stripe_hash *cur;
	struct btrfs_stripe_hash *h;
	int num_entries = 1 << BTRFS_STRIPE_HASH_TABLE_BITS;
	int i;
	int table_size;

	if (info->stripe_hash_table)
		return 0;

	/*
	 * The table is large, starting with order 4 and can go as high as
	 * order 7 in case lock debugging is turned on.
	 *
	 * Try harder to allocate and fallback to vmalloc to lower the chance
	 * of a failing mount.
	 */
	table_size = sizeof(*table) + sizeof(*h) * num_entries;
	table = kzalloc(table_size, GFP_KERNEL | __GFP_NOWARN | __GFP_REPEAT);
	if (!table) {
		table = vzalloc(table_size);
		if (!table)
			return -ENOMEM;
	}

	spin_lock_init(&table->cache_lock);
	INIT_LIST_HEAD(&table->stripe_cache);

	h = table->table;

	for (i = 0; i < num_entries; i++) {
		cur = h + i;
		INIT_LIST_HEAD(&cur->hash_list);
		spin_lock_init(&cur->lock);
		init_waitqueue_head(&cur->wait);
	}

	x = cmpxchg(&info->stripe_hash_table, NULL, table);
	if (x)
		kvfree(x);
	return 0;
}
 */
static void cache_rbio_pages(struct btrfs_raid_bio *rbio)
{
	int i;
	char *s;
	char *d;
	int ret;

	ret = alloc_rbio_pages(rbio);
	if (ret)
		return;

	for (i = 0; i < rbio->nr_pages; i++) {
		if (!rbio->bio_pages[i])
			continue;

		s = kmap(rbio->bio_pages[i]);
		d = kmap(rbio->stripe_pages[i]);

		memcpy(d, s, PAGE_SIZE);

		kunmap(rbio->bio_pages[i]);
		kunmap(rbio->stripe_pages[i]);
		SetPageUptodate(rbio->stripe_pages[i]);
	}
	set_bit(RBIO_CACHE_READY_BIT, &rbio->flags);
}
 */
static void steal_rbio(struct btrfs_raid_bio *src, struct btrfs_raid_bio *dest)
{
	int i;
	struct page *s;
	struct page *d;

	if (!test_bit(RBIO_CACHE_READY_BIT, &src->flags))
		return;

	for (i = 0; i < dest->nr_pages; i++) {
		s = src->stripe_pages[i];
		if (!s || !PageUptodate(s)) {
			continue;
		}

		d = dest->stripe_pages[i];
		if (d)
			__free_page(d);

		dest->stripe_pages[i] = s;
		src->stripe_pages[i] = NULL;
	}
}
 */
static void btrfs_clear_rbio_cache(struct btrfs_fs_info *info)
{
	struct btrfs_stripe_hash_table *table;
	unsigned long flags;
	struct btrfs_raid_bio *rbio;

	table = info->stripe_hash_table;

	spin_lock_irqsave(&table->cache_lock, flags);
	while (!list_empty(&table->stripe_cache)) {
		rbio = list_entry(table->stripe_cache.next,
				  struct btrfs_raid_bio,
				  stripe_cache);
		__remove_rbio_from_cache(rbio);
	}
	spin_unlock_irqrestore(&table->cache_lock, flags);
}

static void __free_raid_bio(struct btrfs_raid_bio *rbio)
{
	int i;

	if (!refcount_dec_and_test(&rbio->refs))
		return;

	WARN_ON(!list_empty(&rbio->stripe_cache));
	WARN_ON(!list_empty(&rbio->hash_list));
	WARN_ON(!bio_list_empty(&rbio->bio_list));

	for (i = 0; i < rbio->nr_pages; i++) {
		if (rbio->stripe_pages[i]) {
			__free_page(rbio->stripe_pages[i]);
			rbio->stripe_pages[i] = NULL;
		}
	}

	btrfs_put_bbio(rbio->bbio);
	kfree(rbio);
}
 */
static void rbio_orig_end_io(struct btrfs_raid_bio *rbio, int err)
{
	struct bio *cur = bio_list_get(&rbio->bio_list);
	struct bio *next;

	if (rbio->generic_bio_cnt)
		btrfs_bio_counter_sub(rbio->fs_info, rbio->generic_bio_cnt);

	free_raid_bio(rbio);

	while (cur) {
		next = cur->bi_next;
		cur->bi_next = NULL;
		cur->bi_error = err;
		bio_endio(cur);
		cur = next;
	}
}
/* allocate pages for all the stripes in the bio, including parity */
static int alloc_rbio_pages(struct btrfs_raid_bio *rbio)
{
	int i;
	struct page *page;

	for (i = 0; i < rbio->nr_pages; i++) {
		if (rbio->stripe_pages[i])
			continue;
		page = alloc_page(GFP_NOFS | __GFP_HIGHMEM);
		if (!page)
			return -ENOMEM;
		rbio->stripe_pages[i] = page;
	}
	return 0;
}
/* only allocate pages for p/q stripes */
static int alloc_rbio_parity_pages(struct btrfs_raid_bio *rbio)
{
	int i;
	struct page *page;

	i = rbio_stripe_page_index(rbio, rbio->nr_data, 0);

	for (; i < rbio->nr_pages; i++) {
		if (rbio->stripe_pages[i])
			continue;
		page = alloc_page(GFP_NOFS | __GFP_HIGHMEM);
		if (!page)
			return -ENOMEM;
		rbio->stripe_pages[i] = page;
	}
	return 0;
}
 */
static noinline void finish_rmw(struct btrfs_raid_bio *rbio)
{
	struct btrfs_bio *bbio = rbio->bbio;
	void *pointers[rbio->real_stripes];
	int nr_data = rbio->nr_data;
	int stripe;
	int pagenr;
	int p_stripe = -1;
	int q_stripe = -1;
	struct bio_list bio_list;
	struct bio *bio;
	int ret;

	bio_list_init(&bio_list);

	if (rbio->real_stripes - rbio->nr_data == 1) {
		p_stripe = rbio->real_stripes - 1;
	} else if (rbio->real_stripes - rbio->nr_data == 2) {
		p_stripe = rbio->real_stripes - 2;
		q_stripe = rbio->real_stripes - 1;
	} else {
		BUG();
	}

	/* at this point we either have a full stripe,
	 * or we've read the full stripe from the drive.
	 * recalculate the parity and write the new results.
	 *
	 * We're not allowed to add any new bios to the
	 * bio list here, anyone else that wants to
	 * change this stripe needs to do their own rmw.
	 */
	spin_lock_irq(&rbio->bio_list_lock);
	set_bit(RBIO_RMW_LOCKED_BIT, &rbio->flags);
	spin_unlock_irq(&rbio->bio_list_lock);

	atomic_set(&rbio->error, 0);

	/*
	 * now that we've set rmw_locked, run through the
	 * bio list one last time and map the page pointers
	 *
	 * We don't cache full rbios because we're assuming
	 * the higher layers are unlikely to use this area of
	 * the disk again soon.  If they do use it again,
	 * hopefully they will send another full bio.
	 */
	index_rbio_pages(rbio);
	if (!rbio_is_full(rbio))
		cache_rbio_pages(rbio);
	else
		clear_bit(RBIO_CACHE_READY_BIT, &rbio->flags);

	for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
		struct page *p;
		/* first collect one page from each data stripe */
		for (stripe = 0; stripe < nr_data; stripe++) {
			p = page_in_rbio(rbio, stripe, pagenr, 0);
			pointers[stripe] = kmap(p);
		}

		/* then add the parity stripe */
		p = rbio_pstripe_page(rbio, pagenr);
		SetPageUptodate(p);
		pointers[stripe++] = kmap(p);

		if (q_stripe != -1) {

			/*
			 * raid6, add the qstripe and call the
			 * library function to fill in our p/q
			 */
			p = rbio_qstripe_page(rbio, pagenr);
			SetPageUptodate(p);
			pointers[stripe++] = kmap(p);

			raid6_call.gen_syndrome(rbio->real_stripes, PAGE_SIZE,
						pointers);
		} else {
			/* raid5 */
			memcpy(pointers[nr_data], pointers[0], PAGE_SIZE);
			run_xor(pointers + 1, nr_data - 1, PAGE_SIZE);
		}


		for (stripe = 0; stripe < rbio->real_stripes; stripe++)
			kunmap(page_in_rbio(rbio, stripe, pagenr, 0));
	}

	/*
	 * time to start writing.  Make bios for everything from the
	 * higher layers (the bio_list in our rbio) and our p/q.  Ignore
	 * everything else.
	 */
	for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
		for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
			struct page *page;
			if (stripe < rbio->nr_data) {
				page = page_in_rbio(rbio, stripe, pagenr, 1);
				if (!page)
					continue;
			} else {
			       page = rbio_stripe_page(rbio, stripe, pagenr);
			}

			ret = rbio_add_io_page(rbio, &bio_list,
				       page, stripe, pagenr, rbio->stripe_len);
			if (ret)
				goto cleanup;
		}
	}

	if (likely(!bbio->num_tgtdevs))
		goto write_data;

	for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
		if (!bbio->tgtdev_map[stripe])
			continue;

		for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
			struct page *page;
			if (stripe < rbio->nr_data) {
				page = page_in_rbio(rbio, stripe, pagenr, 1);
				if (!page)
					continue;
			} else {
			       page = rbio_stripe_page(rbio, stripe, pagenr);
			}

			ret = rbio_add_io_page(rbio, &bio_list, page,
					       rbio->bbio->tgtdev_map[stripe],
					       pagenr, rbio->stripe_len);
			if (ret)
				goto cleanup;
		}
	}

write_data:
	atomic_set(&rbio->stripes_pending, bio_list_size(&bio_list));
	BUG_ON(atomic_read(&rbio->stripes_pending) == 0);

	while (1) {
		bio = bio_list_pop(&bio_list);
		if (!bio)
			break;

		bio->bi_private = rbio;
		bio->bi_end_io = raid_write_end_io;
		bio_set_op_attrs(bio, REQ_OP_WRITE, 0);

		submit_bio(bio);
	}
	return;

cleanup:
	rbio_orig_end_io(rbio, -EIO);
}
static int find_bio_stripe(struct btrfs_raid_bio *rbio,
			   struct bio *bio)
{
	u64 physical = bio->bi_iter.bi_sector;
	u64 stripe_start;
	int i;
	struct btrfs_bio_stripe *stripe;

	physical <<= 9;

	for (i = 0; i < rbio->bbio->num_stripes; i++) {
		stripe = &rbio->bbio->stripes[i];
		stripe_start = stripe->physical;
		if (physical >= stripe_start &&
		    physical < stripe_start + rbio->stripe_len &&
		    bio->bi_bdev == stripe->dev->bdev) {
			return i;
		}
	}
	return -1;
}
static int find_logical_bio_stripe(struct btrfs_raid_bio *rbio,
				   struct bio *bio)
{
	u64 logical = bio->bi_iter.bi_sector;
	u64 stripe_start;
	int i;

	logical <<= 9;

	for (i = 0; i < rbio->nr_data; i++) {
		stripe_start = rbio->bbio->raid_map[i];
		if (logical >= stripe_start &&
		    logical < stripe_start + rbio->stripe_len) {
			return i;
		}
	}
	return -1;
}
 */
static int raid56_rmw_stripe(struct btrfs_raid_bio *rbio)
{
	int bios_to_read = 0;
	struct bio_list bio_list;
	int ret;
	int pagenr;
	int stripe;
	struct bio *bio;

	bio_list_init(&bio_list);

	ret = alloc_rbio_pages(rbio);
	if (ret)
		goto cleanup;

	index_rbio_pages(rbio);

	atomic_set(&rbio->error, 0);
	/*
	 * build a list of bios to read all the missing parts of this
	 * stripe
	 */
	for (stripe = 0; stripe < rbio->nr_data; stripe++) {
		for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
			struct page *page;
			/*
			 * we want to find all the pages missing from
			 * the rbio and read them from the disk.  If
			 * page_in_rbio finds a page in the bio list
			 * we don't need to read it off the stripe.
			 */
			page = page_in_rbio(rbio, stripe, pagenr, 1);
			if (page)
				continue;

			page = rbio_stripe_page(rbio, stripe, pagenr);
			/*
			 * the bio cache may have handed us an uptodate
			 * page.  If so, be happy and use it
			 */
			if (PageUptodate(page))
				continue;

			ret = rbio_add_io_page(rbio, &bio_list, page,
				       stripe, pagenr, rbio->stripe_len);
			if (ret)
				goto cleanup;
		}
	}

	bios_to_read = bio_list_size(&bio_list);
	if (!bios_to_read) {
		/*
		 * this can happen if others have merged with
		 * us, it means there is nothing left to read.
		 * But if there are missing devices it may not be
		 * safe to do the full stripe write yet.
		 */
		goto finish;
	}

	/*
	 * the bbio may be freed once we submit the last bio.  Make sure
	 * not to touch it after that
	 */
	atomic_set(&rbio->stripes_pending, bios_to_read);
	while (1) {
		bio = bio_list_pop(&bio_list);
		if (!bio)
			break;

		bio->bi_private = rbio;
		bio->bi_end_io = raid_rmw_end_io;
		bio_set_op_attrs(bio, REQ_OP_READ, 0);

		btrfs_bio_wq_end_io(rbio->fs_info, bio, BTRFS_WQ_ENDIO_RAID56);

		submit_bio(bio);
	}
	/* the actual write will happen once the reads are done */
	return 0;

cleanup:
	rbio_orig_end_io(rbio, -EIO);
	return -EIO;

finish:
	validate_rbio_for_rmw(rbio);
	return 0;
}

static void run_plug(struct btrfs_plug_cb *plug)
{
	struct btrfs_raid_bio *cur;
	struct btrfs_raid_bio *last = NULL;

	/*
	 * sort our plug list then try to merge
	 * everything we can in hopes of creating full
	 * stripes.
	 */
	list_sort(NULL, &plug->rbio_list, plug_cmp);
	while (!list_empty(&plug->rbio_list)) {
		cur = list_entry(plug->rbio_list.next,
				 struct btrfs_raid_bio, plug_list);
		list_del_init(&cur->plug_list);

		if (rbio_is_full(cur)) {
			/* we have a full stripe, send it down */
			full_stripe_write(cur);
			continue;
		}
		if (last) {
			if (rbio_can_merge(last, cur)) {
				merge_rbio(last, cur);
				__free_raid_bio(cur);
				continue;

			}
			__raid56_parity_write(last);
		}
		last = cur;
	}
	if (last) {
		__raid56_parity_write(last);
	}
	kfree(plug);
}
 */
static void __raid_recover_end_io(struct btrfs_raid_bio *rbio)
{
	int pagenr, stripe;
	void **pointers;
	int faila = -1, failb = -1;
	struct page *page;
	int err;
	int i;

	pointers = kcalloc(rbio->real_stripes, sizeof(void *), GFP_NOFS);
	if (!pointers) {
		err = -ENOMEM;
		goto cleanup_io;
	}

	faila = rbio->faila;
	failb = rbio->failb;

	if (rbio->operation == BTRFS_RBIO_READ_REBUILD ||
	    rbio->operation == BTRFS_RBIO_REBUILD_MISSING) {
		spin_lock_irq(&rbio->bio_list_lock);
		set_bit(RBIO_RMW_LOCKED_BIT, &rbio->flags);
		spin_unlock_irq(&rbio->bio_list_lock);
	}

	index_rbio_pages(rbio);

	for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
		/*
		 * Now we just use bitmap to mark the horizontal stripes in
		 * which we have data when doing parity scrub.
		 */
		if (rbio->operation == BTRFS_RBIO_PARITY_SCRUB &&
		    !test_bit(pagenr, rbio->dbitmap))
			continue;

		/* setup our array of pointers with pages
		 * from each stripe
		 */
		for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
			/*
			 * if we're rebuilding a read, we have to use
			 * pages from the bio list
			 */
			if ((rbio->operation == BTRFS_RBIO_READ_REBUILD ||
			     rbio->operation == BTRFS_RBIO_REBUILD_MISSING) &&
			    (stripe == faila || stripe == failb)) {
				page = page_in_rbio(rbio, stripe, pagenr, 0);
			} else {
				page = rbio_stripe_page(rbio, stripe, pagenr);
			}
			pointers[stripe] = kmap(page);
		}

		/* all raid6 handling here */
		if (rbio->bbio->map_type & BTRFS_BLOCK_GROUP_RAID6) {
			/*
			 * single failure, rebuild from parity raid5
			 * style
			 */
			if (failb < 0) {
				if (faila == rbio->nr_data) {
					/*
					 * Just the P stripe has failed, without
					 * a bad data or Q stripe.
					 * TODO, we should redo the xor here.
					 */
					err = -EIO;
					goto cleanup;
				}
				/*
				 * a single failure in raid6 is rebuilt
				 * in the pstripe code below
				 */
				goto pstripe;
			}

			/* make sure our ps and qs are in order */
			if (faila > failb) {
				int tmp = failb;
				failb = faila;
				faila = tmp;
			}

			/* if the q stripe is failed, do a pstripe reconstruction
			 * from the xors.
			 * If both the q stripe and the P stripe are failed, we're
			 * here due to a crc mismatch and we can't give them the
			 * data they want
			 */
			if (rbio->bbio->raid_map[failb] == RAID6_Q_STRIPE) {
				if (rbio->bbio->raid_map[faila] ==
				    RAID5_P_STRIPE) {
					err = -EIO;
					goto cleanup;
				}
				/*
				 * otherwise we have one bad data stripe and
				 * a good P stripe.  raid5!
				 */
				goto pstripe;
			}

			if (rbio->bbio->raid_map[failb] == RAID5_P_STRIPE) {
				raid6_datap_recov(rbio->real_stripes,
						  PAGE_SIZE, faila, pointers);
			} else {
				raid6_2data_recov(rbio->real_stripes,
						  PAGE_SIZE, faila, failb,
						  pointers);
			}
		} else {
			void *p;

			/* rebuild from P stripe here (raid5 or raid6) */
			BUG_ON(failb != -1);
pstripe:
			/* Copy parity block into failed block to start with */
			memcpy(pointers[faila],
			       pointers[rbio->nr_data],
			       PAGE_SIZE);

			/* rearrange the pointer array */
			p = pointers[faila];
			for (stripe = faila; stripe < rbio->nr_data - 1; stripe++)
				pointers[stripe] = pointers[stripe + 1];
			pointers[rbio->nr_data - 1] = p;

			/* xor in the rest */
			run_xor(pointers, rbio->nr_data - 1, PAGE_SIZE);
		}
		/* if we're doing this rebuild as part of an rmw, go through
		 * and set all of our private rbio pages in the
		 * failed stripes as uptodate.  This way finish_rmw will
		 * know they can be trusted.  If this was a read reconstruction,
		 * other endio functions will fiddle the uptodate bits
		 */
		if (rbio->operation == BTRFS_RBIO_WRITE) {
			for (i = 0;  i < rbio->stripe_npages; i++) {
				if (faila != -1) {
					page = rbio_stripe_page(rbio, faila, i);
					SetPageUptodate(page);
				}
				if (failb != -1) {
					page = rbio_stripe_page(rbio, failb, i);
					SetPageUptodate(page);
				}
			}
		}
		for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
			/*
			 * if we're rebuilding a read, we have to use
			 * pages from the bio list
			 */
			if ((rbio->operation == BTRFS_RBIO_READ_REBUILD ||
			     rbio->operation == BTRFS_RBIO_REBUILD_MISSING) &&
			    (stripe == faila || stripe == failb)) {
				page = page_in_rbio(rbio, stripe, pagenr, 0);
			} else {
				page = rbio_stripe_page(rbio, stripe, pagenr);
			}
			kunmap(page);
		}
	}

	err = 0;
cleanup:
	kfree(pointers);

cleanup_io:
	if (rbio->operation == BTRFS_RBIO_READ_REBUILD) {
		if (err == 0)
			cache_rbio_pages(rbio);
		else
			clear_bit(RBIO_CACHE_READY_BIT, &rbio->flags);

		rbio_orig_end_io(rbio, err);
	} else if (rbio->operation == BTRFS_RBIO_REBUILD_MISSING) {
		rbio_orig_end_io(rbio, err);
	} else if (err == 0) {
		rbio->faila = -1;
		rbio->failb = -1;

		if (rbio->operation == BTRFS_RBIO_WRITE)
			finish_rmw(rbio);
		else if (rbio->operation == BTRFS_RBIO_PARITY_SCRUB)
			finish_parity_scrub(rbio, 0);
		else
			BUG();
	} else {
		rbio_orig_end_io(rbio, err);
	}
}
 */
static int __raid56_parity_recover(struct btrfs_raid_bio *rbio)
{
	int bios_to_read = 0;
	struct bio_list bio_list;
	int ret;
	int pagenr;
	int stripe;
	struct bio *bio;

	bio_list_init(&bio_list);

	ret = alloc_rbio_pages(rbio);
	if (ret)
		goto cleanup;

	atomic_set(&rbio->error, 0);

	/*
	 * read everything that hasn't failed.  Thanks to the
	 * stripe cache, it is possible that some or all of these
	 * pages are going to be uptodate.
	 */
	for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
		if (rbio->faila == stripe || rbio->failb == stripe) {
			atomic_inc(&rbio->error);
			continue;
		}

		for (pagenr = 0; pagenr < rbio->stripe_npages; pagenr++) {
			struct page *p;

			/*
			 * the rmw code may have already read this
			 * page in
			 */
			p = rbio_stripe_page(rbio, stripe, pagenr);
			if (PageUptodate(p))
				continue;

			ret = rbio_add_io_page(rbio, &bio_list,
				       rbio_stripe_page(rbio, stripe, pagenr),
				       stripe, pagenr, rbio->stripe_len);
			if (ret < 0)
				goto cleanup;
		}
	}

	bios_to_read = bio_list_size(&bio_list);
	if (!bios_to_read) {
		/*
		 * we might have no bios to read just because the pages
		 * were up to date, or we might have no bios to read because
		 * the devices were gone.
		 */
		if (atomic_read(&rbio->error) <= rbio->bbio->max_errors) {
			__raid_recover_end_io(rbio);
			goto out;
		} else {
			goto cleanup;
		}
	}

	/*
	 * the bbio may be freed once we submit the last bio.  Make sure
	 * not to touch it after that
	 */
	atomic_set(&rbio->stripes_pending, bios_to_read);
	while (1) {
		bio = bio_list_pop(&bio_list);
		if (!bio)
			break;

		bio->bi_private = rbio;
		bio->bi_end_io = raid_recover_end_io;
		bio_set_op_attrs(bio, REQ_OP_READ, 0);

		btrfs_bio_wq_end_io(rbio->fs_info, bio, BTRFS_WQ_ENDIO_RAID56);

		submit_bio(bio);
	}
out:
	return 0;

cleanup:
	if (rbio->operation == BTRFS_RBIO_READ_REBUILD ||
	    rbio->operation == BTRFS_RBIO_REBUILD_MISSING)
		rbio_orig_end_io(rbio, -EIO);
	return -EIO;
}
			       struct btrfs_device *scrub_dev,
			       unsigned long *dbitmap, int stripe_nsectors)
{
	struct btrfs_raid_bio *rbio;
	int i;

	rbio = alloc_rbio(fs_info, bbio, stripe_len);
	if (IS_ERR(rbio))
		return NULL;
	bio_list_add(&rbio->bio_list, bio);
	/*
	 * This is a special bio which is used to hold the completion handler
	 * and make the scrub rbio is similar to the other types
	 */
	ASSERT(!bio->bi_iter.bi_size);
	rbio->operation = BTRFS_RBIO_PARITY_SCRUB;

	for (i = 0; i < rbio->real_stripes; i++) {
		if (bbio->stripes[i].dev == scrub_dev) {
			rbio->scrubp = i;
			break;
		}
	}

	/* Now we just support the sectorsize equals to page size */
	ASSERT(fs_info->sectorsize == PAGE_SIZE);
	ASSERT(rbio->stripe_npages == stripe_nsectors);
	bitmap_copy(rbio->dbitmap, dbitmap, stripe_nsectors);

	/*
	 * We have already increased bio_counter when getting bbio, record it
	 * so we can free it at rbio_orig_end_io().
	 */
	rbio->generic_bio_cnt = 1;

	return rbio;
}
 */
static int alloc_rbio_essential_pages(struct btrfs_raid_bio *rbio)
{
	int i;
	int bit;
	int index;
	struct page *page;

	for_each_set_bit(bit, rbio->dbitmap, rbio->stripe_npages) {
		for (i = 0; i < rbio->real_stripes; i++) {
			index = i * rbio->stripe_npages + bit;
			if (rbio->stripe_pages[index])
				continue;

			page = alloc_page(GFP_NOFS | __GFP_HIGHMEM);
			if (!page)
				return -ENOMEM;
			rbio->stripe_pages[index] = page;
		}
	}
	return 0;
}
static noinline void finish_parity_scrub(struct btrfs_raid_bio *rbio,
					 int need_check)
{
	struct btrfs_bio *bbio = rbio->bbio;
	void *pointers[rbio->real_stripes];
	DECLARE_BITMAP(pbitmap, rbio->stripe_npages);
	int nr_data = rbio->nr_data;
	int stripe;
	int pagenr;
	int p_stripe = -1;
	int q_stripe = -1;
	struct page *p_page = NULL;
	struct page *q_page = NULL;
	struct bio_list bio_list;
	struct bio *bio;
	int is_replace = 0;
	int ret;

	bio_list_init(&bio_list);

	if (rbio->real_stripes - rbio->nr_data == 1) {
		p_stripe = rbio->real_stripes - 1;
	} else if (rbio->real_stripes - rbio->nr_data == 2) {
		p_stripe = rbio->real_stripes - 2;
		q_stripe = rbio->real_stripes - 1;
	} else {
		BUG();
	}

	if (bbio->num_tgtdevs && bbio->tgtdev_map[rbio->scrubp]) {
		is_replace = 1;
		bitmap_copy(pbitmap, rbio->dbitmap, rbio->stripe_npages);
	}

	/*
	 * Because the higher layers(scrubber) are unlikely to
	 * use this area of the disk again soon, so don't cache
	 * it.
	 */
	clear_bit(RBIO_CACHE_READY_BIT, &rbio->flags);

	if (!need_check)
		goto writeback;

	p_page = alloc_page(GFP_NOFS | __GFP_HIGHMEM);
	if (!p_page)
		goto cleanup;
	SetPageUptodate(p_page);

	if (q_stripe != -1) {
		q_page = alloc_page(GFP_NOFS | __GFP_HIGHMEM);
		if (!q_page) {
			__free_page(p_page);
			goto cleanup;
		}
		SetPageUptodate(q_page);
	}

	atomic_set(&rbio->error, 0);

	for_each_set_bit(pagenr, rbio->dbitmap, rbio->stripe_npages) {
		struct page *p;
		void *parity;
		/* first collect one page from each data stripe */
		for (stripe = 0; stripe < nr_data; stripe++) {
			p = page_in_rbio(rbio, stripe, pagenr, 0);
			pointers[stripe] = kmap(p);
		}

		/* then add the parity stripe */
		pointers[stripe++] = kmap(p_page);

		if (q_stripe != -1) {

			/*
			 * raid6, add the qstripe and call the
			 * library function to fill in our p/q
			 */
			pointers[stripe++] = kmap(q_page);

			raid6_call.gen_syndrome(rbio->real_stripes, PAGE_SIZE,
						pointers);
		} else {
			/* raid5 */
			memcpy(pointers[nr_data], pointers[0], PAGE_SIZE);
			run_xor(pointers + 1, nr_data - 1, PAGE_SIZE);
		}

		/* Check scrubbing parity and repair it */
		p = rbio_stripe_page(rbio, rbio->scrubp, pagenr);
		parity = kmap(p);
		if (memcmp(parity, pointers[rbio->scrubp], PAGE_SIZE))
			memcpy(parity, pointers[rbio->scrubp], PAGE_SIZE);
		else
			/* Parity is right, needn't writeback */
			bitmap_clear(rbio->dbitmap, pagenr, 1);
		kunmap(p);

		for (stripe = 0; stripe < rbio->real_stripes; stripe++)
			kunmap(page_in_rbio(rbio, stripe, pagenr, 0));
	}

	__free_page(p_page);
	if (q_page)
		__free_page(q_page);

writeback:
	/*
	 * time to start writing.  Make bios for everything from the
	 * higher layers (the bio_list in our rbio) and our p/q.  Ignore
	 * everything else.
	 */
	for_each_set_bit(pagenr, rbio->dbitmap, rbio->stripe_npages) {
		struct page *page;

		page = rbio_stripe_page(rbio, rbio->scrubp, pagenr);
		ret = rbio_add_io_page(rbio, &bio_list,
			       page, rbio->scrubp, pagenr, rbio->stripe_len);
		if (ret)
			goto cleanup;
	}

	if (!is_replace)
		goto submit_write;

	for_each_set_bit(pagenr, pbitmap, rbio->stripe_npages) {
		struct page *page;

		page = rbio_stripe_page(rbio, rbio->scrubp, pagenr);
		ret = rbio_add_io_page(rbio, &bio_list, page,
				       bbio->tgtdev_map[rbio->scrubp],
				       pagenr, rbio->stripe_len);
		if (ret)
			goto cleanup;
	}

submit_write:
	nr_data = bio_list_size(&bio_list);
	if (!nr_data) {
		/* Every parity is right */
		rbio_orig_end_io(rbio, 0);
		return;
	}

	atomic_set(&rbio->stripes_pending, nr_data);

	while (1) {
		bio = bio_list_pop(&bio_list);
		if (!bio)
			break;

		bio->bi_private = rbio;
		bio->bi_end_io = raid_write_end_io;
		bio_set_op_attrs(bio, REQ_OP_WRITE, 0);

		submit_bio(bio);
	}
	return;

cleanup:
	rbio_orig_end_io(rbio, -EIO);
}

static void raid56_parity_scrub_stripe(struct btrfs_raid_bio *rbio)
{
	int bios_to_read = 0;
	struct bio_list bio_list;
	int ret;
	int pagenr;
	int stripe;
	struct bio *bio;

	ret = alloc_rbio_essential_pages(rbio);
	if (ret)
		goto cleanup;

	bio_list_init(&bio_list);

	atomic_set(&rbio->error, 0);
	/*
	 * build a list of bios to read all the missing parts of this
	 * stripe
	 */
	for (stripe = 0; stripe < rbio->real_stripes; stripe++) {
		for_each_set_bit(pagenr, rbio->dbitmap, rbio->stripe_npages) {
			struct page *page;
			/*
			 * we want to find all the pages missing from
			 * the rbio and read them from the disk.  If
			 * page_in_rbio finds a page in the bio list
			 * we don't need to read it off the stripe.
			 */
			page = page_in_rbio(rbio, stripe, pagenr, 1);
			if (page)
				continue;

			page = rbio_stripe_page(rbio, stripe, pagenr);
			/*
			 * the bio cache may have handed us an uptodate
			 * page.  If so, be happy and use it
			 */
			if (PageUptodate(page))
				continue;

			ret = rbio_add_io_page(rbio, &bio_list, page,
				       stripe, pagenr, rbio->stripe_len);
			if (ret)
				goto cleanup;
		}
	}

	bios_to_read = bio_list_size(&bio_list);
	if (!bios_to_read) {
		/*
		 * this can happen if others have merged with
		 * us, it means there is nothing left to read.
		 * But if there are missing devices it may not be
		 * safe to do the full stripe write yet.
		 */
		goto finish;
	}

	/*
	 * the bbio may be freed once we submit the last bio.  Make sure
	 * not to touch it after that
	 */
	atomic_set(&rbio->stripes_pending, bios_to_read);
	while (1) {
		bio = bio_list_pop(&bio_list);
		if (!bio)
			break;

		bio->bi_private = rbio;
		bio->bi_end_io = raid56_parity_scrub_end_io;
		bio_set_op_attrs(bio, REQ_OP_READ, 0);

		btrfs_bio_wq_end_io(rbio->fs_info, bio, BTRFS_WQ_ENDIO_RAID56);

		submit_bio(bio);
	}
	/* the actual write will happen once the reads are done */
	return;

cleanup:
	rbio_orig_end_io(rbio, -EIO);
	return;

finish:
	validate_rbio_for_parity_scrub(rbio);
}
