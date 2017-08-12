				     ext4_lblk_t end_blk,
				     loff_t *offset)
{
	struct pagevec pvec;
	unsigned int blkbits;
	pgoff_t index;
	pgoff_t end;
	loff_t endoff;
	loff_t startoff;
	loff_t lastoff;
	int found = 0;

	blkbits = inode->i_sb->s_blocksize_bits;
	startoff = *offset;
	lastoff = startoff;
	endoff = (loff_t)end_blk << blkbits;

	index = startoff >> PAGE_SHIFT;
	end = (endoff - 1) >> PAGE_SHIFT;

	pagevec_init(&pvec, 0);
	do {
		int i, num;
		unsigned long nr_pages;

		num = min_t(pgoff_t, end - index, PAGEVEC_SIZE - 1) + 1;
		nr_pages = pagevec_lookup(&pvec, inode->i_mapping, index,
					  (pgoff_t)num);
		if (nr_pages == 0)
			break;

		for (i = 0; i < nr_pages; i++) {
			struct page *page = pvec.pages[i];
			struct buffer_head *bh, *head;

			/*
			 * If current offset is smaller than the page offset,
			 * there is a hole at this offset.
			 */
			if (whence == SEEK_HOLE && lastoff < endoff &&
			    lastoff < page_offset(pvec.pages[i])) {
				found = 1;
				*offset = lastoff;
				goto out;
			}

			if (page->index > end)
				goto out;

			lock_page(page);

			if (unlikely(page->mapping != inode->i_mapping)) {
				unlock_page(page);
				continue;
			}

			if (!page_has_buffers(page)) {
				unlock_page(page);
				continue;
			}

			if (page_has_buffers(page)) {
				lastoff = page_offset(page);
				bh = head = page_buffers(page);
				do {
					if (buffer_uptodate(bh) ||
					    buffer_unwritten(bh)) {
						if (whence == SEEK_DATA)
							found = 1;
					} else {
						if (whence == SEEK_HOLE)
							found = 1;
					}
					if (found) {
						*offset = max_t(loff_t,
							startoff, lastoff);
						unlock_page(page);
						goto out;
					}
					lastoff += bh->b_size;
					bh = bh->b_this_page;
				} while (bh != head);
			}

			lastoff = page_offset(page) + PAGE_SIZE;
			unlock_page(page);
		}

		/* The no. of pages is less than our desired, we are done. */
		if (nr_pages < num)
			break;

		index = pvec.pages[i - 1]->index + 1;
		pagevec_release(&pvec);
	} while (index <= end);

	if (whence == SEEK_HOLE && lastoff < endoff) {
		found = 1;
		*offset = lastoff;
	}
out:
	pagevec_release(&pvec);
	return found;
}
 */
static loff_t ext4_seek_data(struct file *file, loff_t offset, loff_t maxsize)
{
	struct inode *inode = file->f_mapping->host;
	struct extent_status es;
	ext4_lblk_t start, last, end;
	loff_t dataoff, isize;
	int blkbits;
	int ret;

	inode_lock(inode);

	isize = i_size_read(inode);
	if (offset >= isize) {
		inode_unlock(inode);
		return -ENXIO;
	}

	blkbits = inode->i_sb->s_blocksize_bits;
	start = offset >> blkbits;
	last = start;
	end = isize >> blkbits;
	dataoff = offset;

	do {
		ret = ext4_get_next_extent(inode, last, end - last + 1, &es);
		if (ret <= 0) {
			/* No extent found -> no data */
			if (ret == 0)
				ret = -ENXIO;
			inode_unlock(inode);
			return ret;
		}

		last = es.es_lblk;
		if (last != start)
			dataoff = (loff_t)last << blkbits;
		if (!ext4_es_is_unwritten(&es))
			break;

		/*
		 * If there is a unwritten extent at this offset,
		 * it will be as a data or a hole according to page
		 * cache that has data or not.
		 */
		if (ext4_find_unwritten_pgoff(inode, SEEK_DATA,
					      es.es_lblk + es.es_len, &dataoff))
			break;
		last += es.es_len;
		dataoff = (loff_t)last << blkbits;
		cond_resched();
	} while (last <= end);

	inode_unlock(inode);

	if (dataoff > isize)
		return -ENXIO;

	return vfs_setpos(file, dataoff, maxsize);
}
 */
static loff_t ext4_seek_hole(struct file *file, loff_t offset, loff_t maxsize)
{
	struct inode *inode = file->f_mapping->host;
	struct extent_status es;
	ext4_lblk_t start, last, end;
	loff_t holeoff, isize;
	int blkbits;
	int ret;

	inode_lock(inode);

	isize = i_size_read(inode);
	if (offset >= isize) {
		inode_unlock(inode);
		return -ENXIO;
	}

	blkbits = inode->i_sb->s_blocksize_bits;
	start = offset >> blkbits;
	last = start;
	end = isize >> blkbits;
	holeoff = offset;

	do {
		ret = ext4_get_next_extent(inode, last, end - last + 1, &es);
		if (ret < 0) {
			inode_unlock(inode);
			return ret;
		}
		/* Found a hole? */
		if (ret == 0 || es.es_lblk > last) {
			if (last != start)
				holeoff = (loff_t)last << blkbits;
			break;
		}
		/*
		 * If there is a unwritten extent at this offset,
		 * it will be as a data or a hole according to page
		 * cache that has data or not.
		 */
		if (ext4_es_is_unwritten(&es) &&
		    ext4_find_unwritten_pgoff(inode, SEEK_HOLE,
					      last + es.es_len, &holeoff))
			break;

		last += es.es_len;
		holeoff = (loff_t)last << blkbits;
		cond_resched();
	} while (last <= end);

	inode_unlock(inode);

	if (holeoff > isize)
		holeoff = isize;

	return vfs_setpos(file, holeoff, maxsize);
}
