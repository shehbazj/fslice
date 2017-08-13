static int __btrfs_lookup_bio_sums(struct inode *inode, struct bio *bio,
				   u64 logical_offset, u32 *dst, int dio)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct bio_vec *bvec;
	struct btrfs_io_bio *btrfs_bio = btrfs_io_bio(bio);
	struct btrfs_csum_item *item = NULL;
	struct extent_io_tree *io_tree = &BTRFS_I(inode)->io_tree;
	struct btrfs_path *path;
	u8 *csum;
	u64 offset = 0;
	u64 item_start_offset = 0;
	u64 item_last_offset = 0;
	u64 disk_bytenr;
	u64 page_bytes_left;
	u32 diff;
	int nblocks;
	int count = 0, i;
	u16 csum_size = btrfs_super_csum_size(fs_info->super_copy);

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	nblocks = bio->bi_iter.bi_size >> inode->i_sb->s_blocksize_bits;
	if (!dst) {
		if (nblocks * csum_size > BTRFS_BIO_INLINE_CSUM_SIZE) {
			btrfs_bio->csum_allocated = kmalloc_array(nblocks,
					csum_size, GFP_NOFS);
			if (!btrfs_bio->csum_allocated) {
				btrfs_free_path(path);
				return -ENOMEM;
			}
			btrfs_bio->csum = btrfs_bio->csum_allocated;
			btrfs_bio->end_io = btrfs_io_bio_endio_readpage;
		} else {
			btrfs_bio->csum = btrfs_bio->csum_inline;
		}
		csum = btrfs_bio->csum;
	} else {
		csum = (u8 *)dst;
	}

	if (bio->bi_iter.bi_size > PAGE_SIZE * 8)
		path->reada = READA_FORWARD;

	WARN_ON(bio->bi_vcnt <= 0);

	/*
	 * the free space stuff is only read when it hasn't been
	 * updated in the current transaction.  So, we can safely
	 * read from the commit root and sidestep a nasty deadlock
	 * between reading the free space cache and updating the csum tree.
	 */
	if (btrfs_is_free_space_inode(BTRFS_I(inode))) {
		path->search_commit_root = 1;
		path->skip_locking = 1;
	}

	disk_bytenr = (u64)bio->bi_iter.bi_sector << 9;
	if (dio)
		offset = logical_offset;

	bio_for_each_segment_all(bvec, bio, i) {
		page_bytes_left = bvec->bv_len;
		if (count)
			goto next;

		if (!dio)
			offset = page_offset(bvec->bv_page) + bvec->bv_offset;
		count = btrfs_find_ordered_sum(inode, offset, disk_bytenr,
					       (u32 *)csum, nblocks);
		if (count)
			goto found;

		if (!item || disk_bytenr < item_start_offset ||
		    disk_bytenr >= item_last_offset) {
			struct btrfs_key found_key;
			u32 item_size;

			if (item)
				btrfs_release_path(path);
			item = btrfs_lookup_csum(NULL, fs_info->csum_root,
						 path, disk_bytenr, 0);
			if (IS_ERR(item)) {
				count = 1;
				memset(csum, 0, csum_size);
				if (BTRFS_I(inode)->root->root_key.objectid ==
				    BTRFS_DATA_RELOC_TREE_OBJECTID) {
					set_extent_bits(io_tree, offset,
						offset + fs_info->sectorsize - 1,
						EXTENT_NODATASUM);
				} else {
					btrfs_info_rl(fs_info,
						   "no csum found for inode %llu start %llu",
					       btrfs_ino(BTRFS_I(inode)), offset);
				}
				item = NULL;
				btrfs_release_path(path);
				goto found;
			}
			btrfs_item_key_to_cpu(path->nodes[0], &found_key,
					      path->slots[0]);

			item_start_offset = found_key.offset;
			item_size = btrfs_item_size_nr(path->nodes[0],
						       path->slots[0]);
			item_last_offset = item_start_offset +
				(item_size / csum_size) *
				fs_info->sectorsize;
			item = btrfs_item_ptr(path->nodes[0], path->slots[0],
					      struct btrfs_csum_item);
		}
		/*
		 * this byte range must be able to fit inside
		 * a single leaf so it will also fit inside a u32
		 */
		diff = disk_bytenr - item_start_offset;
		diff = diff / fs_info->sectorsize;
		diff = diff * csum_size;
		count = min_t(int, nblocks, (item_last_offset - disk_bytenr) >>
					    inode->i_sb->s_blocksize_bits);
		read_extent_buffer(path->nodes[0], csum,
				   ((unsigned long)item) + diff,
				   csum_size * count);
found:
		csum += count * csum_size;
		nblocks -= count;
next:
		while (count--) {
			disk_bytenr += fs_info->sectorsize;
			offset += fs_info->sectorsize;
			page_bytes_left -= fs_info->sectorsize;
			if (!page_bytes_left)
				break; /* move to next bio */
		}
	}

	WARN_ON_ONCE(count);
	btrfs_free_path(path);
	return 0;
}
int btrfs_lookup_csums_range(struct btrfs_root *root, u64 start, u64 end,
			     struct list_head *list, int search_commit)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_key key;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_ordered_sum *sums;
	struct btrfs_csum_item *item;
	LIST_HEAD(tmplist);
	unsigned long offset;
	int ret;
	size_t size;
	u64 csum_end;
	u16 csum_size = btrfs_super_csum_size(fs_info->super_copy);

	ASSERT(IS_ALIGNED(start, fs_info->sectorsize) &&
	       IS_ALIGNED(end + 1, fs_info->sectorsize));

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	if (search_commit) {
		path->skip_locking = 1;
		path->reada = READA_FORWARD;
		path->search_commit_root = 1;
	}

	key.objectid = BTRFS_EXTENT_CSUM_OBJECTID;
	key.offset = start;
	key.type = BTRFS_EXTENT_CSUM_KEY;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto fail;
	if (ret > 0 && path->slots[0] > 0) {
		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &key, path->slots[0] - 1);
		if (key.objectid == BTRFS_EXTENT_CSUM_OBJECTID &&
		    key.type == BTRFS_EXTENT_CSUM_KEY) {
			offset = (start - key.offset) >>
				 fs_info->sb->s_blocksize_bits;
			if (offset * csum_size <
			    btrfs_item_size_nr(leaf, path->slots[0] - 1))
				path->slots[0]--;
		}
	}

	while (start <= end) {
		leaf = path->nodes[0];
		if (path->slots[0] >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto fail;
			if (ret > 0)
				break;
			leaf = path->nodes[0];
		}

		btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
		if (key.objectid != BTRFS_EXTENT_CSUM_OBJECTID ||
		    key.type != BTRFS_EXTENT_CSUM_KEY ||
		    key.offset > end)
			break;

		if (key.offset > start)
			start = key.offset;

		size = btrfs_item_size_nr(leaf, path->slots[0]);
		csum_end = key.offset + (size / csum_size) * fs_info->sectorsize;
		if (csum_end <= start) {
			path->slots[0]++;
			continue;
		}

		csum_end = min(csum_end, end + 1);
		item = btrfs_item_ptr(path->nodes[0], path->slots[0],
				      struct btrfs_csum_item);
		while (start < csum_end) {
			size = min_t(size_t, csum_end - start,
				     MAX_ORDERED_SUM_BYTES(fs_info));
			sums = kzalloc(btrfs_ordered_sum_size(fs_info, size),
				       GFP_NOFS);
			if (!sums) {
				ret = -ENOMEM;
				goto fail;
			}

			sums->bytenr = start;
			sums->len = (int)size;

			offset = (start - key.offset) >>
				fs_info->sb->s_blocksize_bits;
			offset *= csum_size;
			size >>= fs_info->sb->s_blocksize_bits;

			read_extent_buffer(path->nodes[0],
					   sums->sums,
					   ((unsigned long)item) + offset,
					   csum_size * size);

			start += fs_info->sectorsize * size;
			list_add_tail(&sums->list, &tmplist);
		}
		path->slots[0]++;
	}
	ret = 0;
fail:
	while (ret < 0 && !list_empty(&tmplist)) {
		sums = list_entry(tmplist.next, struct btrfs_ordered_sum, list);
		list_del(&sums->list);
		kfree(sums);
	}
	list_splice_tail(&tmplist, list);

	btrfs_free_path(path);
	return ret;
}
int btrfs_csum_one_bio(struct inode *inode, struct bio *bio,
		       u64 file_start, int contig)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_ordered_sum *sums;
	struct btrfs_ordered_extent *ordered = NULL;
	char *data;
	struct bio_vec *bvec;
	int index;
	int nr_sectors;
	int i, j;
	unsigned long total_bytes = 0;
	unsigned long this_sum_bytes = 0;
	u64 offset;

	WARN_ON(bio->bi_vcnt <= 0);
	sums = kzalloc(btrfs_ordered_sum_size(fs_info, bio->bi_iter.bi_size),
		       GFP_NOFS);
	if (!sums)
		return -ENOMEM;

	sums->len = bio->bi_iter.bi_size;
	INIT_LIST_HEAD(&sums->list);

	if (contig)
		offset = file_start;
	else
		offset = 0; /* shut up gcc */

	sums->bytenr = (u64)bio->bi_iter.bi_sector << 9;
	index = 0;

	bio_for_each_segment_all(bvec, bio, j) {
		if (!contig)
			offset = page_offset(bvec->bv_page) + bvec->bv_offset;

		if (!ordered) {
			ordered = btrfs_lookup_ordered_extent(inode, offset);
			BUG_ON(!ordered); /* Logic error */
		}

		data = kmap_atomic(bvec->bv_page);

		nr_sectors = BTRFS_BYTES_TO_BLKS(fs_info,
						 bvec->bv_len + fs_info->sectorsize
						 - 1);

		for (i = 0; i < nr_sectors; i++) {
			if (offset >= ordered->file_offset + ordered->len ||
				offset < ordered->file_offset) {
				unsigned long bytes_left;

				kunmap_atomic(data);
				sums->len = this_sum_bytes;
				this_sum_bytes = 0;
				btrfs_add_ordered_sum(inode, ordered, sums);
				btrfs_put_ordered_extent(ordered);

				bytes_left = bio->bi_iter.bi_size - total_bytes;

				sums = kzalloc(btrfs_ordered_sum_size(fs_info, bytes_left),
					       GFP_NOFS);
				BUG_ON(!sums); /* -ENOMEM */
				sums->len = bytes_left;
				ordered = btrfs_lookup_ordered_extent(inode,
								offset);
				ASSERT(ordered); /* Logic error */
				sums->bytenr = ((u64)bio->bi_iter.bi_sector << 9)
					+ total_bytes;
				index = 0;

				data = kmap_atomic(bvec->bv_page);
			}

			sums->sums[index] = ~(u32)0;
			sums->sums[index]
				= btrfs_csum_data(data + bvec->bv_offset
						+ (i * fs_info->sectorsize),
						sums->sums[index],
						fs_info->sectorsize);
			btrfs_csum_final(sums->sums[index],
					(char *)(sums->sums + index));
			index++;
			offset += fs_info->sectorsize;
			this_sum_bytes += fs_info->sectorsize;
			total_bytes += fs_info->sectorsize;
		}

		kunmap_atomic(data);
	}
	this_sum_bytes = 0;
	btrfs_add_ordered_sum(inode, ordered, sums);
	btrfs_put_ordered_extent(ordered);
	return 0;
}
int btrfs_del_csums(struct btrfs_trans_handle *trans,
		    struct btrfs_fs_info *fs_info, u64 bytenr, u64 len)
{
	struct btrfs_root *root = fs_info->csum_root;
	struct btrfs_path *path;
	struct btrfs_key key;
	u64 end_byte = bytenr + len;
	u64 csum_end;
	struct extent_buffer *leaf;
	int ret;
	u16 csum_size = btrfs_super_csum_size(fs_info->super_copy);
	int blocksize_bits = fs_info->sb->s_blocksize_bits;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	while (1) {
		key.objectid = BTRFS_EXTENT_CSUM_OBJECTID;
		key.offset = end_byte - 1;
		key.type = BTRFS_EXTENT_CSUM_KEY;

		path->leave_spinning = 1;
		ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
		if (ret > 0) {
			if (path->slots[0] == 0)
				break;
			path->slots[0]--;
		} else if (ret < 0) {
			break;
		}

		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);

		if (key.objectid != BTRFS_EXTENT_CSUM_OBJECTID ||
		    key.type != BTRFS_EXTENT_CSUM_KEY) {
			break;
		}

		if (key.offset >= end_byte)
			break;

		csum_end = btrfs_item_size_nr(leaf, path->slots[0]) / csum_size;
		csum_end <<= blocksize_bits;
		csum_end += key.offset;

		/* this csum ends before we start, we're done */
		if (csum_end <= bytenr)
			break;

		/* delete the entire item, it is inside our range */
		if (key.offset >= bytenr && csum_end <= end_byte) {
			int del_nr = 1;

			/*
			 * Check how many csum items preceding this one in this
			 * leaf correspond to our range and then delete them all
			 * at once.
			 */
			if (key.offset > bytenr && path->slots[0] > 0) {
				int slot = path->slots[0] - 1;

				while (slot >= 0) {
					struct btrfs_key pk;

					btrfs_item_key_to_cpu(leaf, &pk, slot);
					if (pk.offset < bytenr ||
					    pk.type != BTRFS_EXTENT_CSUM_KEY ||
					    pk.objectid !=
					    BTRFS_EXTENT_CSUM_OBJECTID)
						break;
					path->slots[0] = slot;
					del_nr++;
					key.offset = pk.offset;
					slot--;
				}
			}
			ret = btrfs_del_items(trans, root, path,
					      path->slots[0], del_nr);
			if (ret)
				goto out;
			if (key.offset == bytenr)
				break;
		} else if (key.offset < bytenr && csum_end > end_byte) {
			unsigned long offset;
			unsigned long shift_len;
			unsigned long item_offset;
			/*
			 *        [ bytenr - len ]
			 *     [csum                ]
			 *
			 * Our bytes are in the middle of the csum,
			 * we need to split this item and insert a new one.
			 *
			 * But we can't drop the path because the
			 * csum could change, get removed, extended etc.
			 *
			 * The trick here is the max size of a csum item leaves
			 * enough room in the tree block for a single
			 * item header.  So, we split the item in place,
			 * adding a new header pointing to the existing
			 * bytes.  Then we loop around again and we have
			 * a nicely formed csum item that we can neatly
			 * truncate.
			 */
			offset = (bytenr - key.offset) >> blocksize_bits;
			offset *= csum_size;

			shift_len = (len >> blocksize_bits) * csum_size;

			item_offset = btrfs_item_ptr_offset(leaf,
							    path->slots[0]);

			memzero_extent_buffer(leaf, item_offset + offset,
					     shift_len);
			key.offset = bytenr;

			/*
			 * btrfs_split_item returns -EAGAIN when the
			 * item changed size or key
			 */
			ret = btrfs_split_item(trans, root, path, &key, offset);
			if (ret && ret != -EAGAIN) {
				btrfs_abort_transaction(trans, ret);
				goto out;
			}

			key.offset = end_byte - 1;
		} else {
			truncate_one_csum(fs_info, path, &key, bytenr, len);
			if (key.offset < bytenr)
				break;
		}
		btrfs_release_path(path);
	}
	ret = 0;
out:
	btrfs_free_path(path);
	return ret;
}
