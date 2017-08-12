				 ext4_lblk_t  *offsets,
				 Indirect chain[4], int *err)
{
	struct super_block *sb = inode->i_sb;
	Indirect *p = chain;
	struct buffer_head *bh;
	int ret = -EIO;

	*err = 0;
	/* i_data is not going away, no lock needed */
	add_chain(chain, NULL, EXT4_I(inode)->i_data + *offsets);
	if (!p->key)
		goto no_block;
	while (--depth) {
		bh = sb_getblk(sb, le32_to_cpu(p->key));
		if (unlikely(!bh)) {
			ret = -ENOMEM;
			goto failure;
		}

		if (!bh_uptodate_or_lock(bh)) {
			if (bh_submit_read(bh) < 0) {
				put_bh(bh);
				goto failure;
			}
			/* validate block references */
			if (ext4_check_indirect_blockref(inode, bh)) {
				put_bh(bh);
				goto failure;
			}
		}

		add_chain(++p, bh, (__le32 *)bh->b_data + *++offsets);
		/* Reader: end */
		if (!p->key)
			goto no_block;
	}
	return NULL;

failure:
	*err = ret;
no_block:
	return p;
}
 */
static ext4_fsblk_t ext4_find_near(struct inode *inode, Indirect *ind)
{
	struct ext4_inode_info *ei = EXT4_I(inode);
	__le32 *start = ind->bh ? (__le32 *) ind->bh->b_data : ei->i_data;
	__le32 *p;

	/* Try to find previous block */
	for (p = ind->p - 1; p >= start; p--) {
		if (*p)
			return le32_to_cpu(*p);
	}

	/* No such thing, so let's try location of indirect block */
	if (ind->bh)
		return ind->bh->b_blocknr;

	/*
	 * It is going to be referred to from the inode itself? OK, just put it
	 * into the same cylinder group then.
	 */
	return ext4_inode_to_goal_block(inode);
}
static int ext4_blks_to_allocate(Indirect *branch, int k, unsigned int blks,
				 int blocks_to_boundary)
{
	unsigned int count = 0;

	/*
	 * Simple case, [t,d]Indirect block(s) has not allocated yet
	 * then it's clear blocks on that path have not allocated
	 */
	if (k > 0) {
		/* right now we don't handle cross boundary allocation */
		if (blks < blocks_to_boundary + 1)
			count += blks;
		else
			count += blocks_to_boundary + 1;
		return count;
	}

	count++;
	while (count < blks && count <= blocks_to_boundary &&
		le32_to_cpu(*(branch[0].p + count)) == 0) {
		count++;
	}
	return count;
}
			     int indirect_blks, ext4_lblk_t *offsets,
			     Indirect *branch)
{
	struct buffer_head *		bh;
	ext4_fsblk_t			b, new_blocks[4];
	__le32				*p;
	int				i, j, err, len = 1;

	for (i = 0; i <= indirect_blks; i++) {
		if (i == indirect_blks) {
			new_blocks[i] = ext4_mb_new_blocks(handle, ar, &err);
		} else
			ar->goal = new_blocks[i] = ext4_new_meta_blocks(handle,
					ar->inode, ar->goal,
					ar->flags & EXT4_MB_DELALLOC_RESERVED,
					NULL, &err);
		if (err) {
			i--;
			goto failed;
		}
		branch[i].key = cpu_to_le32(new_blocks[i]);
		if (i == 0)
			continue;

		bh = branch[i].bh = sb_getblk(ar->inode->i_sb, new_blocks[i-1]);
		if (unlikely(!bh)) {
			err = -ENOMEM;
			goto failed;
		}
		lock_buffer(bh);
		BUFFER_TRACE(bh, "call get_create_access");
		err = ext4_journal_get_create_access(handle, bh);
		if (err) {
			unlock_buffer(bh);
			goto failed;
		}

		memset(bh->b_data, 0, bh->b_size);
		p = branch[i].p = (__le32 *) bh->b_data + offsets[i];
		b = new_blocks[i];

		if (i == indirect_blks)
			len = ar->len;
		for (j = 0; j < len; j++)
			*p++ = cpu_to_le32(b++);

		BUFFER_TRACE(bh, "marking uptodate");
		set_buffer_uptodate(bh);
		unlock_buffer(bh);

		BUFFER_TRACE(bh, "call ext4_handle_dirty_metadata");
		err = ext4_handle_dirty_metadata(handle, ar->inode, bh);
		if (err)
			goto failed;
	}
	return 0;
failed:
	for (; i >= 0; i--) {
		/*
		 * We want to ext4_forget() only freshly allocated indirect
		 * blocks.  Buffer for new_blocks[i-1] is at branch[i].bh and
		 * buffer at branch[0].bh is indirect block / inode already
		 * existing before ext4_alloc_branch() was called.
		 */
		if (i > 0 && i != indirect_blks && branch[i].bh)
			ext4_forget(handle, 1, ar->inode, branch[i].bh,
				    branch[i].bh->b_blocknr);
		ext4_free_blocks(handle, ar->inode, NULL, new_blocks[i],
				 (i == indirect_blks) ? ar->len : 1, 0);
	}
	return err;
}
			      struct ext4_allocation_request *ar,
			      Indirect *where, int num)
{
	int i;
	int err = 0;
	ext4_fsblk_t current_block;

	/*
	 * If we're splicing into a [td]indirect block (as opposed to the
	 * inode) then we need to get write access to the [td]indirect block
	 * before the splice.
	 */
	if (where->bh) {
		BUFFER_TRACE(where->bh, "get_write_access");
		err = ext4_journal_get_write_access(handle, where->bh);
		if (err)
			goto err_out;
	}
	/* That's it */

	*where->p = where->key;

	/*
	 * Update the host buffer_head or inode to point to more just allocated
	 * direct blocks blocks
	 */
	if (num == 0 && ar->len > 1) {
		current_block = le32_to_cpu(where->key) + 1;
		for (i = 1; i < ar->len; i++)
			*(where->p + i) = cpu_to_le32(current_block++);
	}

	/* We are done with atomic stuff, now do the rest of housekeeping */
	/* had we spliced it onto indirect block? */
	if (where->bh) {
		/*
		 * If we spliced it onto an indirect block, we haven't
		 * altered the inode.  Note however that if it is being spliced
		 * onto an indirect block at the very end of the file (the
		 * file is growing) then we *will* alter the inode to reflect
		 * the new i_size.  But that is not done here - it is done in
		 * generic_commit_write->__mark_inode_dirty->ext4_dirty_inode.
		 */
		jbd_debug(5, "splicing indirect only\n");
		BUFFER_TRACE(where->bh, "call ext4_handle_dirty_metadata");
		err = ext4_handle_dirty_metadata(handle, ar->inode, where->bh);
		if (err)
			goto err_out;
	} else {
		/*
		 * OK, we spliced it into the inode itself on a direct block.
		 */
		ext4_mark_inode_dirty(handle, ar->inode);
		jbd_debug(5, "splicing direct\n");
	}
	return err;

err_out:
	for (i = 1; i <= num; i++) {
		/*
		 * branch[i].bh is newly allocated, so there is no
		 * need to revoke the block, which is why we don't
		 * need to set EXT4_FREE_BLOCKS_METADATA.
		 */
		ext4_free_blocks(handle, ar->inode, where[i].bh, 0, 1,
				 EXT4_FREE_BLOCKS_FORGET);
	}
	ext4_free_blocks(handle, ar->inode, NULL, le32_to_cpu(where[num].key),
			 ar->len, 0);

	return err;
}
			struct ext4_map_blocks *map,
			int flags)
{
	struct ext4_allocation_request ar;
	int err = -EIO;
	ext4_lblk_t offsets[4];
	Indirect chain[4];
	Indirect *partial;
	int indirect_blks;
	int blocks_to_boundary = 0;
	int depth;
	int count = 0;
	ext4_fsblk_t first_block = 0;

	trace_ext4_ind_map_blocks_enter(inode, map->m_lblk, map->m_len, flags);
	J_ASSERT(!(ext4_test_inode_flag(inode, EXT4_INODE_EXTENTS)));
	J_ASSERT(handle != NULL || (flags & EXT4_GET_BLOCKS_CREATE) == 0);
	depth = ext4_block_to_path(inode, map->m_lblk, offsets,
				   &blocks_to_boundary);

	if (depth == 0)
		goto out;

	partial = ext4_get_branch(inode, depth, offsets, chain, &err);

	/* Simplest case - block found, no allocation needed */
	if (!partial) {
		first_block = le32_to_cpu(chain[depth - 1].key);
		count++;
		/*map more blocks*/
		while (count < map->m_len && count <= blocks_to_boundary) {
			ext4_fsblk_t blk;

			blk = le32_to_cpu(*(chain[depth-1].p + count));

			if (blk == first_block + count)
				count++;
			else
				break;
		}
		goto got_it;
	}

	/* Next simple case - plain lookup failed */
	if ((flags & EXT4_GET_BLOCKS_CREATE) == 0) {
		unsigned epb = inode->i_sb->s_blocksize / sizeof(u32);
		int i;

		/* Count number blocks in a subtree under 'partial' */
		count = 1;
		for (i = 0; partial + i != chain + depth - 1; i++)
			count *= epb;
		/* Fill in size of a hole we found */
		map->m_pblk = 0;
		map->m_len = min_t(unsigned int, map->m_len, count);
		goto cleanup;
	}

	/* Failed read of indirect block */
	if (err == -EIO)
		goto cleanup;

	/*
	 * Okay, we need to do block allocation.
	*/
	if (ext4_has_feature_bigalloc(inode->i_sb)) {
		EXT4_ERROR_INODE(inode, "Can't allocate blocks for "
				 "non-extent mapped inodes with bigalloc");
		return -EFSCORRUPTED;
	}

	/* Set up for the direct block allocation */
	memset(&ar, 0, sizeof(ar));
	ar.inode = inode;
	ar.logical = map->m_lblk;
	if (S_ISREG(inode->i_mode))
		ar.flags = EXT4_MB_HINT_DATA;
	if (flags & EXT4_GET_BLOCKS_DELALLOC_RESERVE)
		ar.flags |= EXT4_MB_DELALLOC_RESERVED;
	if (flags & EXT4_GET_BLOCKS_METADATA_NOFAIL)
		ar.flags |= EXT4_MB_USE_RESERVED;

	ar.goal = ext4_find_goal(inode, map->m_lblk, partial);

	/* the number of blocks need to allocate for [d,t]indirect blocks */
	indirect_blks = (chain + depth) - partial - 1;

	/*
	 * Next look up the indirect map to count the totoal number of
	 * direct blocks to allocate for this branch.
	 */
	ar.len = ext4_blks_to_allocate(partial, indirect_blks,
				       map->m_len, blocks_to_boundary);

	/*
	 * Block out ext4_truncate while we alter the tree
	 */
	err = ext4_alloc_branch(handle, &ar, indirect_blks,
				offsets + (partial - chain), partial);

	/*
	 * The ext4_splice_branch call will free and forget any buffers
	 * on the new chain if there is a failure, but that risks using
	 * up transaction credits, especially for bitmaps where the
	 * credits cannot be returned.  Can we handle this somehow?  We
	 * may need to return -EAGAIN upwards in the worst case.  --sct
	 */
	if (!err)
		err = ext4_splice_branch(handle, &ar, partial, indirect_blks);
	if (err)
		goto cleanup;

	map->m_flags |= EXT4_MAP_NEW;

	ext4_update_inode_fsync_trans(handle, inode, 1);
	count = ar.len;
got_it:
	map->m_flags |= EXT4_MAP_MAPPED;
	map->m_pblk = le32_to_cpu(chain[depth-1].key);
	map->m_len = count;
	if (count > blocks_to_boundary)
		map->m_flags |= EXT4_MAP_BOUNDARY;
	err = count;
	/* Clean up and exit */
	partial = chain + depth - 1;	/* the whole chain */
cleanup:
	while (partial > chain) {
		BUFFER_TRACE(partial->bh, "call brelse");
		brelse(partial->bh);
		partial--;
	}
out:
	trace_ext4_ind_map_blocks_exit(inode, flags, map, err);
	return err;
}
 */
static inline int all_zeroes(__le32 *p, __le32 *q)
{
	while (p < q)
		if (*p++)
			return 0;
	return 1;
}
				  ext4_lblk_t offsets[4], Indirect chain[4],
				  __le32 *top)
{
	Indirect *partial, *p;
	int k, err;

	*top = 0;
	/* Make k index the deepest non-null offset + 1 */
	for (k = depth; k > 1 && !offsets[k-1]; k--)
		;
	partial = ext4_get_branch(inode, k, offsets, chain, &err);
	/* Writer: pointers */
	if (!partial)
		partial = chain + k-1;
	/*
	 * If the branch acquired continuation since we've looked at it -
	 * fine, it should all survive and (new) top doesn't belong to us.
	 */
	if (!partial->key && *partial->p)
		/* Writer: end */
		goto no_top;
	for (p = partial; (p > chain) && all_zeroes((__le32 *) p->bh->b_data, p->p); p--)
		;
	/*
	 * OK, we've found the last block that must survive. The rest of our
	 * branch should be detached before unlocking. However, if that rest
	 * of branch is all ours and does not grow immediately from the inode
	 * it's easier to cheat and just decrement partial->p.
	 */
	if (p == chain + k - 1 && p > chain) {
		p->p--;
	} else {
		*top = *p->p;
		/* Nope, don't do this in ext4.  Must leave the tree intact */
#if 0
		*p->p = 0;
#endif
	}
	/* Writer: end */

	while (partial > p) {
		brelse(partial->bh);
		partial--;
	}
no_top:
	return partial;
}
			     unsigned long count, __le32 *first,
			     __le32 *last)
{
	__le32 *p;
	int	flags = EXT4_FREE_BLOCKS_VALIDATED;
	int	err;

	if (S_ISDIR(inode->i_mode) || S_ISLNK(inode->i_mode))
		flags |= EXT4_FREE_BLOCKS_FORGET | EXT4_FREE_BLOCKS_METADATA;
	else if (ext4_should_journal_data(inode))
		flags |= EXT4_FREE_BLOCKS_FORGET;

	if (!ext4_data_block_valid(EXT4_SB(inode->i_sb), block_to_free,
				   count)) {
		EXT4_ERROR_INODE(inode, "attempt to clear invalid "
				 "blocks %llu len %lu",
				 (unsigned long long) block_to_free, count);
		return 1;
	}

	if (try_to_extend_transaction(handle, inode)) {
		if (bh) {
			BUFFER_TRACE(bh, "call ext4_handle_dirty_metadata");
			err = ext4_handle_dirty_metadata(handle, inode, bh);
			if (unlikely(err))
				goto out_err;
		}
		err = ext4_mark_inode_dirty(handle, inode);
		if (unlikely(err))
			goto out_err;
		err = ext4_truncate_restart_trans(handle, inode,
					ext4_blocks_for_truncate(inode));
		if (unlikely(err))
			goto out_err;
		if (bh) {
			BUFFER_TRACE(bh, "retaking write access");
			err = ext4_journal_get_write_access(handle, bh);
			if (unlikely(err))
				goto out_err;
		}
	}

	for (p = first; p < last; p++)
		*p = 0;

	ext4_free_blocks(handle, inode, NULL, block_to_free, count, flags);
	return 0;
out_err:
	ext4_std_error(inode->i_sb, err);
	return err;
}
			   struct buffer_head *this_bh,
			   __le32 *first, __le32 *last)
{
	ext4_fsblk_t block_to_free = 0;    /* Starting block # of a run */
	unsigned long count = 0;	    /* Number of blocks in the run */
	__le32 *block_to_free_p = NULL;	    /* Pointer into inode/ind
					       corresponding to
					       block_to_free */
	ext4_fsblk_t nr;		    /* Current block # */
	__le32 *p;			    /* Pointer into inode/ind
					       for current block */
	int err = 0;

	if (this_bh) {				/* For indirect block */
		BUFFER_TRACE(this_bh, "get_write_access");
		err = ext4_journal_get_write_access(handle, this_bh);
		/* Important: if we can't update the indirect pointers
		 * to the blocks, we can't free them. */
		if (err)
			return;
	}

	for (p = first; p < last; p++) {
		nr = le32_to_cpu(*p);
		if (nr) {
			/* accumulate blocks to free if they're contiguous */
			if (count == 0) {
				block_to_free = nr;
				block_to_free_p = p;
				count = 1;
			} else if (nr == block_to_free + count) {
				count++;
			} else {
				err = ext4_clear_blocks(handle, inode, this_bh,
						        block_to_free, count,
						        block_to_free_p, p);
				if (err)
					break;
				block_to_free = nr;
				block_to_free_p = p;
				count = 1;
			}
		}
	}

	if (!err && count > 0)
		err = ext4_clear_blocks(handle, inode, this_bh, block_to_free,
					count, block_to_free_p, p);
	if (err < 0)
		/* fatal error */
		return;

	if (this_bh) {
		BUFFER_TRACE(this_bh, "call ext4_handle_dirty_metadata");

		/*
		 * The buffer head should have an attached journal head at this
		 * point. However, if the data is corrupted and an indirect
		 * block pointed to itself, it would have been detached when
		 * the block was cleared. Check for this instead of OOPSing.
		 */
		if ((EXT4_JOURNAL(inode) == NULL) || bh2jh(this_bh))
			ext4_handle_dirty_metadata(handle, inode, this_bh);
		else
			EXT4_ERROR_INODE(inode,
					 "circular indirect block detected at "
					 "block %llu",
				(unsigned long long) this_bh->b_blocknr);
	}
}
			       struct buffer_head *parent_bh,
			       __le32 *first, __le32 *last, int depth)
{
	ext4_fsblk_t nr;
	__le32 *p;

	if (ext4_handle_is_aborted(handle))
		return;

	if (depth--) {
		struct buffer_head *bh;
		int addr_per_block = EXT4_ADDR_PER_BLOCK(inode->i_sb);
		p = last;
		while (--p >= first) {
			nr = le32_to_cpu(*p);
			if (!nr)
				continue;		/* A hole */

			if (!ext4_data_block_valid(EXT4_SB(inode->i_sb),
						   nr, 1)) {
				EXT4_ERROR_INODE(inode,
						 "invalid indirect mapped "
						 "block %lu (level %d)",
						 (unsigned long) nr, depth);
				break;
			}

			/* Go read the buffer for the next level down */
			bh = sb_bread(inode->i_sb, nr);

			/*
			 * A read failure? Report error and clear slot
			 * (should be rare).
			 */
			if (!bh) {
				EXT4_ERROR_INODE_BLOCK(inode, nr,
						       "Read failure");
				continue;
			}

			/* This zaps the entire block.  Bottom up. */
			BUFFER_TRACE(bh, "free child branches");
			ext4_free_branches(handle, inode, bh,
					(__le32 *) bh->b_data,
					(__le32 *) bh->b_data + addr_per_block,
					depth);
			brelse(bh);

			/*
			 * Everything below this this pointer has been
			 * released.  Now let this top-of-subtree go.
			 *
			 * We want the freeing of this indirect block to be
			 * atomic in the journal with the updating of the
			 * bitmap block which owns it.  So make some room in
			 * the journal.
			 *
			 * We zero the parent pointer *after* freeing its
			 * pointee in the bitmaps, so if extend_transaction()
			 * for some reason fails to put the bitmap changes and
			 * the release into the same transaction, recovery
			 * will merely complain about releasing a free block,
			 * rather than leaking blocks.
			 */
			if (ext4_handle_is_aborted(handle))
				return;
			if (try_to_extend_transaction(handle, inode)) {
				ext4_mark_inode_dirty(handle, inode);
				ext4_truncate_restart_trans(handle, inode,
					    ext4_blocks_for_truncate(inode));
			}

			/*
			 * The forget flag here is critical because if
			 * we are journaling (and not doing data
			 * journaling), we have to make sure a revoke
			 * record is written to prevent the journal
			 * replay from overwriting the (former)
			 * indirect block if it gets reallocated as a
			 * data block.  This must happen in the same
			 * transaction where the data blocks are
			 * actually freed.
			 */
			ext4_free_blocks(handle, inode, NULL, nr, 1,
					 EXT4_FREE_BLOCKS_METADATA|
					 EXT4_FREE_BLOCKS_FORGET);

			if (parent_bh) {
				/*
				 * The block which we have just freed is
				 * pointed to by an indirect block: journal it
				 */
				BUFFER_TRACE(parent_bh, "get_write_access");
				if (!ext4_journal_get_write_access(handle,
								   parent_bh)){
					*p = 0;
					BUFFER_TRACE(parent_bh,
					"call ext4_handle_dirty_metadata");
					ext4_handle_dirty_metadata(handle,
								   inode,
								   parent_bh);
				}
			}
		}
	} else {
		/* We have reached the bottom of the tree. */
		BUFFER_TRACE(parent_bh, "free data blocks");
		ext4_free_data(handle, inode, parent_bh, first, last);
	}
}

void ext4_ind_truncate(handle_t *handle, struct inode *inode)
{
	struct ext4_inode_info *ei = EXT4_I(inode);
	__le32 *i_data = ei->i_data;
	int addr_per_block = EXT4_ADDR_PER_BLOCK(inode->i_sb);
	ext4_lblk_t offsets[4];
	Indirect chain[4];
	Indirect *partial;
	__le32 nr = 0;
	int n = 0;
	ext4_lblk_t last_block, max_block;
	unsigned blocksize = inode->i_sb->s_blocksize;

	last_block = (inode->i_size + blocksize-1)
					>> EXT4_BLOCK_SIZE_BITS(inode->i_sb);
	max_block = (EXT4_SB(inode->i_sb)->s_bitmap_maxbytes + blocksize-1)
					>> EXT4_BLOCK_SIZE_BITS(inode->i_sb);

	if (last_block != max_block) {
		n = ext4_block_to_path(inode, last_block, offsets, NULL);
		if (n == 0)
			return;
	}

	ext4_es_remove_extent(inode, last_block, EXT_MAX_BLOCKS - last_block);

	/*
	 * The orphan list entry will now protect us from any crash which
	 * occurs before the truncate completes, so it is now safe to propagate
	 * the new, shorter inode size (held for now in i_size) into the
	 * on-disk inode. We do this via i_disksize, which is the value which
	 * ext4 *really* writes onto the disk inode.
	 */
	ei->i_disksize = inode->i_size;

	if (last_block == max_block) {
		/*
		 * It is unnecessary to free any data blocks if last_block is
		 * equal to the indirect block limit.
		 */
		return;
	} else if (n == 1) {		/* direct blocks */
		ext4_free_data(handle, inode, NULL, i_data+offsets[0],
			       i_data + EXT4_NDIR_BLOCKS);
		goto do_indirects;
	}

	partial = ext4_find_shared(inode, n, offsets, chain, &nr);
	/* Kill the top of shared branch (not detached) */
	if (nr) {
		if (partial == chain) {
			/* Shared branch grows from the inode */
			ext4_free_branches(handle, inode, NULL,
					   &nr, &nr+1, (chain+n-1) - partial);
			*partial->p = 0;
			/*
			 * We mark the inode dirty prior to restart,
			 * and prior to stop.  No need for it here.
			 */
		} else {
			/* Shared branch grows from an indirect block */
			BUFFER_TRACE(partial->bh, "get_write_access");
			ext4_free_branches(handle, inode, partial->bh,
					partial->p,
					partial->p+1, (chain+n-1) - partial);
		}
	}
	/* Clear the ends of indirect blocks on the shared branch */
	while (partial > chain) {
		ext4_free_branches(handle, inode, partial->bh, partial->p + 1,
				   (__le32*)partial->bh->b_data+addr_per_block,
				   (chain+n-1) - partial);
		BUFFER_TRACE(partial->bh, "call brelse");
		brelse(partial->bh);
		partial--;
	}
do_indirects:
	/* Kill the remaining (whole) subtrees */
	switch (offsets[0]) {
	default:
		nr = i_data[EXT4_IND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 1);
			i_data[EXT4_IND_BLOCK] = 0;
		}
	case EXT4_IND_BLOCK:
		nr = i_data[EXT4_DIND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 2);
			i_data[EXT4_DIND_BLOCK] = 0;
		}
	case EXT4_DIND_BLOCK:
		nr = i_data[EXT4_TIND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 3);
			i_data[EXT4_TIND_BLOCK] = 0;
		}
	case EXT4_TIND_BLOCK:
		;
	}
}
int ext4_ind_remove_space(handle_t *handle, struct inode *inode,
			  ext4_lblk_t start, ext4_lblk_t end)
{
	struct ext4_inode_info *ei = EXT4_I(inode);
	__le32 *i_data = ei->i_data;
	int addr_per_block = EXT4_ADDR_PER_BLOCK(inode->i_sb);
	ext4_lblk_t offsets[4], offsets2[4];
	Indirect chain[4], chain2[4];
	Indirect *partial, *partial2;
	ext4_lblk_t max_block;
	__le32 nr = 0, nr2 = 0;
	int n = 0, n2 = 0;
	unsigned blocksize = inode->i_sb->s_blocksize;

	max_block = (EXT4_SB(inode->i_sb)->s_bitmap_maxbytes + blocksize-1)
					>> EXT4_BLOCK_SIZE_BITS(inode->i_sb);
	if (end >= max_block)
		end = max_block;
	if ((start >= end) || (start > max_block))
		return 0;

	n = ext4_block_to_path(inode, start, offsets, NULL);
	n2 = ext4_block_to_path(inode, end, offsets2, NULL);

	BUG_ON(n > n2);

	if ((n == 1) && (n == n2)) {
		/* We're punching only within direct block range */
		ext4_free_data(handle, inode, NULL, i_data + offsets[0],
			       i_data + offsets2[0]);
		return 0;
	} else if (n2 > n) {
		/*
		 * Start and end are on a different levels so we're going to
		 * free partial block at start, and partial block at end of
		 * the range. If there are some levels in between then
		 * do_indirects label will take care of that.
		 */

		if (n == 1) {
			/*
			 * Start is at the direct block level, free
			 * everything to the end of the level.
			 */
			ext4_free_data(handle, inode, NULL, i_data + offsets[0],
				       i_data + EXT4_NDIR_BLOCKS);
			goto end_range;
		}


		partial = ext4_find_shared(inode, n, offsets, chain, &nr);
		if (nr) {
			if (partial == chain) {
				/* Shared branch grows from the inode */
				ext4_free_branches(handle, inode, NULL,
					   &nr, &nr+1, (chain+n-1) - partial);
				*partial->p = 0;
			} else {
				/* Shared branch grows from an indirect block */
				BUFFER_TRACE(partial->bh, "get_write_access");
				ext4_free_branches(handle, inode, partial->bh,
					partial->p,
					partial->p+1, (chain+n-1) - partial);
			}
		}

		/*
		 * Clear the ends of indirect blocks on the shared branch
		 * at the start of the range
		 */
		while (partial > chain) {
			ext4_free_branches(handle, inode, partial->bh,
				partial->p + 1,
				(__le32 *)partial->bh->b_data+addr_per_block,
				(chain+n-1) - partial);
			BUFFER_TRACE(partial->bh, "call brelse");
			brelse(partial->bh);
			partial--;
		}

end_range:
		partial2 = ext4_find_shared(inode, n2, offsets2, chain2, &nr2);
		if (nr2) {
			if (partial2 == chain2) {
				/*
				 * Remember, end is exclusive so here we're at
				 * the start of the next level we're not going
				 * to free. Everything was covered by the start
				 * of the range.
				 */
				goto do_indirects;
			}
		} else {
			/*
			 * ext4_find_shared returns Indirect structure which
			 * points to the last element which should not be
			 * removed by truncate. But this is end of the range
			 * in punch_hole so we need to point to the next element
			 */
			partial2->p++;
		}

		/*
		 * Clear the ends of indirect blocks on the shared branch
		 * at the end of the range
		 */
		while (partial2 > chain2) {
			ext4_free_branches(handle, inode, partial2->bh,
					   (__le32 *)partial2->bh->b_data,
					   partial2->p,
					   (chain2+n2-1) - partial2);
			BUFFER_TRACE(partial2->bh, "call brelse");
			brelse(partial2->bh);
			partial2--;
		}
		goto do_indirects;
	}

	/* Punch happened within the same level (n == n2) */
	partial = ext4_find_shared(inode, n, offsets, chain, &nr);
	partial2 = ext4_find_shared(inode, n2, offsets2, chain2, &nr2);

	/* Free top, but only if partial2 isn't its subtree. */
	if (nr) {
		int level = min(partial - chain, partial2 - chain2);
		int i;
		int subtree = 1;

		for (i = 0; i <= level; i++) {
			if (offsets[i] != offsets2[i]) {
				subtree = 0;
				break;
			}
		}

		if (!subtree) {
			if (partial == chain) {
				/* Shared branch grows from the inode */
				ext4_free_branches(handle, inode, NULL,
						   &nr, &nr+1,
						   (chain+n-1) - partial);
				*partial->p = 0;
			} else {
				/* Shared branch grows from an indirect block */
				BUFFER_TRACE(partial->bh, "get_write_access");
				ext4_free_branches(handle, inode, partial->bh,
						   partial->p,
						   partial->p+1,
						   (chain+n-1) - partial);
			}
		}
	}

	if (!nr2) {
		/*
		 * ext4_find_shared returns Indirect structure which
		 * points to the last element which should not be
		 * removed by truncate. But this is end of the range
		 * in punch_hole so we need to point to the next element
		 */
		partial2->p++;
	}

	while (partial > chain || partial2 > chain2) {
		int depth = (chain+n-1) - partial;
		int depth2 = (chain2+n2-1) - partial2;

		if (partial > chain && partial2 > chain2 &&
		    partial->bh->b_blocknr == partial2->bh->b_blocknr) {
			/*
			 * We've converged on the same block. Clear the range,
			 * then we're done.
			 */
			ext4_free_branches(handle, inode, partial->bh,
					   partial->p + 1,
					   partial2->p,
					   (chain+n-1) - partial);
			BUFFER_TRACE(partial->bh, "call brelse");
			brelse(partial->bh);
			BUFFER_TRACE(partial2->bh, "call brelse");
			brelse(partial2->bh);
			return 0;
		}

		/*
		 * The start and end partial branches may not be at the same
		 * level even though the punch happened within one level. So, we
		 * give them a chance to arrive at the same level, then walk
		 * them in step with each other until we converge on the same
		 * block.
		 */
		if (partial > chain && depth <= depth2) {
			ext4_free_branches(handle, inode, partial->bh,
					   partial->p + 1,
					   (__le32 *)partial->bh->b_data+addr_per_block,
					   (chain+n-1) - partial);
			BUFFER_TRACE(partial->bh, "call brelse");
			brelse(partial->bh);
			partial--;
		}
		if (partial2 > chain2 && depth2 <= depth) {
			ext4_free_branches(handle, inode, partial2->bh,
					   (__le32 *)partial2->bh->b_data,
					   partial2->p,
					   (chain2+n2-1) - partial2);
			BUFFER_TRACE(partial2->bh, "call brelse");
			brelse(partial2->bh);
			partial2--;
		}
	}
	return 0;

do_indirects:
	/* Kill the remaining (whole) subtrees */
	switch (offsets[0]) {
	default:
		if (++n >= n2)
			return 0;
		nr = i_data[EXT4_IND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 1);
			i_data[EXT4_IND_BLOCK] = 0;
		}
	case EXT4_IND_BLOCK:
		if (++n >= n2)
			return 0;
		nr = i_data[EXT4_DIND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 2);
			i_data[EXT4_DIND_BLOCK] = 0;
		}
	case EXT4_DIND_BLOCK:
		if (++n >= n2)
			return 0;
		nr = i_data[EXT4_TIND_BLOCK];
		if (nr) {
			ext4_free_branches(handle, inode, NULL, &nr, &nr+1, 3);
			i_data[EXT4_TIND_BLOCK] = 0;
		}
	case EXT4_TIND_BLOCK:
		;
	}
	return 0;
}
