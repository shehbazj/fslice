
static int ext4_readdir(struct file *file, struct dir_context *ctx)
{
	unsigned int offset;
	int i;
	struct ext4_dir_entry_2 *de;
	int err;
	struct inode *inode = file_inode(file);
	struct super_block *sb = inode->i_sb;
	struct buffer_head *bh = NULL;
	int dir_has_error = 0;
	struct fscrypt_str fstr = FSTR_INIT(NULL, 0);

	if (ext4_encrypted_inode(inode)) {
		err = fscrypt_get_encryption_info(inode);
		if (err && err != -ENOKEY)
			return err;
	}

	if (is_dx_dir(inode)) {
		err = ext4_dx_readdir(file, ctx);
		if (err != ERR_BAD_DX_DIR) {
			return err;
		}
		/*
		 * We don't set the inode dirty flag since it's not
		 * critical that it get flushed back to the disk.
		 */
		ext4_clear_inode_flag(file_inode(file),
				      EXT4_INODE_INDEX);
	}

	if (ext4_has_inline_data(inode)) {
		int has_inline_data = 1;
		err = ext4_read_inline_dir(file, ctx,
					   &has_inline_data);
		if (has_inline_data)
			return err;
	}

	if (ext4_encrypted_inode(inode)) {
		err = fscrypt_fname_alloc_buffer(inode, EXT4_NAME_LEN, &fstr);
		if (err < 0)
			return err;
	}

	offset = ctx->pos & (sb->s_blocksize - 1);

	while (ctx->pos < inode->i_size) {
		struct ext4_map_blocks map;

		if (fatal_signal_pending(current)) {
			err = -ERESTARTSYS;
			goto errout;
		}
		cond_resched();
		map.m_lblk = ctx->pos >> EXT4_BLOCK_SIZE_BITS(sb);
		map.m_len = 1;
		err = ext4_map_blocks(NULL, inode, &map, 0);
		if (err > 0) {
			pgoff_t index = map.m_pblk >>
					(PAGE_SHIFT - inode->i_blkbits);
			if (!ra_has_index(&file->f_ra, index))
				page_cache_sync_readahead(
					sb->s_bdev->bd_inode->i_mapping,
					&file->f_ra, file,
					index, 1);
			file->f_ra.prev_pos = (loff_t)index << PAGE_SHIFT;
			bh = ext4_bread(NULL, inode, map.m_lblk, 0);
			if (IS_ERR(bh)) {
				err = PTR_ERR(bh);
				bh = NULL;
				goto errout;
			}
		}

		if (!bh) {
			if (!dir_has_error) {
				EXT4_ERROR_FILE(file, 0,
						"directory contains a "
						"hole at offset %llu",
					   (unsigned long long) ctx->pos);
				dir_has_error = 1;
			}
			/* corrupt size?  Maybe no more blocks to read */
			if (ctx->pos > inode->i_blocks << 9)
				break;
			ctx->pos += sb->s_blocksize - offset;
			continue;
		}

		/* Check the checksum */
		if (!buffer_verified(bh) &&
		    !ext4_dirent_csum_verify(inode,
				(struct ext4_dir_entry *)bh->b_data)) {
			EXT4_ERROR_FILE(file, 0, "directory fails checksum "
					"at offset %llu",
					(unsigned long long)ctx->pos);
			ctx->pos += sb->s_blocksize - offset;
			brelse(bh);
			bh = NULL;
			continue;
		}
		set_buffer_verified(bh);

		/* If the dir block has changed since the last call to
		 * readdir(2), then we might be pointing to an invalid
		 * dirent right now.  Scan from the start of the block
		 * to make sure. */
		if (file->f_version != inode->i_version) {
			for (i = 0; i < sb->s_blocksize && i < offset; ) {
				de = (struct ext4_dir_entry_2 *)
					(bh->b_data + i);
				/* It's too expensive to do a full
				 * dirent test each time round this
				 * loop, but we do have to test at
				 * least that it is non-zero.  A
				 * failure will be detected in the
				 * dirent test below. */
				if (ext4_rec_len_from_disk(de->rec_len,
					sb->s_blocksize) < EXT4_DIR_REC_LEN(1))
					break;
				i += ext4_rec_len_from_disk(de->rec_len,
							    sb->s_blocksize);
			}
			offset = i;
			ctx->pos = (ctx->pos & ~(sb->s_blocksize - 1))
				| offset;
			file->f_version = inode->i_version;
		}

		while (ctx->pos < inode->i_size
		       && offset < sb->s_blocksize) {
			de = (struct ext4_dir_entry_2 *) (bh->b_data + offset);
			if (ext4_check_dir_entry(inode, file, de, bh,
						 bh->b_data, bh->b_size,
						 offset)) {
				/*
				 * On error, skip to the next block
				 */
				ctx->pos = (ctx->pos |
						(sb->s_blocksize - 1)) + 1;
				break;
			}
			offset += ext4_rec_len_from_disk(de->rec_len,
					sb->s_blocksize);
			if (le32_to_cpu(de->inode)) {
				if (!ext4_encrypted_inode(inode)) {
					if (!dir_emit(ctx, de->name,
					    de->name_len,
					    le32_to_cpu(de->inode),
					    get_dtype(sb, de->file_type)))
						goto done;
				} else {
					int save_len = fstr.len;
					struct fscrypt_str de_name =
							FSTR_INIT(de->name,
								de->name_len);

					/* Directory is encrypted */
					err = fscrypt_fname_disk_to_usr(inode,
						0, 0, &de_name, &fstr);
					de_name = fstr;
					fstr.len = save_len;
					if (err)
						goto errout;
					if (!dir_emit(ctx,
					    de_name.name, de_name.len,
					    le32_to_cpu(de->inode),
					    get_dtype(sb, de->file_type)))
						goto done;
				}
			}
			ctx->pos += ext4_rec_len_from_disk(de->rec_len,
						sb->s_blocksize);
		}
		if ((ctx->pos < inode->i_size) && !dir_relax_shared(inode))
			goto done;
		brelse(bh);
		bh = NULL;
		offset = 0;
	}
done:
	err = 0;
errout:
#ifdef CONFIG_EXT4_FS_ENCRYPTION
	fscrypt_fname_free_buffer(&fstr);
#endif
	brelse(bh);
	return err;
}
 */
static void free_rb_tree_fname(struct rb_root *root)
{
	struct fname *fname, *next;

	rbtree_postorder_for_each_entry_safe(fname, next, root, rb_hash)
		while (fname) {
			struct fname *old = fname;
			fname = fname->next;
			kfree(old);
		}

	*root = RB_ROOT;
}
			    struct ext4_dir_entry_2 *dirent,
			    struct fscrypt_str *ent_name)
{
	struct rb_node **p, *parent = NULL;
	struct fname *fname, *new_fn;
	struct dir_private_info *info;
	int len;

	info = dir_file->private_data;
	p = &info->root.rb_node;

	/* Create and allocate the fname structure */
	len = sizeof(struct fname) + ent_name->len + 1;
	new_fn = kzalloc(len, GFP_KERNEL);
	if (!new_fn)
		return -ENOMEM;
	new_fn->hash = hash;
	new_fn->minor_hash = minor_hash;
	new_fn->inode = le32_to_cpu(dirent->inode);
	new_fn->name_len = ent_name->len;
	new_fn->file_type = dirent->file_type;
	memcpy(new_fn->name, ent_name->name, ent_name->len);
	new_fn->name[ent_name->len] = 0;

	while (*p) {
		parent = *p;
		fname = rb_entry(parent, struct fname, rb_hash);

		/*
		 * If the hash and minor hash match up, then we put
		 * them on a linked list.  This rarely happens...
		 */
		if ((new_fn->hash == fname->hash) &&
		    (new_fn->minor_hash == fname->minor_hash)) {
			new_fn->next = fname->next;
			fname->next = new_fn;
			return 0;
		}

		if (new_fn->hash < fname->hash)
			p = &(*p)->rb_left;
		else if (new_fn->hash > fname->hash)
			p = &(*p)->rb_right;
		else if (new_fn->minor_hash < fname->minor_hash)
			p = &(*p)->rb_left;
		else /* if (new_fn->minor_hash > fname->minor_hash) */
			p = &(*p)->rb_right;
	}

	rb_link_node(&new_fn->rb_hash, parent, p);
	rb_insert_color(&new_fn->rb_hash, &info->root);
	return 0;
}
static int call_filldir(struct file *file, struct dir_context *ctx,
			struct fname *fname)
{
	struct dir_private_info *info = file->private_data;
	struct inode *inode = file_inode(file);
	struct super_block *sb = inode->i_sb;

	if (!fname) {
		ext4_msg(sb, KERN_ERR, "%s:%d: inode #%lu: comm %s: "
			 "called with null fname?!?", __func__, __LINE__,
			 inode->i_ino, current->comm);
		return 0;
	}
	ctx->pos = hash2pos(file, fname->hash, fname->minor_hash);
	while (fname) {
		if (!dir_emit(ctx, fname->name,
				fname->name_len,
				fname->inode,
				get_dtype(sb, fname->file_type))) {
			info->extra_fname = fname;
			return 1;
		}
		fname = fname->next;
	}
	return 0;
}

static int ext4_dx_readdir(struct file *file, struct dir_context *ctx)
{
	struct dir_private_info *info = file->private_data;
	struct inode *inode = file_inode(file);
	struct fname *fname;
	int	ret;

	if (!info) {
		info = ext4_htree_create_dir_info(file, ctx->pos);
		if (!info)
			return -ENOMEM;
		file->private_data = info;
	}

	if (ctx->pos == ext4_get_htree_eof(file))
		return 0;	/* EOF */

	/* Some one has messed with f_pos; reset the world */
	if (info->last_pos != ctx->pos) {
		free_rb_tree_fname(&info->root);
		info->curr_node = NULL;
		info->extra_fname = NULL;
		info->curr_hash = pos2maj_hash(file, ctx->pos);
		info->curr_minor_hash = pos2min_hash(file, ctx->pos);
	}

	/*
	 * If there are any leftover names on the hash collision
	 * chain, return them first.
	 */
	if (info->extra_fname) {
		if (call_filldir(file, ctx, info->extra_fname))
			goto finished;
		info->extra_fname = NULL;
		goto next_node;
	} else if (!info->curr_node)
		info->curr_node = rb_first(&info->root);

	while (1) {
		/*
		 * Fill the rbtree if we have no more entries,
		 * or the inode has changed since we last read in the
		 * cached entries.
		 */
		if ((!info->curr_node) ||
		    (file->f_version != inode->i_version)) {
			info->curr_node = NULL;
			free_rb_tree_fname(&info->root);
			file->f_version = inode->i_version;
			ret = ext4_htree_fill_tree(file, info->curr_hash,
						   info->curr_minor_hash,
						   &info->next_hash);
			if (ret < 0)
				return ret;
			if (ret == 0) {
				ctx->pos = ext4_get_htree_eof(file);
				break;
			}
			info->curr_node = rb_first(&info->root);
		}

		fname = rb_entry(info->curr_node, struct fname, rb_hash);
		info->curr_hash = fname->hash;
		info->curr_minor_hash = fname->minor_hash;
		if (call_filldir(file, ctx, fname))
			break;
	next_node:
		info->curr_node = rb_next(info->curr_node);
		if (info->curr_node) {
			fname = rb_entry(info->curr_node, struct fname,
					 rb_hash);
			info->curr_hash = fname->hash;
			info->curr_minor_hash = fname->minor_hash;
		} else {
			if (info->next_hash == ~0) {
				ctx->pos = ext4_get_htree_eof(file);
				break;
			}
			info->curr_hash = info->next_hash;
			info->curr_minor_hash = 0;
		}
	}
finished:
	info->last_pos = ctx->pos;
	return 0;
}
int ext4_check_all_de(struct inode *dir, struct buffer_head *bh, void *buf,
		      int buf_size)
{
	struct ext4_dir_entry_2 *de;
	int rlen;
	unsigned int offset = 0;
	char *top;

	de = (struct ext4_dir_entry_2 *)buf;
	top = buf + buf_size;
	while ((char *) de < top) {
		if (ext4_check_dir_entry(dir, NULL, de, bh,
					 buf, buf_size, offset))
			return -EFSCORRUPTED;
		rlen = ext4_rec_len_from_disk(de->rec_len, buf_size);
		de = (struct ext4_dir_entry_2 *)((char *)de + rlen);
		offset += rlen;
	}
	if ((char *) de > top)
		return -EFSCORRUPTED;

	return 0;
}
