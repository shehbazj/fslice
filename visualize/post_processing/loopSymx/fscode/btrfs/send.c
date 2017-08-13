
static int write_buf(struct file *filp, const void *buf, u32 len, loff_t *off)
{
	int ret;
	mm_segment_t old_fs;
	u32 pos = 0;

	old_fs = get_fs();
	set_fs(KERNEL_DS);

	while (pos < len) {
		ret = vfs_write(filp, (__force const char __user *)buf + pos,
				len - pos, off);
		/* TODO handle that correctly */
		/*if (ret == -ERESTARTSYS) {
			continue;
		}*/
		if (ret < 0)
			goto out;
		if (ret == 0) {
			ret = -EIO;
			goto out;
		}
		pos += ret;
	}

	ret = 0;

out:
	set_fs(old_fs);
	return ret;
}

static int send_header(struct send_ctx *sctx)
{
	struct btrfs_stream_header hdr;

	strcpy(hdr.magic, BTRFS_SEND_STREAM_MAGIC);
	hdr.version = cpu_to_le32(BTRFS_SEND_STREAM_VERSION);

	return write_buf(sctx->send_filp, &hdr, sizeof(hdr),
					&sctx->send_off);
}
			     struct btrfs_key *found_key, int resolve,
			     iterate_inode_ref_t iterate, void *ctx)
{
	struct extent_buffer *eb = path->nodes[0];
	struct btrfs_item *item;
	struct btrfs_inode_ref *iref;
	struct btrfs_inode_extref *extref;
	struct btrfs_path *tmp_path;
	struct fs_path *p;
	u32 cur = 0;
	u32 total;
	int slot = path->slots[0];
	u32 name_len;
	char *start;
	int ret = 0;
	int num = 0;
	int index;
	u64 dir;
	unsigned long name_off;
	unsigned long elem_size;
	unsigned long ptr;

	p = fs_path_alloc_reversed();
	if (!p)
		return -ENOMEM;

	tmp_path = alloc_path_for_send();
	if (!tmp_path) {
		fs_path_free(p);
		return -ENOMEM;
	}


	if (found_key->type == BTRFS_INODE_REF_KEY) {
		ptr = (unsigned long)btrfs_item_ptr(eb, slot,
						    struct btrfs_inode_ref);
		item = btrfs_item_nr(slot);
		total = btrfs_item_size(eb, item);
		elem_size = sizeof(*iref);
	} else {
		ptr = btrfs_item_ptr_offset(eb, slot);
		total = btrfs_item_size_nr(eb, slot);
		elem_size = sizeof(*extref);
	}

	while (cur < total) {
		fs_path_reset(p);

		if (found_key->type == BTRFS_INODE_REF_KEY) {
			iref = (struct btrfs_inode_ref *)(ptr + cur);
			name_len = btrfs_inode_ref_name_len(eb, iref);
			name_off = (unsigned long)(iref + 1);
			index = btrfs_inode_ref_index(eb, iref);
			dir = found_key->offset;
		} else {
			extref = (struct btrfs_inode_extref *)(ptr + cur);
			name_len = btrfs_inode_extref_name_len(eb, extref);
			name_off = (unsigned long)&extref->name;
			index = btrfs_inode_extref_index(eb, extref);
			dir = btrfs_inode_extref_parent(eb, extref);
		}

		if (resolve) {
			start = btrfs_ref_to_path(root, tmp_path, name_len,
						  name_off, eb, dir,
						  p->buf, p->buf_len);
			if (IS_ERR(start)) {
				ret = PTR_ERR(start);
				goto out;
			}
			if (start < p->buf) {
				/* overflow , try again with larger buffer */
				ret = fs_path_ensure_buf(p,
						p->buf_len + p->buf - start);
				if (ret < 0)
					goto out;
				start = btrfs_ref_to_path(root, tmp_path,
							  name_len, name_off,
							  eb, dir,
							  p->buf, p->buf_len);
				if (IS_ERR(start)) {
					ret = PTR_ERR(start);
					goto out;
				}
				BUG_ON(start < p->buf);
			}
			p->start = start;
		} else {
			ret = fs_path_add_from_extent_buffer(p, eb, name_off,
							     name_len);
			if (ret < 0)
				goto out;
		}

		cur += elem_size + name_len;
		ret = iterate(num, dir, index, p, ctx);
		if (ret)
			goto out;
		num++;
	}

out:
	btrfs_free_path(tmp_path);
	fs_path_free(p);
	return ret;
}
			    struct btrfs_key *found_key,
			    iterate_dir_item_t iterate, void *ctx)
{
	int ret = 0;
	struct extent_buffer *eb;
	struct btrfs_item *item;
	struct btrfs_dir_item *di;
	struct btrfs_key di_key;
	char *buf = NULL;
	int buf_len;
	u32 name_len;
	u32 data_len;
	u32 cur;
	u32 len;
	u32 total;
	int slot;
	int num;
	u8 type;

	/*
	 * Start with a small buffer (1 page). If later we end up needing more
	 * space, which can happen for xattrs on a fs with a leaf size greater
	 * then the page size, attempt to increase the buffer. Typically xattr
	 * values are small.
	 */
	buf_len = PATH_MAX;
	buf = kmalloc(buf_len, GFP_KERNEL);
	if (!buf) {
		ret = -ENOMEM;
		goto out;
	}

	eb = path->nodes[0];
	slot = path->slots[0];
	item = btrfs_item_nr(slot);
	di = btrfs_item_ptr(eb, slot, struct btrfs_dir_item);
	cur = 0;
	len = 0;
	total = btrfs_item_size(eb, item);

	num = 0;
	while (cur < total) {
		name_len = btrfs_dir_name_len(eb, di);
		data_len = btrfs_dir_data_len(eb, di);
		type = btrfs_dir_type(eb, di);
		btrfs_dir_item_key_to_cpu(eb, di, &di_key);

		if (type == BTRFS_FT_XATTR) {
			if (name_len > XATTR_NAME_MAX) {
				ret = -ENAMETOOLONG;
				goto out;
			}
			if (name_len + data_len >
					BTRFS_MAX_XATTR_SIZE(root->fs_info)) {
				ret = -E2BIG;
				goto out;
			}
		} else {
			/*
			 * Path too long
			 */
			if (name_len + data_len > PATH_MAX) {
				ret = -ENAMETOOLONG;
				goto out;
			}
		}

		if (name_len + data_len > buf_len) {
			buf_len = name_len + data_len;
			if (is_vmalloc_addr(buf)) {
				vfree(buf);
				buf = NULL;
			} else {
				char *tmp = krealloc(buf, buf_len,
						GFP_KERNEL | __GFP_NOWARN);

				if (!tmp)
					kfree(buf);
				buf = tmp;
			}
			if (!buf) {
				buf = vmalloc(buf_len);
				if (!buf) {
					ret = -ENOMEM;
					goto out;
				}
			}
		}

		read_extent_buffer(eb, buf, (unsigned long)(di + 1),
				name_len + data_len);

		len = sizeof(*di) + name_len + data_len;
		di = (struct btrfs_dir_item *)((char *)di + len);
		cur += len;

		ret = iterate(num, &di_key, buf, name_len, buf + name_len,
				data_len, type, ctx);
		if (ret < 0)
			goto out;
		if (ret) {
			ret = 0;
			goto out;
		}

		num++;
	}

out:
	kvfree(buf);
	return ret;
}
			     u64 ino_size,
			     struct clone_root **found)
{
	struct btrfs_fs_info *fs_info = sctx->send_root->fs_info;
	int ret;
	int extent_type;
	u64 logical;
	u64 disk_byte;
	u64 num_bytes;
	u64 extent_item_pos;
	u64 flags = 0;
	struct btrfs_file_extent_item *fi;
	struct extent_buffer *eb = path->nodes[0];
	struct backref_ctx *backref_ctx = NULL;
	struct clone_root *cur_clone_root;
	struct btrfs_key found_key;
	struct btrfs_path *tmp_path;
	int compressed;
	u32 i;

	tmp_path = alloc_path_for_send();
	if (!tmp_path)
		return -ENOMEM;

	/* We only use this path under the commit sem */
	tmp_path->need_commit_sem = 0;

	backref_ctx = kmalloc(sizeof(*backref_ctx), GFP_KERNEL);
	if (!backref_ctx) {
		ret = -ENOMEM;
		goto out;
	}

	backref_ctx->path = tmp_path;

	if (data_offset >= ino_size) {
		/*
		 * There may be extents that lie behind the file's size.
		 * I at least had this in combination with snapshotting while
		 * writing large files.
		 */
		ret = 0;
		goto out;
	}

	fi = btrfs_item_ptr(eb, path->slots[0],
			struct btrfs_file_extent_item);
	extent_type = btrfs_file_extent_type(eb, fi);
	if (extent_type == BTRFS_FILE_EXTENT_INLINE) {
		ret = -ENOENT;
		goto out;
	}
	compressed = btrfs_file_extent_compression(eb, fi);

	num_bytes = btrfs_file_extent_num_bytes(eb, fi);
	disk_byte = btrfs_file_extent_disk_bytenr(eb, fi);
	if (disk_byte == 0) {
		ret = -ENOENT;
		goto out;
	}
	logical = disk_byte + btrfs_file_extent_offset(eb, fi);

	down_read(&fs_info->commit_root_sem);
	ret = extent_from_logical(fs_info, disk_byte, tmp_path,
				  &found_key, &flags);
	up_read(&fs_info->commit_root_sem);
	btrfs_release_path(tmp_path);

	if (ret < 0)
		goto out;
	if (flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) {
		ret = -EIO;
		goto out;
	}

	/*
	 * Setup the clone roots.
	 */
	for (i = 0; i < sctx->clone_roots_cnt; i++) {
		cur_clone_root = sctx->clone_roots + i;
		cur_clone_root->ino = (u64)-1;
		cur_clone_root->offset = 0;
		cur_clone_root->found_refs = 0;
	}

	backref_ctx->sctx = sctx;
	backref_ctx->found = 0;
	backref_ctx->cur_objectid = ino;
	backref_ctx->cur_offset = data_offset;
	backref_ctx->found_itself = 0;
	backref_ctx->extent_len = num_bytes;
	/*
	 * For non-compressed extents iterate_extent_inodes() gives us extent
	 * offsets that already take into account the data offset, but not for
	 * compressed extents, since the offset is logical and not relative to
	 * the physical extent locations. We must take this into account to
	 * avoid sending clone offsets that go beyond the source file's size,
	 * which would result in the clone ioctl failing with -EINVAL on the
	 * receiving end.
	 */
	if (compressed == BTRFS_COMPRESS_NONE)
		backref_ctx->data_offset = 0;
	else
		backref_ctx->data_offset = btrfs_file_extent_offset(eb, fi);

	/*
	 * The last extent of a file may be too large due to page alignment.
	 * We need to adjust extent_len in this case so that the checks in
	 * __iterate_backrefs work.
	 */
	if (data_offset + num_bytes >= ino_size)
		backref_ctx->extent_len = ino_size - data_offset;

	/*
	 * Now collect all backrefs.
	 */
	if (compressed == BTRFS_COMPRESS_NONE)
		extent_item_pos = logical - found_key.objectid;
	else
		extent_item_pos = 0;
	ret = iterate_extent_inodes(fs_info, found_key.objectid,
				    extent_item_pos, 1, __iterate_backrefs,
				    backref_ctx);

	if (ret < 0)
		goto out;

	if (!backref_ctx->found_itself) {
		/* found a bug in backref code? */
		ret = -EIO;
		btrfs_err(fs_info,
			  "did not find backref in send_root. inode=%llu, offset=%llu, disk_byte=%llu found extent=%llu",
			  ino, data_offset, disk_byte, found_key.objectid);
		goto out;
	}

	btrfs_debug(fs_info,
		    "find_extent_clone: data_offset=%llu, ino=%llu, num_bytes=%llu, logical=%llu",
		    data_offset, ino, num_bytes, logical);

	if (!backref_ctx->found)
		btrfs_debug(fs_info, "no clones found");

	cur_clone_root = NULL;
	for (i = 0; i < sctx->clone_roots_cnt; i++) {
		if (sctx->clone_roots[i].found_refs) {
			if (!cur_clone_root)
				cur_clone_root = sctx->clone_roots + i;
			else if (sctx->clone_roots[i].root == sctx->send_root)
				/* prefer clones from send_root over others */
				cur_clone_root = sctx->clone_roots + i;
		}

	}

	if (cur_clone_root) {
		*found = cur_clone_root;
		ret = 0;
	} else {
		ret = -ENOENT;
	}

out:
	btrfs_free_path(tmp_path);
	kfree(backref_ctx);
	return ret;
}
			   u64 ino, u64 gen,
			   struct fs_path *dest)
{
	int ret = 0;
	struct btrfs_path *path;
	struct btrfs_dir_item *di;
	char tmp[64];
	int len;
	u64 idx = 0;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	while (1) {
		len = snprintf(tmp, sizeof(tmp), "o%llu-%llu-%llu",
				ino, gen, idx);
		ASSERT(len < sizeof(tmp));

		di = btrfs_lookup_dir_item(NULL, sctx->send_root,
				path, BTRFS_FIRST_FREE_OBJECTID,
				tmp, strlen(tmp), 0);
		btrfs_release_path(path);
		if (IS_ERR(di)) {
			ret = PTR_ERR(di);
			goto out;
		}
		if (di) {
			/* not unique, try again */
			idx++;
			continue;
		}

		if (!sctx->parent_root) {
			/* unique */
			ret = 0;
			break;
		}

		di = btrfs_lookup_dir_item(NULL, sctx->parent_root,
				path, BTRFS_FIRST_FREE_OBJECTID,
				tmp, strlen(tmp), 0);
		btrfs_release_path(path);
		if (IS_ERR(di)) {
			ret = PTR_ERR(di);
			goto out;
		}
		if (di) {
			/* not unique, try again */
			idx++;
			continue;
		}
		/* unique */
		break;
	}

	ret = fs_path_add(dest, tmp, strlen(tmp));

out:
	btrfs_free_path(path);
	return ret;
}
 */
static void name_cache_clean_unused(struct send_ctx *sctx)
{
	struct name_cache_entry *nce;

	if (sctx->name_cache_size < SEND_CTX_NAME_CACHE_CLEAN_SIZE)
		return;

	while (sctx->name_cache_size > SEND_CTX_MAX_NAME_CACHE_SIZE) {
		nce = list_entry(sctx->name_cache_list.next,
				struct name_cache_entry, list);
		name_cache_delete(sctx, nce);
		kfree(nce);
	}
}

static void name_cache_free(struct send_ctx *sctx)
{
	struct name_cache_entry *nce;

	while (!list_empty(&sctx->name_cache_list)) {
		nce = list_entry(sctx->name_cache_list.next,
				struct name_cache_entry, list);
		name_cache_delete(sctx, nce);
		kfree(nce);
	}
}
static int get_cur_path(struct send_ctx *sctx, u64 ino, u64 gen,
			struct fs_path *dest)
{
	int ret = 0;
	struct fs_path *name = NULL;
	u64 parent_inode = 0;
	u64 parent_gen = 0;
	int stop = 0;

	name = fs_path_alloc();
	if (!name) {
		ret = -ENOMEM;
		goto out;
	}

	dest->reversed = 1;
	fs_path_reset(dest);

	while (!stop && ino != BTRFS_FIRST_FREE_OBJECTID) {
		struct waiting_dir_move *wdm;

		fs_path_reset(name);

		if (is_waiting_for_rm(sctx, ino)) {
			ret = gen_unique_name(sctx, ino, gen, name);
			if (ret < 0)
				goto out;
			ret = fs_path_add_path(dest, name);
			break;
		}

		wdm = get_waiting_dir_move(sctx, ino);
		if (wdm && wdm->orphanized) {
			ret = gen_unique_name(sctx, ino, gen, name);
			stop = 1;
		} else if (wdm) {
			ret = get_first_ref(sctx->parent_root, ino,
					    &parent_inode, &parent_gen, name);
		} else {
			ret = __get_cur_name_and_parent(sctx, ino, gen,
							&parent_inode,
							&parent_gen, name);
			if (ret)
				stop = 1;
		}

		if (ret < 0)
			goto out;

		ret = fs_path_add_path(dest, name);
		if (ret < 0)
			goto out;

		ino = parent_inode;
		gen = parent_gen;
	}

out:
	fs_path_free(name);
	if (!ret)
		fs_path_unreverse(dest);
	return ret;
}
 */
static int did_create_dir(struct send_ctx *sctx, u64 dir)
{
	int ret = 0;
	struct btrfs_path *path = NULL;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_key di_key;
	struct extent_buffer *eb;
	struct btrfs_dir_item *di;
	int slot;

	path = alloc_path_for_send();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	key.objectid = dir;
	key.type = BTRFS_DIR_INDEX_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, sctx->send_root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		eb = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(eb)) {
			ret = btrfs_next_leaf(sctx->send_root, path);
			if (ret < 0) {
				goto out;
			} else if (ret > 0) {
				ret = 0;
				break;
			}
			continue;
		}

		btrfs_item_key_to_cpu(eb, &found_key, slot);
		if (found_key.objectid != key.objectid ||
		    found_key.type != key.type) {
			ret = 0;
			goto out;
		}

		di = btrfs_item_ptr(eb, slot, struct btrfs_dir_item);
		btrfs_dir_item_key_to_cpu(eb, di, &di_key);

		if (di_key.type != BTRFS_ROOT_ITEM_KEY &&
		    di_key.objectid < sctx->send_progress) {
			ret = 1;
			goto out;
		}

		path->slots[0]++;
	}

out:
	btrfs_free_path(path);
	return ret;
}

static void __free_recorded_refs(struct list_head *head)
{
	struct recorded_ref *cur;

	while (!list_empty(head)) {
		cur = list_entry(head->next, struct recorded_ref, list);
		fs_path_free(cur->full_path);
		list_del(&cur->list);
		kfree(cur);
	}
}
static struct orphan_dir_info *
add_orphan_dir_info(struct send_ctx *sctx, u64 dir_ino)
{
	struct rb_node **p = &sctx->orphan_dirs.rb_node;
	struct rb_node *parent = NULL;
	struct orphan_dir_info *entry, *odi;

	odi = kmalloc(sizeof(*odi), GFP_KERNEL);
	if (!odi)
		return ERR_PTR(-ENOMEM);
	odi->ino = dir_ino;
	odi->gen = 0;

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct orphan_dir_info, node);
		if (dir_ino < entry->ino) {
			p = &(*p)->rb_left;
		} else if (dir_ino > entry->ino) {
			p = &(*p)->rb_right;
		} else {
			kfree(odi);
			return entry;
		}
	}

	rb_link_node(&odi->node, parent, p);
	rb_insert_color(&odi->node, &sctx->orphan_dirs);
	return odi;
}
static struct orphan_dir_info *
get_orphan_dir_info(struct send_ctx *sctx, u64 dir_ino)
{
	struct rb_node *n = sctx->orphan_dirs.rb_node;
	struct orphan_dir_info *entry;

	while (n) {
		entry = rb_entry(n, struct orphan_dir_info, node);
		if (dir_ino < entry->ino)
			n = n->rb_left;
		else if (dir_ino > entry->ino)
			n = n->rb_right;
		else
			return entry;
	}
	return NULL;
}
static int can_rmdir(struct send_ctx *sctx, u64 dir, u64 dir_gen,
		     u64 send_progress)
{
	int ret = 0;
	struct btrfs_root *root = sctx->parent_root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_key loc;
	struct btrfs_dir_item *di;

	/*
	 * Don't try to rmdir the top/root subvolume dir.
	 */
	if (dir == BTRFS_FIRST_FREE_OBJECTID)
		return 0;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	key.objectid = dir;
	key.type = BTRFS_DIR_INDEX_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		struct waiting_dir_move *dm;

		if (path->slots[0] >= btrfs_header_nritems(path->nodes[0])) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}
		btrfs_item_key_to_cpu(path->nodes[0], &found_key,
				      path->slots[0]);
		if (found_key.objectid != key.objectid ||
		    found_key.type != key.type)
			break;

		di = btrfs_item_ptr(path->nodes[0], path->slots[0],
				struct btrfs_dir_item);
		btrfs_dir_item_key_to_cpu(path->nodes[0], di, &loc);

		dm = get_waiting_dir_move(sctx, loc.objectid);
		if (dm) {
			struct orphan_dir_info *odi;

			odi = add_orphan_dir_info(sctx, dir);
			if (IS_ERR(odi)) {
				ret = PTR_ERR(odi);
				goto out;
			}
			odi->gen = dir_gen;
			dm->rmdir_ino = dir;
			ret = 0;
			goto out;
		}

		if (loc.objectid > send_progress) {
			struct orphan_dir_info *odi;

			odi = get_orphan_dir_info(sctx, dir);
			free_orphan_dir_info(sctx, odi);
			ret = 0;
			goto out;
		}

		path->slots[0]++;
	}

	ret = 1;

out:
	btrfs_free_path(path);
	return ret;
}

static int add_waiting_dir_move(struct send_ctx *sctx, u64 ino, bool orphanized)
{
	struct rb_node **p = &sctx->waiting_dir_moves.rb_node;
	struct rb_node *parent = NULL;
	struct waiting_dir_move *entry, *dm;

	dm = kmalloc(sizeof(*dm), GFP_KERNEL);
	if (!dm)
		return -ENOMEM;
	dm->ino = ino;
	dm->rmdir_ino = 0;
	dm->orphanized = orphanized;

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct waiting_dir_move, node);
		if (ino < entry->ino) {
			p = &(*p)->rb_left;
		} else if (ino > entry->ino) {
			p = &(*p)->rb_right;
		} else {
			kfree(dm);
			return -EEXIST;
		}
	}

	rb_link_node(&dm->node, parent, p);
	rb_insert_color(&dm->node, &sctx->waiting_dir_moves);
	return 0;
}
static struct waiting_dir_move *
get_waiting_dir_move(struct send_ctx *sctx, u64 ino)
{
	struct rb_node *n = sctx->waiting_dir_moves.rb_node;
	struct waiting_dir_move *entry;

	while (n) {
		entry = rb_entry(n, struct waiting_dir_move, node);
		if (ino < entry->ino)
			n = n->rb_left;
		else if (ino > entry->ino)
			n = n->rb_right;
		else
			return entry;
	}
	return NULL;
}
				struct list_head *deleted_refs,
				const bool is_orphan)
{
	struct rb_node **p = &sctx->pending_dir_moves.rb_node;
	struct rb_node *parent = NULL;
	struct pending_dir_move *entry = NULL, *pm;
	struct recorded_ref *cur;
	int exists = 0;
	int ret;

	pm = kmalloc(sizeof(*pm), GFP_KERNEL);
	if (!pm)
		return -ENOMEM;
	pm->parent_ino = parent_ino;
	pm->ino = ino;
	pm->gen = ino_gen;
	INIT_LIST_HEAD(&pm->list);
	INIT_LIST_HEAD(&pm->update_refs);
	RB_CLEAR_NODE(&pm->node);

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct pending_dir_move, node);
		if (parent_ino < entry->parent_ino) {
			p = &(*p)->rb_left;
		} else if (parent_ino > entry->parent_ino) {
			p = &(*p)->rb_right;
		} else {
			exists = 1;
			break;
		}
	}

	list_for_each_entry(cur, deleted_refs, list) {
		ret = dup_ref(cur, &pm->update_refs);
		if (ret < 0)
			goto out;
	}
	list_for_each_entry(cur, new_refs, list) {
		ret = dup_ref(cur, &pm->update_refs);
		if (ret < 0)
			goto out;
	}

	ret = add_waiting_dir_move(sctx, pm->ino, is_orphan);
	if (ret)
		goto out;

	if (exists) {
		list_add_tail(&pm->list, &entry->list);
	} else {
		rb_link_node(&pm->node, parent, p);
		rb_insert_color(&pm->node, &sctx->pending_dir_moves);
	}
	ret = 0;
out:
	if (ret) {
		__free_recorded_refs(&pm->update_refs);
		kfree(pm);
	}
	return ret;
}
static struct pending_dir_move *get_pending_dir_moves(struct send_ctx *sctx,
						      u64 parent_ino)
{
	struct rb_node *n = sctx->pending_dir_moves.rb_node;
	struct pending_dir_move *entry;

	while (n) {
		entry = rb_entry(n, struct pending_dir_move, node);
		if (parent_ino < entry->parent_ino)
			n = n->rb_left;
		else if (parent_ino > entry->parent_ino)
			n = n->rb_right;
		else
			return entry;
	}
	return NULL;
}
static int path_loop(struct send_ctx *sctx, struct fs_path *name,
		     u64 ino, u64 gen, u64 *ancestor_ino)
{
	int ret = 0;
	u64 parent_inode = 0;
	u64 parent_gen = 0;
	u64 start_ino = ino;

	*ancestor_ino = 0;
	while (ino != BTRFS_FIRST_FREE_OBJECTID) {
		fs_path_reset(name);

		if (is_waiting_for_rm(sctx, ino))
			break;
		if (is_waiting_for_move(sctx, ino)) {
			if (*ancestor_ino == 0)
				*ancestor_ino = ino;
			ret = get_first_ref(sctx->parent_root, ino,
					    &parent_inode, &parent_gen, name);
		} else {
			ret = __get_cur_name_and_parent(sctx, ino, gen,
							&parent_inode,
							&parent_gen, name);
			if (ret > 0) {
				ret = 0;
				break;
			}
		}
		if (ret < 0)
			break;
		if (parent_inode == start_ino) {
			ret = 1;
			if (*ancestor_ino == 0)
				*ancestor_ino = ino;
			break;
		}
		ino = parent_inode;
		gen = parent_gen;
	}
	return ret;
}

static int apply_children_dir_moves(struct send_ctx *sctx)
{
	struct pending_dir_move *pm;
	struct list_head stack;
	u64 parent_ino = sctx->cur_ino;
	int ret = 0;

	pm = get_pending_dir_moves(sctx, parent_ino);
	if (!pm)
		return 0;

	INIT_LIST_HEAD(&stack);
	tail_append_pending_moves(pm, &stack);

	while (!list_empty(&stack)) {
		pm = list_first_entry(&stack, struct pending_dir_move, list);
		parent_ino = pm->ino;
		ret = apply_dir_move(sctx, pm);
		free_pending_move(sctx, pm);
		if (ret)
			goto out;
		pm = get_pending_dir_moves(sctx, parent_ino);
		if (pm)
			tail_append_pending_moves(pm, &stack);
	}
	return 0;

out:
	while (!list_empty(&stack)) {
		pm = list_first_entry(&stack, struct pending_dir_move, list);
		free_pending_move(sctx, pm);
	}
	return ret;
}
		       const u64 ino2,
		       struct fs_path *fs_path)
{
	u64 ino = ino2;

	while (ino > BTRFS_FIRST_FREE_OBJECTID) {
		int ret;
		u64 parent;
		u64 parent_gen;

		fs_path_reset(fs_path);
		ret = get_first_ref(root, ino, &parent, &parent_gen, fs_path);
		if (ret < 0) {
			if (ret == -ENOENT && ino == ino2)
				ret = 0;
			return ret;
		}
		if (parent == ino1)
			return parent_gen == ino1_gen ? 1 : 0;
		ino = parent;
	}
	return 0;
}
				struct recorded_ref *parent_ref,
				const bool is_orphan)
{
	int ret = 0;
	u64 ino = parent_ref->dir;
	u64 ino_gen = parent_ref->dir_gen;
	u64 parent_ino_before, parent_ino_after;
	struct fs_path *path_before = NULL;
	struct fs_path *path_after = NULL;
	int len1, len2;

	path_after = fs_path_alloc();
	path_before = fs_path_alloc();
	if (!path_after || !path_before) {
		ret = -ENOMEM;
		goto out;
	}

	/*
	 * Our current directory inode may not yet be renamed/moved because some
	 * ancestor (immediate or not) has to be renamed/moved first. So find if
	 * such ancestor exists and make sure our own rename/move happens after
	 * that ancestor is processed to avoid path build infinite loops (done
	 * at get_cur_path()).
	 */
	while (ino > BTRFS_FIRST_FREE_OBJECTID) {
		u64 parent_ino_after_gen;

		if (is_waiting_for_move(sctx, ino)) {
			/*
			 * If the current inode is an ancestor of ino in the
			 * parent root, we need to delay the rename of the
			 * current inode, otherwise don't delayed the rename
			 * because we can end up with a circular dependency
			 * of renames, resulting in some directories never
			 * getting the respective rename operations issued in
			 * the send stream or getting into infinite path build
			 * loops.
			 */
			ret = is_ancestor(sctx->parent_root,
					  sctx->cur_ino, sctx->cur_inode_gen,
					  ino, path_before);
			if (ret)
				break;
		}

		fs_path_reset(path_before);
		fs_path_reset(path_after);

		ret = get_first_ref(sctx->send_root, ino, &parent_ino_after,
				    &parent_ino_after_gen, path_after);
		if (ret < 0)
			goto out;
		ret = get_first_ref(sctx->parent_root, ino, &parent_ino_before,
				    NULL, path_before);
		if (ret < 0 && ret != -ENOENT) {
			goto out;
		} else if (ret == -ENOENT) {
			ret = 0;
			break;
		}

		len1 = fs_path_len(path_before);
		len2 = fs_path_len(path_after);
		if (ino > sctx->cur_ino &&
		    (parent_ino_before != parent_ino_after || len1 != len2 ||
		     memcmp(path_before->start, path_after->start, len1))) {
			u64 parent_ino_gen;

			ret = get_inode_info(sctx->parent_root, ino, NULL,
					     &parent_ino_gen, NULL, NULL, NULL,
					     NULL);
			if (ret < 0)
				goto out;
			if (ino_gen == parent_ino_gen) {
				ret = 1;
				break;
			}
		}
		ino = parent_ino_after;
		ino_gen = parent_ino_after_gen;
	}

out:
	fs_path_free(path_before);
	fs_path_free(path_after);

	if (ret == 1) {
		ret = add_pending_dir_move(sctx,
					   sctx->cur_ino,
					   sctx->cur_inode_gen,
					   ino,
					   &sctx->new_refs,
					   &sctx->deleted_refs,
					   is_orphan);
		if (!ret)
			ret = 1;
	}

	return ret;
}
static int process_all_refs(struct send_ctx *sctx,
			    enum btrfs_compare_tree_result cmd)
{
	int ret;
	struct btrfs_root *root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct extent_buffer *eb;
	int slot;
	iterate_inode_ref_t cb;
	int pending_move = 0;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	if (cmd == BTRFS_COMPARE_TREE_NEW) {
		root = sctx->send_root;
		cb = __record_new_ref;
	} else if (cmd == BTRFS_COMPARE_TREE_DELETED) {
		root = sctx->parent_root;
		cb = __record_deleted_ref;
	} else {
		btrfs_err(sctx->send_root->fs_info,
				"Wrong command %d in process_all_refs", cmd);
		ret = -EINVAL;
		goto out;
	}

	key.objectid = sctx->cmp_key->objectid;
	key.type = BTRFS_INODE_REF_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		eb = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(eb)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(eb, &found_key, slot);

		if (found_key.objectid != key.objectid ||
		    (found_key.type != BTRFS_INODE_REF_KEY &&
		     found_key.type != BTRFS_INODE_EXTREF_KEY))
			break;

		ret = iterate_inode_ref(root, path, &found_key, 0, cb, sctx);
		if (ret < 0)
			goto out;

		path->slots[0]++;
	}
	btrfs_release_path(path);

	/*
	 * We don't actually care about pending_move as we are simply
	 * re-creating this inode and will be rename'ing it into place once we
	 * rename the parent directory.
	 */
	ret = process_recorded_refs(sctx, &pending_move);
out:
	btrfs_free_path(path);
	return ret;
}

static int process_all_new_xattrs(struct send_ctx *sctx)
{
	int ret;
	struct btrfs_root *root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct extent_buffer *eb;
	int slot;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	root = sctx->send_root;

	key.objectid = sctx->cmp_key->objectid;
	key.type = BTRFS_XATTR_ITEM_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		eb = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(eb)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0) {
				goto out;
			} else if (ret > 0) {
				ret = 0;
				break;
			}
			continue;
		}

		btrfs_item_key_to_cpu(eb, &found_key, slot);
		if (found_key.objectid != key.objectid ||
		    found_key.type != key.type) {
			ret = 0;
			goto out;
		}

		ret = iterate_dir_item(root, path, &found_key,
				       __process_new_xattr, sctx);
		if (ret < 0)
			goto out;

		path->slots[0]++;
	}

out:
	btrfs_free_path(path);
	return ret;
}

static ssize_t fill_read_buf(struct send_ctx *sctx, u64 offset, u32 len)
{
	struct btrfs_root *root = sctx->send_root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct inode *inode;
	struct page *page;
	char *addr;
	struct btrfs_key key;
	pgoff_t index = offset >> PAGE_SHIFT;
	pgoff_t last_index;
	unsigned pg_offset = offset & ~PAGE_MASK;
	ssize_t ret = 0;

	key.objectid = sctx->cur_ino;
	key.type = BTRFS_INODE_ITEM_KEY;
	key.offset = 0;

	inode = btrfs_iget(fs_info->sb, &key, root, NULL);
	if (IS_ERR(inode))
		return PTR_ERR(inode);

	if (offset + len > i_size_read(inode)) {
		if (offset > i_size_read(inode))
			len = 0;
		else
			len = offset - i_size_read(inode);
	}
	if (len == 0)
		goto out;

	last_index = (offset + len - 1) >> PAGE_SHIFT;

	/* initial readahead */
	memset(&sctx->ra, 0, sizeof(struct file_ra_state));
	file_ra_state_init(&sctx->ra, inode->i_mapping);
	btrfs_force_ra(inode->i_mapping, &sctx->ra, NULL, index,
		       last_index - index + 1);

	while (index <= last_index) {
		unsigned cur_len = min_t(unsigned, len,
					 PAGE_SIZE - pg_offset);
		page = find_or_create_page(inode->i_mapping, index, GFP_KERNEL);
		if (!page) {
			ret = -ENOMEM;
			break;
		}

		if (!PageUptodate(page)) {
			btrfs_readpage(NULL, page);
			lock_page(page);
			if (!PageUptodate(page)) {
				unlock_page(page);
				put_page(page);
				ret = -EIO;
				break;
			}
		}

		addr = kmap(page);
		memcpy(sctx->read_buf + ret, addr + pg_offset, cur_len);
		kunmap(page);
		unlock_page(page);
		put_page(page);
		index++;
		pg_offset = 0;
		len -= cur_len;
		ret += cur_len;
	}
out:
	iput(inode);
	return ret;
}

static int send_hole(struct send_ctx *sctx, u64 end)
{
	struct fs_path *p = NULL;
	u64 offset = sctx->cur_inode_last_extent;
	u64 len;
	int ret = 0;

	p = fs_path_alloc();
	if (!p)
		return -ENOMEM;
	ret = get_cur_path(sctx, sctx->cur_ino, sctx->cur_inode_gen, p);
	if (ret < 0)
		goto tlv_put_failure;
	memset(sctx->read_buf, 0, BTRFS_SEND_READ_SIZE);
	while (offset < end) {
		len = min_t(u64, end - offset, BTRFS_SEND_READ_SIZE);

		ret = begin_cmd(sctx, BTRFS_SEND_C_WRITE);
		if (ret < 0)
			break;
		TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH, p);
		TLV_PUT_U64(sctx, BTRFS_SEND_A_FILE_OFFSET, offset);
		TLV_PUT(sctx, BTRFS_SEND_A_DATA, sctx->read_buf, len);
		ret = send_cmd(sctx);
		if (ret < 0)
			break;
		offset += len;
	}
tlv_put_failure:
	fs_path_free(p);
	return ret;
}
			    const u64 offset,
			    const u64 len)
{
	u64 sent = 0;

	if (sctx->flags & BTRFS_SEND_FLAG_NO_FILE_DATA)
		return send_update_extent(sctx, offset, len);

	while (sent < len) {
		u64 size = len - sent;
		int ret;

		if (size > BTRFS_SEND_READ_SIZE)
			size = BTRFS_SEND_READ_SIZE;
		ret = send_write(sctx, offset + sent, size);
		if (ret < 0)
			return ret;
		if (!ret)
			break;
		sent += ret;
	}
	return 0;
}
		       u64 offset,
		       u64 len)
{
	struct btrfs_path *path;
	struct btrfs_key key;
	int ret;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	/*
	 * We can't send a clone operation for the entire range if we find
	 * extent items in the respective range in the source file that
	 * refer to different extents or if we find holes.
	 * So check for that and do a mix of clone and regular write/copy
	 * operations if needed.
	 *
	 * Example:
	 *
	 * mkfs.btrfs -f /dev/sda
	 * mount /dev/sda /mnt
	 * xfs_io -f -c "pwrite -S 0xaa 0K 100K" /mnt/foo
	 * cp --reflink=always /mnt/foo /mnt/bar
	 * xfs_io -c "pwrite -S 0xbb 50K 50K" /mnt/foo
	 * btrfs subvolume snapshot -r /mnt /mnt/snap
	 *
	 * If when we send the snapshot and we are processing file bar (which
	 * has a higher inode number than foo) we blindly send a clone operation
	 * for the [0, 100K[ range from foo to bar, the receiver ends up getting
	 * a file bar that matches the content of file foo - iow, doesn't match
	 * the content from bar in the original filesystem.
	 */
	key.objectid = clone_root->ino;
	key.type = BTRFS_EXTENT_DATA_KEY;
	key.offset = clone_root->offset;
	ret = btrfs_search_slot(NULL, clone_root->root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret > 0 && path->slots[0] > 0) {
		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0] - 1);
		if (key.objectid == clone_root->ino &&
		    key.type == BTRFS_EXTENT_DATA_KEY)
			path->slots[0]--;
	}

	while (true) {
		struct extent_buffer *leaf = path->nodes[0];
		int slot = path->slots[0];
		struct btrfs_file_extent_item *ei;
		u8 type;
		u64 ext_len;
		u64 clone_len;

		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(clone_root->root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);

		/*
		 * We might have an implicit trailing hole (NO_HOLES feature
		 * enabled). We deal with it after leaving this loop.
		 */
		if (key.objectid != clone_root->ino ||
		    key.type != BTRFS_EXTENT_DATA_KEY)
			break;

		ei = btrfs_item_ptr(leaf, slot, struct btrfs_file_extent_item);
		type = btrfs_file_extent_type(leaf, ei);
		if (type == BTRFS_FILE_EXTENT_INLINE) {
			ext_len = btrfs_file_extent_inline_len(leaf, slot, ei);
			ext_len = PAGE_ALIGN(ext_len);
		} else {
			ext_len = btrfs_file_extent_num_bytes(leaf, ei);
		}

		if (key.offset + ext_len <= clone_root->offset)
			goto next;

		if (key.offset > clone_root->offset) {
			/* Implicit hole, NO_HOLES feature enabled. */
			u64 hole_len = key.offset - clone_root->offset;

			if (hole_len > len)
				hole_len = len;
			ret = send_extent_data(sctx, offset, hole_len);
			if (ret < 0)
				goto out;

			len -= hole_len;
			if (len == 0)
				break;
			offset += hole_len;
			clone_root->offset += hole_len;
			data_offset += hole_len;
		}

		if (key.offset >= clone_root->offset + len)
			break;

		clone_len = min_t(u64, ext_len, len);

		if (btrfs_file_extent_disk_bytenr(leaf, ei) == disk_byte &&
		    btrfs_file_extent_offset(leaf, ei) == data_offset)
			ret = send_clone(sctx, offset, clone_len, clone_root);
		else
			ret = send_extent_data(sctx, offset, clone_len);

		if (ret < 0)
			goto out;

		len -= clone_len;
		if (len == 0)
			break;
		offset += clone_len;
		clone_root->offset += clone_len;
		data_offset += clone_len;
next:
		path->slots[0]++;
	}

	if (len > 0)
		ret = send_extent_data(sctx, offset, len);
	else
		ret = 0;
out:
	btrfs_free_path(path);
	return ret;
}
			       struct btrfs_path *left_path,
			       struct btrfs_key *ekey)
{
	int ret = 0;
	struct btrfs_key key;
	struct btrfs_path *path = NULL;
	struct extent_buffer *eb;
	int slot;
	struct btrfs_key found_key;
	struct btrfs_file_extent_item *ei;
	u64 left_disknr;
	u64 right_disknr;
	u64 left_offset;
	u64 right_offset;
	u64 left_offset_fixed;
	u64 left_len;
	u64 right_len;
	u64 left_gen;
	u64 right_gen;
	u8 left_type;
	u8 right_type;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	eb = left_path->nodes[0];
	slot = left_path->slots[0];
	ei = btrfs_item_ptr(eb, slot, struct btrfs_file_extent_item);
	left_type = btrfs_file_extent_type(eb, ei);

	if (left_type != BTRFS_FILE_EXTENT_REG) {
		ret = 0;
		goto out;
	}
	left_disknr = btrfs_file_extent_disk_bytenr(eb, ei);
	left_len = btrfs_file_extent_num_bytes(eb, ei);
	left_offset = btrfs_file_extent_offset(eb, ei);
	left_gen = btrfs_file_extent_generation(eb, ei);

	/*
	 * Following comments will refer to these graphics. L is the left
	 * extents which we are checking at the moment. 1-8 are the right
	 * extents that we iterate.
	 *
	 *       |-----L-----|
	 * |-1-|-2a-|-3-|-4-|-5-|-6-|
	 *
	 *       |-----L-----|
	 * |--1--|-2b-|...(same as above)
	 *
	 * Alternative situation. Happens on files where extents got split.
	 *       |-----L-----|
	 * |-----------7-----------|-6-|
	 *
	 * Alternative situation. Happens on files which got larger.
	 *       |-----L-----|
	 * |-8-|
	 * Nothing follows after 8.
	 */

	key.objectid = ekey->objectid;
	key.type = BTRFS_EXTENT_DATA_KEY;
	key.offset = ekey->offset;
	ret = btrfs_search_slot_for_read(sctx->parent_root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret) {
		ret = 0;
		goto out;
	}

	/*
	 * Handle special case where the right side has no extents at all.
	 */
	eb = path->nodes[0];
	slot = path->slots[0];
	btrfs_item_key_to_cpu(eb, &found_key, slot);
	if (found_key.objectid != key.objectid ||
	    found_key.type != key.type) {
		/* If we're a hole then just pretend nothing changed */
		ret = (left_disknr) ? 0 : 1;
		goto out;
	}

	/*
	 * We're now on 2a, 2b or 7.
	 */
	key = found_key;
	while (key.offset < ekey->offset + left_len) {
		ei = btrfs_item_ptr(eb, slot, struct btrfs_file_extent_item);
		right_type = btrfs_file_extent_type(eb, ei);
		if (right_type != BTRFS_FILE_EXTENT_REG &&
		    right_type != BTRFS_FILE_EXTENT_INLINE) {
			ret = 0;
			goto out;
		}

		if (right_type == BTRFS_FILE_EXTENT_INLINE) {
			right_len = btrfs_file_extent_inline_len(eb, slot, ei);
			right_len = PAGE_ALIGN(right_len);
		} else {
			right_len = btrfs_file_extent_num_bytes(eb, ei);
		}

		/*
		 * Are we at extent 8? If yes, we know the extent is changed.
		 * This may only happen on the first iteration.
		 */
		if (found_key.offset + right_len <= ekey->offset) {
			/* If we're a hole just pretend nothing changed */
			ret = (left_disknr) ? 0 : 1;
			goto out;
		}

		/*
		 * We just wanted to see if when we have an inline extent, what
		 * follows it is a regular extent (wanted to check the above
		 * condition for inline extents too). This should normally not
		 * happen but it's possible for example when we have an inline
		 * compressed extent representing data with a size matching
		 * the page size (currently the same as sector size).
		 */
		if (right_type == BTRFS_FILE_EXTENT_INLINE) {
			ret = 0;
			goto out;
		}

		right_disknr = btrfs_file_extent_disk_bytenr(eb, ei);
		right_offset = btrfs_file_extent_offset(eb, ei);
		right_gen = btrfs_file_extent_generation(eb, ei);

		left_offset_fixed = left_offset;
		if (key.offset < ekey->offset) {
			/* Fix the right offset for 2a and 7. */
			right_offset += ekey->offset - key.offset;
		} else {
			/* Fix the left offset for all behind 2a and 2b */
			left_offset_fixed += key.offset - ekey->offset;
		}

		/*
		 * Check if we have the same extent.
		 */
		if (left_disknr != right_disknr ||
		    left_offset_fixed != right_offset ||
		    left_gen != right_gen) {
			ret = 0;
			goto out;
		}

		/*
		 * Go to the next extent.
		 */
		ret = btrfs_next_item(sctx->parent_root, path);
		if (ret < 0)
			goto out;
		if (!ret) {
			eb = path->nodes[0];
			slot = path->slots[0];
			btrfs_item_key_to_cpu(eb, &found_key, slot);
		}
		if (ret || found_key.objectid != key.objectid ||
		    found_key.type != key.type) {
			key.offset += right_len;
			break;
		}
		if (found_key.offset != key.offset + right_len) {
			ret = 0;
			goto out;
		}
		key = found_key;
	}

	/*
	 * We're now behind the left extent (treat as unchanged) or at the end
	 * of the right side (treat as changed).
	 */
	if (key.offset >= ekey->offset + left_len)
		ret = 1;
	else
		ret = 0;


out:
	btrfs_free_path(path);
	return ret;
}
				   const u64 start,
				   const u64 end)
{
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_root *root = sctx->parent_root;
	u64 search_start = start;
	int ret;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	key.objectid = sctx->cur_ino;
	key.type = BTRFS_EXTENT_DATA_KEY;
	key.offset = search_start;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret > 0 && path->slots[0] > 0)
		path->slots[0]--;

	while (search_start < end) {
		struct extent_buffer *leaf = path->nodes[0];
		int slot = path->slots[0];
		struct btrfs_file_extent_item *fi;
		u64 extent_end;

		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);
		if (key.objectid < sctx->cur_ino ||
		    key.type < BTRFS_EXTENT_DATA_KEY)
			goto next;
		if (key.objectid > sctx->cur_ino ||
		    key.type > BTRFS_EXTENT_DATA_KEY ||
		    key.offset >= end)
			break;

		fi = btrfs_item_ptr(leaf, slot, struct btrfs_file_extent_item);
		if (btrfs_file_extent_type(leaf, fi) ==
		    BTRFS_FILE_EXTENT_INLINE) {
			u64 size = btrfs_file_extent_inline_len(leaf, slot, fi);

			extent_end = ALIGN(key.offset + size,
					   root->fs_info->sectorsize);
		} else {
			extent_end = key.offset +
				btrfs_file_extent_num_bytes(leaf, fi);
		}
		if (extent_end <= start)
			goto next;
		if (btrfs_file_extent_disk_bytenr(leaf, fi) == 0) {
			search_start = extent_end;
			goto next;
		}
		ret = 0;
		goto out;
next:
		path->slots[0]++;
	}
	ret = 1;
out:
	btrfs_free_path(path);
	return ret;
}

static int process_all_extents(struct send_ctx *sctx)
{
	int ret;
	struct btrfs_root *root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct extent_buffer *eb;
	int slot;

	root = sctx->send_root;
	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	key.objectid = sctx->cmp_key->objectid;
	key.type = BTRFS_EXTENT_DATA_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		eb = path->nodes[0];
		slot = path->slots[0];

		if (slot >= btrfs_header_nritems(eb)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0) {
				goto out;
			} else if (ret > 0) {
				ret = 0;
				break;
			}
			continue;
		}

		btrfs_item_key_to_cpu(eb, &found_key, slot);

		if (found_key.objectid != key.objectid ||
		    found_key.type != key.type) {
			ret = 0;
			goto out;
		}

		ret = process_extent(sctx, path, &found_key);
		if (ret < 0)
			goto out;

		path->slots[0]++;
	}

out:
	btrfs_free_path(path);
	return ret;
}
static int compare_refs(struct send_ctx *sctx, struct btrfs_path *path,
			struct btrfs_key *key)
{
	struct btrfs_inode_extref *extref;
	struct extent_buffer *leaf;
	u64 dirid = 0, last_dirid = 0;
	unsigned long ptr;
	u32 item_size;
	u32 cur_offset = 0;
	int ref_name_len;
	int ret = 0;

	/* Easy case, just check this one dirid */
	if (key->type == BTRFS_INODE_REF_KEY) {
		dirid = key->offset;

		ret = dir_changed(sctx, dirid);
		goto out;
	}

	leaf = path->nodes[0];
	item_size = btrfs_item_size_nr(leaf, path->slots[0]);
	ptr = btrfs_item_ptr_offset(leaf, path->slots[0]);
	while (cur_offset < item_size) {
		extref = (struct btrfs_inode_extref *)(ptr +
						       cur_offset);
		dirid = btrfs_inode_extref_parent(leaf, extref);
		ref_name_len = btrfs_inode_extref_name_len(leaf, extref);
		cur_offset += ref_name_len + sizeof(*extref);
		if (dirid == last_dirid)
			continue;
		ret = dir_changed(sctx, dirid);
		if (ret)
			break;
		last_dirid = dirid;
	}
out:
	return ret;
}

static int full_send_tree(struct send_ctx *sctx)
{
	int ret;
	struct btrfs_root *send_root = sctx->send_root;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_path *path;
	struct extent_buffer *eb;
	int slot;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	key.objectid = BTRFS_FIRST_FREE_OBJECTID;
	key.type = BTRFS_INODE_ITEM_KEY;
	key.offset = 0;

	ret = btrfs_search_slot_for_read(send_root, &key, path, 1, 0);
	if (ret < 0)
		goto out;
	if (ret)
		goto out_finish;

	while (1) {
		eb = path->nodes[0];
		slot = path->slots[0];
		btrfs_item_key_to_cpu(eb, &found_key, slot);

		ret = changed_cb(send_root, NULL, path, NULL,
				&found_key, BTRFS_COMPARE_TREE_NEW, sctx);
		if (ret < 0)
			goto out;

		key.objectid = found_key.objectid;
		key.type = found_key.type;
		key.offset = found_key.offset + 1;

		ret = btrfs_next_item(send_root, path);
		if (ret < 0)
			goto out;
		if (ret) {
			ret  = 0;
			break;
		}
	}

out_finish:
	ret = finish_inode_if_needed(sctx, 1);

out:
	btrfs_free_path(path);
	return ret;
}
 */
static int ensure_commit_roots_uptodate(struct send_ctx *sctx)
{
	int i;
	struct btrfs_trans_handle *trans = NULL;

again:
	if (sctx->parent_root &&
	    sctx->parent_root->node != sctx->parent_root->commit_root)
		goto commit_trans;

	for (i = 0; i < sctx->clone_roots_cnt; i++)
		if (sctx->clone_roots[i].root->node !=
		    sctx->clone_roots[i].root->commit_root)
			goto commit_trans;

	if (trans)
		return btrfs_end_transaction(trans);

	return 0;

commit_trans:
	/* Use any root, all fs roots will get their commit roots updated. */
	if (!trans) {
		trans = btrfs_join_transaction(sctx->send_root);
		if (IS_ERR(trans))
			return PTR_ERR(trans);
		goto again;
	}

	return btrfs_commit_transaction(trans);
}

long btrfs_ioctl_send(struct file *mnt_file, void __user *arg_)
{
	int ret = 0;
	struct btrfs_root *send_root = BTRFS_I(file_inode(mnt_file))->root;
	struct btrfs_fs_info *fs_info = send_root->fs_info;
	struct btrfs_root *clone_root;
	struct btrfs_ioctl_send_args *arg = NULL;
	struct btrfs_key key;
	struct send_ctx *sctx = NULL;
	u32 i;
	u64 *clone_sources_tmp = NULL;
	int clone_sources_to_rollback = 0;
	unsigned alloc_size;
	int sort_clone_roots = 0;
	int index;

	if (!capable(CAP_SYS_ADMIN))
		return -EPERM;

	/*
	 * The subvolume must remain read-only during send, protect against
	 * making it RW. This also protects against deletion.
	 */
	spin_lock(&send_root->root_item_lock);
	send_root->send_in_progress++;
	spin_unlock(&send_root->root_item_lock);

	/*
	 * This is done when we lookup the root, it should already be complete
	 * by the time we get here.
	 */
	WARN_ON(send_root->orphan_cleanup_state != ORPHAN_CLEANUP_DONE);

	/*
	 * Userspace tools do the checks and warn the user if it's
	 * not RO.
	 */
	if (!btrfs_root_readonly(send_root)) {
		ret = -EPERM;
		goto out;
	}

	arg = memdup_user(arg_, sizeof(*arg));
	if (IS_ERR(arg)) {
		ret = PTR_ERR(arg);
		arg = NULL;
		goto out;
	}

	/*
	 * Check that we don't overflow at later allocations, we request
	 * clone_sources_count + 1 items, and compare to unsigned long inside
	 * access_ok.
	 */
	if (arg->clone_sources_count >
	    ULONG_MAX / sizeof(struct clone_root) - 1) {
		ret = -EINVAL;
		goto out;
	}

	if (!access_ok(VERIFY_READ, arg->clone_sources,
			sizeof(*arg->clone_sources) *
			arg->clone_sources_count)) {
		ret = -EFAULT;
		goto out;
	}

	if (arg->flags & ~BTRFS_SEND_FLAG_MASK) {
		ret = -EINVAL;
		goto out;
	}

	sctx = kzalloc(sizeof(struct send_ctx), GFP_KERNEL);
	if (!sctx) {
		ret = -ENOMEM;
		goto out;
	}

	INIT_LIST_HEAD(&sctx->new_refs);
	INIT_LIST_HEAD(&sctx->deleted_refs);
	INIT_RADIX_TREE(&sctx->name_cache, GFP_KERNEL);
	INIT_LIST_HEAD(&sctx->name_cache_list);

	sctx->flags = arg->flags;

	sctx->send_filp = fget(arg->send_fd);
	if (!sctx->send_filp) {
		ret = -EBADF;
		goto out;
	}

	sctx->send_root = send_root;
	/*
	 * Unlikely but possible, if the subvolume is marked for deletion but
	 * is slow to remove the directory entry, send can still be started
	 */
	if (btrfs_root_dead(sctx->send_root)) {
		ret = -EPERM;
		goto out;
	}

	sctx->clone_roots_cnt = arg->clone_sources_count;

	sctx->send_max_size = BTRFS_SEND_BUF_SIZE;
	sctx->send_buf = kvmalloc(sctx->send_max_size, GFP_KERNEL);
	if (!sctx->send_buf) {
		ret = -ENOMEM;
		goto out;
	}

	sctx->read_buf = kvmalloc(BTRFS_SEND_READ_SIZE, GFP_KERNEL);
	if (!sctx->read_buf) {
		ret = -ENOMEM;
		goto out;
	}

	sctx->pending_dir_moves = RB_ROOT;
	sctx->waiting_dir_moves = RB_ROOT;
	sctx->orphan_dirs = RB_ROOT;

	alloc_size = sizeof(struct clone_root) * (arg->clone_sources_count + 1);

	sctx->clone_roots = kzalloc(alloc_size, GFP_KERNEL | __GFP_NOWARN);
	if (!sctx->clone_roots) {
		sctx->clone_roots = vzalloc(alloc_size);
		if (!sctx->clone_roots) {
			ret = -ENOMEM;
			goto out;
		}
	}

	alloc_size = arg->clone_sources_count * sizeof(*arg->clone_sources);

	if (arg->clone_sources_count) {
		clone_sources_tmp = kvmalloc(alloc_size, GFP_KERNEL);
		if (!clone_sources_tmp) {
			ret = -ENOMEM;
			goto out;
		}

		ret = copy_from_user(clone_sources_tmp, arg->clone_sources,
				alloc_size);
		if (ret) {
			ret = -EFAULT;
			goto out;
		}

		for (i = 0; i < arg->clone_sources_count; i++) {
			key.objectid = clone_sources_tmp[i];
			key.type = BTRFS_ROOT_ITEM_KEY;
			key.offset = (u64)-1;

			index = srcu_read_lock(&fs_info->subvol_srcu);

			clone_root = btrfs_read_fs_root_no_name(fs_info, &key);
			if (IS_ERR(clone_root)) {
				srcu_read_unlock(&fs_info->subvol_srcu, index);
				ret = PTR_ERR(clone_root);
				goto out;
			}
			spin_lock(&clone_root->root_item_lock);
			if (!btrfs_root_readonly(clone_root) ||
			    btrfs_root_dead(clone_root)) {
				spin_unlock(&clone_root->root_item_lock);
				srcu_read_unlock(&fs_info->subvol_srcu, index);
				ret = -EPERM;
				goto out;
			}
			clone_root->send_in_progress++;
			spin_unlock(&clone_root->root_item_lock);
			srcu_read_unlock(&fs_info->subvol_srcu, index);

			sctx->clone_roots[i].root = clone_root;
			clone_sources_to_rollback = i + 1;
		}
		kvfree(clone_sources_tmp);
		clone_sources_tmp = NULL;
	}

	if (arg->parent_root) {
		key.objectid = arg->parent_root;
		key.type = BTRFS_ROOT_ITEM_KEY;
		key.offset = (u64)-1;

		index = srcu_read_lock(&fs_info->subvol_srcu);

		sctx->parent_root = btrfs_read_fs_root_no_name(fs_info, &key);
		if (IS_ERR(sctx->parent_root)) {
			srcu_read_unlock(&fs_info->subvol_srcu, index);
			ret = PTR_ERR(sctx->parent_root);
			goto out;
		}

		spin_lock(&sctx->parent_root->root_item_lock);
		sctx->parent_root->send_in_progress++;
		if (!btrfs_root_readonly(sctx->parent_root) ||
				btrfs_root_dead(sctx->parent_root)) {
			spin_unlock(&sctx->parent_root->root_item_lock);
			srcu_read_unlock(&fs_info->subvol_srcu, index);
			ret = -EPERM;
			goto out;
		}
		spin_unlock(&sctx->parent_root->root_item_lock);

		srcu_read_unlock(&fs_info->subvol_srcu, index);
	}

	/*
	 * Clones from send_root are allowed, but only if the clone source
	 * is behind the current send position. This is checked while searching
	 * for possible clone sources.
	 */
	sctx->clone_roots[sctx->clone_roots_cnt++].root = sctx->send_root;

	/* We do a bsearch later */
	sort(sctx->clone_roots, sctx->clone_roots_cnt,
			sizeof(*sctx->clone_roots), __clone_root_cmp_sort,
			NULL);
	sort_clone_roots = 1;

	ret = ensure_commit_roots_uptodate(sctx);
	if (ret)
		goto out;

	current->journal_info = BTRFS_SEND_TRANS_STUB;
	ret = send_subvol(sctx);
	current->journal_info = NULL;
	if (ret < 0)
		goto out;

	if (!(sctx->flags & BTRFS_SEND_FLAG_OMIT_END_CMD)) {
		ret = begin_cmd(sctx, BTRFS_SEND_C_END);
		if (ret < 0)
			goto out;
		ret = send_cmd(sctx);
		if (ret < 0)
			goto out;
	}

out:
	WARN_ON(sctx && !ret && !RB_EMPTY_ROOT(&sctx->pending_dir_moves));
	while (sctx && !RB_EMPTY_ROOT(&sctx->pending_dir_moves)) {
		struct rb_node *n;
		struct pending_dir_move *pm;

		n = rb_first(&sctx->pending_dir_moves);
		pm = rb_entry(n, struct pending_dir_move, node);
		while (!list_empty(&pm->list)) {
			struct pending_dir_move *pm2;

			pm2 = list_first_entry(&pm->list,
					       struct pending_dir_move, list);
			free_pending_move(sctx, pm2);
		}
		free_pending_move(sctx, pm);
	}

	WARN_ON(sctx && !ret && !RB_EMPTY_ROOT(&sctx->waiting_dir_moves));
	while (sctx && !RB_EMPTY_ROOT(&sctx->waiting_dir_moves)) {
		struct rb_node *n;
		struct waiting_dir_move *dm;

		n = rb_first(&sctx->waiting_dir_moves);
		dm = rb_entry(n, struct waiting_dir_move, node);
		rb_erase(&dm->node, &sctx->waiting_dir_moves);
		kfree(dm);
	}

	WARN_ON(sctx && !ret && !RB_EMPTY_ROOT(&sctx->orphan_dirs));
	while (sctx && !RB_EMPTY_ROOT(&sctx->orphan_dirs)) {
		struct rb_node *n;
		struct orphan_dir_info *odi;

		n = rb_first(&sctx->orphan_dirs);
		odi = rb_entry(n, struct orphan_dir_info, node);
		free_orphan_dir_info(sctx, odi);
	}

	if (sort_clone_roots) {
		for (i = 0; i < sctx->clone_roots_cnt; i++)
			btrfs_root_dec_send_in_progress(
					sctx->clone_roots[i].root);
	} else {
		for (i = 0; sctx && i < clone_sources_to_rollback; i++)
			btrfs_root_dec_send_in_progress(
					sctx->clone_roots[i].root);

		btrfs_root_dec_send_in_progress(send_root);
	}
	if (sctx && !IS_ERR_OR_NULL(sctx->parent_root))
		btrfs_root_dec_send_in_progress(sctx->parent_root);

	kfree(arg);
	kvfree(clone_sources_tmp);

	if (sctx) {
		if (sctx->send_filp)
			fput(sctx->send_filp);

		kvfree(sctx->clone_roots);
		kvfree(sctx->send_buf);
		kvfree(sctx->read_buf);

		name_cache_free(sctx);

		kfree(sctx);
	}

	return ret;
}
