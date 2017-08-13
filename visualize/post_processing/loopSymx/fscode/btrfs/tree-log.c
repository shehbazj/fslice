				      struct extent_buffer *eb, int slot,
				      struct btrfs_key *key)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int found_type;
	u64 extent_end;
	u64 start = key->offset;
	u64 nbytes = 0;
	struct btrfs_file_extent_item *item;
	struct inode *inode = NULL;
	unsigned long size;
	int ret = 0;

	item = btrfs_item_ptr(eb, slot, struct btrfs_file_extent_item);
	found_type = btrfs_file_extent_type(eb, item);

	if (found_type == BTRFS_FILE_EXTENT_REG ||
	    found_type == BTRFS_FILE_EXTENT_PREALLOC) {
		nbytes = btrfs_file_extent_num_bytes(eb, item);
		extent_end = start + nbytes;

		/*
		 * We don't add to the inodes nbytes if we are prealloc or a
		 * hole.
		 */
		if (btrfs_file_extent_disk_bytenr(eb, item) == 0)
			nbytes = 0;
	} else if (found_type == BTRFS_FILE_EXTENT_INLINE) {
		size = btrfs_file_extent_inline_len(eb, slot, item);
		nbytes = btrfs_file_extent_ram_bytes(eb, item);
		extent_end = ALIGN(start + size,
				   fs_info->sectorsize);
	} else {
		ret = 0;
		goto out;
	}

	inode = read_one_inode(root, key->objectid);
	if (!inode) {
		ret = -EIO;
		goto out;
	}

	/*
	 * first check to see if we already have this extent in the
	 * file.  This must be done before the btrfs_drop_extents run
	 * so we don't try to drop this extent.
	 */
	ret = btrfs_lookup_file_extent(trans, root, path,
			btrfs_ino(BTRFS_I(inode)), start, 0);

	if (ret == 0 &&
	    (found_type == BTRFS_FILE_EXTENT_REG ||
	     found_type == BTRFS_FILE_EXTENT_PREALLOC)) {
		struct btrfs_file_extent_item cmp1;
		struct btrfs_file_extent_item cmp2;
		struct btrfs_file_extent_item *existing;
		struct extent_buffer *leaf;

		leaf = path->nodes[0];
		existing = btrfs_item_ptr(leaf, path->slots[0],
					  struct btrfs_file_extent_item);

		read_extent_buffer(eb, &cmp1, (unsigned long)item,
				   sizeof(cmp1));
		read_extent_buffer(leaf, &cmp2, (unsigned long)existing,
				   sizeof(cmp2));

		/*
		 * we already have a pointer to this exact extent,
		 * we don't have to do anything
		 */
		if (memcmp(&cmp1, &cmp2, sizeof(cmp1)) == 0) {
			btrfs_release_path(path);
			goto out;
		}
	}
	btrfs_release_path(path);

	/* drop any overlapping extents */
	ret = btrfs_drop_extents(trans, root, inode, start, extent_end, 1);
	if (ret)
		goto out;

	if (found_type == BTRFS_FILE_EXTENT_REG ||
	    found_type == BTRFS_FILE_EXTENT_PREALLOC) {
		u64 offset;
		unsigned long dest_offset;
		struct btrfs_key ins;

		if (btrfs_file_extent_disk_bytenr(eb, item) == 0 &&
		    btrfs_fs_incompat(fs_info, NO_HOLES))
			goto update_inode;

		ret = btrfs_insert_empty_item(trans, root, path, key,
					      sizeof(*item));
		if (ret)
			goto out;
		dest_offset = btrfs_item_ptr_offset(path->nodes[0],
						    path->slots[0]);
		copy_extent_buffer(path->nodes[0], eb, dest_offset,
				(unsigned long)item,  sizeof(*item));

		ins.objectid = btrfs_file_extent_disk_bytenr(eb, item);
		ins.offset = btrfs_file_extent_disk_num_bytes(eb, item);
		ins.type = BTRFS_EXTENT_ITEM_KEY;
		offset = key->offset - btrfs_file_extent_offset(eb, item);

		/*
		 * Manually record dirty extent, as here we did a shallow
		 * file extent item copy and skip normal backref update,
		 * but modifying extent tree all by ourselves.
		 * So need to manually record dirty extent for qgroup,
		 * as the owner of the file extent changed from log tree
		 * (doesn't affect qgroup) to fs/file tree(affects qgroup)
		 */
		ret = btrfs_qgroup_trace_extent(trans, fs_info,
				btrfs_file_extent_disk_bytenr(eb, item),
				btrfs_file_extent_disk_num_bytes(eb, item),
				GFP_NOFS);
		if (ret < 0)
			goto out;

		if (ins.objectid > 0) {
			u64 csum_start;
			u64 csum_end;
			LIST_HEAD(ordered_sums);
			/*
			 * is this extent already allocated in the extent
			 * allocation tree?  If so, just add a reference
			 */
			ret = btrfs_lookup_data_extent(fs_info, ins.objectid,
						ins.offset);
			if (ret == 0) {
				ret = btrfs_inc_extent_ref(trans, fs_info,
						ins.objectid, ins.offset,
						0, root->root_key.objectid,
						key->objectid, offset);
				if (ret)
					goto out;
			} else {
				/*
				 * insert the extent pointer in the extent
				 * allocation tree
				 */
				ret = btrfs_alloc_logged_file_extent(trans,
						fs_info,
						root->root_key.objectid,
						key->objectid, offset, &ins);
				if (ret)
					goto out;
			}
			btrfs_release_path(path);

			if (btrfs_file_extent_compression(eb, item)) {
				csum_start = ins.objectid;
				csum_end = csum_start + ins.offset;
			} else {
				csum_start = ins.objectid +
					btrfs_file_extent_offset(eb, item);
				csum_end = csum_start +
					btrfs_file_extent_num_bytes(eb, item);
			}

			ret = btrfs_lookup_csums_range(root->log_root,
						csum_start, csum_end - 1,
						&ordered_sums, 0);
			if (ret)
				goto out;
			/*
			 * Now delete all existing cums in the csum root that
			 * cover our range. We do this because we can have an
			 * extent that is completely referenced by one file
			 * extent item and partially referenced by another
			 * file extent item (like after using the clone or
			 * extent_same ioctls). In this case if we end up doing
			 * the replay of the one that partially references the
			 * extent first, and we do not do the csum deletion
			 * below, we can get 2 csum items in the csum tree that
			 * overlap each other. For example, imagine our log has
			 * the two following file extent items:
			 *
			 * key (257 EXTENT_DATA 409600)
			 *     extent data disk byte 12845056 nr 102400
			 *     extent data offset 20480 nr 20480 ram 102400
			 *
			 * key (257 EXTENT_DATA 819200)
			 *     extent data disk byte 12845056 nr 102400
			 *     extent data offset 0 nr 102400 ram 102400
			 *
			 * Where the second one fully references the 100K extent
			 * that starts at disk byte 12845056, and the log tree
			 * has a single csum item that covers the entire range
			 * of the extent:
			 *
			 * key (EXTENT_CSUM EXTENT_CSUM 12845056) itemsize 100
			 *
			 * After the first file extent item is replayed, the
			 * csum tree gets the following csum item:
			 *
			 * key (EXTENT_CSUM EXTENT_CSUM 12865536) itemsize 20
			 *
			 * Which covers the 20K sub-range starting at offset 20K
			 * of our extent. Now when we replay the second file
			 * extent item, if we do not delete existing csum items
			 * that cover any of its blocks, we end up getting two
			 * csum items in our csum tree that overlap each other:
			 *
			 * key (EXTENT_CSUM EXTENT_CSUM 12845056) itemsize 100
			 * key (EXTENT_CSUM EXTENT_CSUM 12865536) itemsize 20
			 *
			 * Which is a problem, because after this anyone trying
			 * to lookup up for the checksum of any block of our
			 * extent starting at an offset of 40K or higher, will
			 * end up looking at the second csum item only, which
			 * does not contain the checksum for any block starting
			 * at offset 40K or higher of our extent.
			 */
			while (!list_empty(&ordered_sums)) {
				struct btrfs_ordered_sum *sums;
				sums = list_entry(ordered_sums.next,
						struct btrfs_ordered_sum,
						list);
				if (!ret)
					ret = btrfs_del_csums(trans, fs_info,
							      sums->bytenr,
							      sums->len);
				if (!ret)
					ret = btrfs_csum_file_blocks(trans,
						fs_info->csum_root, sums);
				list_del(&sums->list);
				kfree(sums);
			}
			if (ret)
				goto out;
		} else {
			btrfs_release_path(path);
		}
	} else if (found_type == BTRFS_FILE_EXTENT_INLINE) {
		/* inline extents are easy, we just overwrite them */
		ret = overwrite_item(trans, root, path, eb, slot, key);
		if (ret)
			goto out;
	}

	inode_add_bytes(inode, nbytes);
update_inode:
	ret = btrfs_update_inode(trans, root, inode);
out:
	if (inode)
		iput(inode);
	return ret;
}
				   u64 ref_objectid,
				   const char *name, int namelen)
{
	struct btrfs_path *path;
	struct btrfs_inode_ref *ref;
	unsigned long ptr;
	unsigned long ptr_end;
	unsigned long name_ptr;
	int found_name_len;
	int item_size;
	int ret;
	int match = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	ret = btrfs_search_slot(NULL, log, key, path, 0, 0);
	if (ret != 0)
		goto out;

	ptr = btrfs_item_ptr_offset(path->nodes[0], path->slots[0]);

	if (key->type == BTRFS_INODE_EXTREF_KEY) {
		if (btrfs_find_name_in_ext_backref(path, ref_objectid,
						   name, namelen, NULL))
			match = 1;

		goto out;
	}

	item_size = btrfs_item_size_nr(path->nodes[0], path->slots[0]);
	ptr_end = ptr + item_size;
	while (ptr < ptr_end) {
		ref = (struct btrfs_inode_ref *)ptr;
		found_name_len = btrfs_inode_ref_name_len(path->nodes[0], ref);
		if (found_name_len == namelen) {
			name_ptr = (unsigned long)(ref + 1);
			ret = memcmp_extent_buffer(path->nodes[0], name,
						   name_ptr, namelen);
			if (ret == 0) {
				match = 1;
				goto out;
			}
		}
		ptr = (unsigned long)(ref + 1) + found_name_len;
	}
out:
	btrfs_free_path(path);
	return match;
}
				  u64 ref_index, char *name, int namelen,
				  int *search_done)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret;
	char *victim_name;
	int victim_name_len;
	struct extent_buffer *leaf;
	struct btrfs_dir_item *di;
	struct btrfs_key search_key;
	struct btrfs_inode_extref *extref;

again:
	/* Search old style refs */
	search_key.objectid = inode_objectid;
	search_key.type = BTRFS_INODE_REF_KEY;
	search_key.offset = parent_objectid;
	ret = btrfs_search_slot(NULL, root, &search_key, path, 0, 0);
	if (ret == 0) {
		struct btrfs_inode_ref *victim_ref;
		unsigned long ptr;
		unsigned long ptr_end;

		leaf = path->nodes[0];

		/* are we trying to overwrite a back ref for the root directory
		 * if so, just jump out, we're done
		 */
		if (search_key.objectid == search_key.offset)
			return 1;

		/* check all the names in this back reference to see
		 * if they are in the log.  if so, we allow them to stay
		 * otherwise they must be unlinked as a conflict
		 */
		ptr = btrfs_item_ptr_offset(leaf, path->slots[0]);
		ptr_end = ptr + btrfs_item_size_nr(leaf, path->slots[0]);
		while (ptr < ptr_end) {
			victim_ref = (struct btrfs_inode_ref *)ptr;
			victim_name_len = btrfs_inode_ref_name_len(leaf,
								   victim_ref);
			victim_name = kmalloc(victim_name_len, GFP_NOFS);
			if (!victim_name)
				return -ENOMEM;

			read_extent_buffer(leaf, victim_name,
					   (unsigned long)(victim_ref + 1),
					   victim_name_len);

			if (!backref_in_log(log_root, &search_key,
					    parent_objectid,
					    victim_name,
					    victim_name_len)) {
				inc_nlink(&inode->vfs_inode);
				btrfs_release_path(path);

				ret = btrfs_unlink_inode(trans, root, dir, inode,
						victim_name, victim_name_len);
				kfree(victim_name);
				if (ret)
					return ret;
				ret = btrfs_run_delayed_items(trans, fs_info);
				if (ret)
					return ret;
				*search_done = 1;
				goto again;
			}
			kfree(victim_name);

			ptr = (unsigned long)(victim_ref + 1) + victim_name_len;
		}

		/*
		 * NOTE: we have searched root tree and checked the
		 * corresponding ref, it does not need to check again.
		 */
		*search_done = 1;
	}
	btrfs_release_path(path);

	/* Same search but for extended refs */
	extref = btrfs_lookup_inode_extref(NULL, root, path, name, namelen,
					   inode_objectid, parent_objectid, 0,
					   0);
	if (!IS_ERR_OR_NULL(extref)) {
		u32 item_size;
		u32 cur_offset = 0;
		unsigned long base;
		struct inode *victim_parent;

		leaf = path->nodes[0];

		item_size = btrfs_item_size_nr(leaf, path->slots[0]);
		base = btrfs_item_ptr_offset(leaf, path->slots[0]);

		while (cur_offset < item_size) {
			extref = (struct btrfs_inode_extref *)(base + cur_offset);

			victim_name_len = btrfs_inode_extref_name_len(leaf, extref);

			if (btrfs_inode_extref_parent(leaf, extref) != parent_objectid)
				goto next;

			victim_name = kmalloc(victim_name_len, GFP_NOFS);
			if (!victim_name)
				return -ENOMEM;
			read_extent_buffer(leaf, victim_name, (unsigned long)&extref->name,
					   victim_name_len);

			search_key.objectid = inode_objectid;
			search_key.type = BTRFS_INODE_EXTREF_KEY;
			search_key.offset = btrfs_extref_hash(parent_objectid,
							      victim_name,
							      victim_name_len);
			ret = 0;
			if (!backref_in_log(log_root, &search_key,
					    parent_objectid, victim_name,
					    victim_name_len)) {
				ret = -ENOENT;
				victim_parent = read_one_inode(root,
						parent_objectid);
				if (victim_parent) {
					inc_nlink(&inode->vfs_inode);
					btrfs_release_path(path);

					ret = btrfs_unlink_inode(trans, root,
							BTRFS_I(victim_parent),
							inode,
							victim_name,
							victim_name_len);
					if (!ret)
						ret = btrfs_run_delayed_items(
								  trans,
								  fs_info);
				}
				iput(victim_parent);
				kfree(victim_name);
				if (ret)
					return ret;
				*search_done = 1;
				goto again;
			}
			kfree(victim_name);
			if (ret)
				return ret;
next:
			cur_offset += victim_name_len + sizeof(*extref);
		}
		*search_done = 1;
	}
	btrfs_release_path(path);

	/* look for a conflicting sequence number */
	di = btrfs_lookup_dir_index_item(trans, root, path, btrfs_ino(dir),
					 ref_index, name, namelen, 0);
	if (di && !IS_ERR(di)) {
		ret = drop_one_dir_item(trans, root, path, dir, di);
		if (ret)
			return ret;
	}
	btrfs_release_path(path);

	/* look for a conflicing name */
	di = btrfs_lookup_dir_item(trans, root, path, btrfs_ino(dir),
				   name, namelen, 0);
	if (di && !IS_ERR(di)) {
		ret = drop_one_dir_item(trans, root, path, dir, di);
		if (ret)
			return ret;
	}
	btrfs_release_path(path);

	return 0;
}
				  struct extent_buffer *eb, int slot,
				  struct btrfs_key *key)
{
	struct inode *dir = NULL;
	struct inode *inode = NULL;
	unsigned long ref_ptr;
	unsigned long ref_end;
	char *name = NULL;
	int namelen;
	int ret;
	int search_done = 0;
	int log_ref_ver = 0;
	u64 parent_objectid;
	u64 inode_objectid;
	u64 ref_index = 0;
	int ref_struct_size;

	ref_ptr = btrfs_item_ptr_offset(eb, slot);
	ref_end = ref_ptr + btrfs_item_size_nr(eb, slot);

	if (key->type == BTRFS_INODE_EXTREF_KEY) {
		struct btrfs_inode_extref *r;

		ref_struct_size = sizeof(struct btrfs_inode_extref);
		log_ref_ver = 1;
		r = (struct btrfs_inode_extref *)ref_ptr;
		parent_objectid = btrfs_inode_extref_parent(eb, r);
	} else {
		ref_struct_size = sizeof(struct btrfs_inode_ref);
		parent_objectid = key->offset;
	}
	inode_objectid = key->objectid;

	/*
	 * it is possible that we didn't log all the parent directories
	 * for a given inode.  If we don't find the dir, just don't
	 * copy the back ref in.  The link count fixup code will take
	 * care of the rest
	 */
	dir = read_one_inode(root, parent_objectid);
	if (!dir) {
		ret = -ENOENT;
		goto out;
	}

	inode = read_one_inode(root, inode_objectid);
	if (!inode) {
		ret = -EIO;
		goto out;
	}

	while (ref_ptr < ref_end) {
		if (log_ref_ver) {
			ret = extref_get_fields(eb, ref_ptr, &namelen, &name,
						&ref_index, &parent_objectid);
			/*
			 * parent object can change from one array
			 * item to another.
			 */
			if (!dir)
				dir = read_one_inode(root, parent_objectid);
			if (!dir) {
				ret = -ENOENT;
				goto out;
			}
		} else {
			ret = ref_get_fields(eb, ref_ptr, &namelen, &name,
					     &ref_index);
		}
		if (ret)
			goto out;

		/* if we already have a perfect match, we're done */
		if (!inode_in_dir(root, path, btrfs_ino(BTRFS_I(dir)),
					btrfs_ino(BTRFS_I(inode)), ref_index,
					name, namelen)) {
			/*
			 * look for a conflicting back reference in the
			 * metadata. if we find one we have to unlink that name
			 * of the file before we add our new link.  Later on, we
			 * overwrite any existing back reference, and we don't
			 * want to create dangling pointers in the directory.
			 */

			if (!search_done) {
				ret = __add_inode_ref(trans, root, path, log,
						      BTRFS_I(dir),
						      BTRFS_I(inode),
						      inode_objectid,
						      parent_objectid,
						      ref_index, name, namelen,
						      &search_done);
				if (ret) {
					if (ret == 1)
						ret = 0;
					goto out;
				}
			}

			/* insert our name */
			ret = btrfs_add_link(trans, BTRFS_I(dir),
					BTRFS_I(inode),
					name, namelen, 0, ref_index);
			if (ret)
				goto out;

			btrfs_update_inode(trans, root, inode);
		}

		ref_ptr = (unsigned long)(ref_ptr + ref_struct_size) + namelen;
		kfree(name);
		name = NULL;
		if (log_ref_ver) {
			iput(dir);
			dir = NULL;
		}
	}

	/* finally write the back reference in the inode */
	ret = overwrite_item(trans, root, path, eb, slot, key);
out:
	btrfs_release_path(path);
	kfree(name);
	iput(dir);
	iput(inode);
	return ret;
}
static int count_inode_extrefs(struct btrfs_root *root,
		struct btrfs_inode *inode, struct btrfs_path *path)
{
	int ret = 0;
	int name_len;
	unsigned int nlink = 0;
	u32 item_size;
	u32 cur_offset = 0;
	u64 inode_objectid = btrfs_ino(inode);
	u64 offset = 0;
	unsigned long ptr;
	struct btrfs_inode_extref *extref;
	struct extent_buffer *leaf;

	while (1) {
		ret = btrfs_find_one_extref(root, inode_objectid, offset, path,
					    &extref, &offset);
		if (ret)
			break;

		leaf = path->nodes[0];
		item_size = btrfs_item_size_nr(leaf, path->slots[0]);
		ptr = btrfs_item_ptr_offset(leaf, path->slots[0]);
		cur_offset = 0;

		while (cur_offset < item_size) {
			extref = (struct btrfs_inode_extref *) (ptr + cur_offset);
			name_len = btrfs_inode_extref_name_len(leaf, extref);

			nlink++;

			cur_offset += name_len + sizeof(*extref);
		}

		offset++;
		btrfs_release_path(path);
	}
	btrfs_release_path(path);

	if (ret < 0 && ret != -ENOENT)
		return ret;
	return nlink;
}
static int count_inode_refs(struct btrfs_root *root,
			struct btrfs_inode *inode, struct btrfs_path *path)
{
	int ret;
	struct btrfs_key key;
	unsigned int nlink = 0;
	unsigned long ptr;
	unsigned long ptr_end;
	int name_len;
	u64 ino = btrfs_ino(inode);

	key.objectid = ino;
	key.type = BTRFS_INODE_REF_KEY;
	key.offset = (u64)-1;

	while (1) {
		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0)
			break;
		if (ret > 0) {
			if (path->slots[0] == 0)
				break;
			path->slots[0]--;
		}
process_slot:
		btrfs_item_key_to_cpu(path->nodes[0], &key,
				      path->slots[0]);
		if (key.objectid != ino ||
		    key.type != BTRFS_INODE_REF_KEY)
			break;
		ptr = btrfs_item_ptr_offset(path->nodes[0], path->slots[0]);
		ptr_end = ptr + btrfs_item_size_nr(path->nodes[0],
						   path->slots[0]);
		while (ptr < ptr_end) {
			struct btrfs_inode_ref *ref;

			ref = (struct btrfs_inode_ref *)ptr;
			name_len = btrfs_inode_ref_name_len(path->nodes[0],
							    ref);
			ptr = (unsigned long)(ref + 1) + name_len;
			nlink++;
		}

		if (key.offset == 0)
			break;
		if (path->slots[0] > 0) {
			path->slots[0]--;
			goto process_slot;
		}
		key.offset--;
		btrfs_release_path(path);
	}
	btrfs_release_path(path);

	return nlink;
}
					    struct btrfs_root *root,
					    struct btrfs_path *path)
{
	int ret;
	struct btrfs_key key;
	struct inode *inode;

	key.objectid = BTRFS_TREE_LOG_FIXUP_OBJECTID;
	key.type = BTRFS_ORPHAN_ITEM_KEY;
	key.offset = (u64)-1;
	while (1) {
		ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
		if (ret < 0)
			break;

		if (ret == 1) {
			if (path->slots[0] == 0)
				break;
			path->slots[0]--;
		}

		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);
		if (key.objectid != BTRFS_TREE_LOG_FIXUP_OBJECTID ||
		    key.type != BTRFS_ORPHAN_ITEM_KEY)
			break;

		ret = btrfs_del_item(trans, root, path);
		if (ret)
			goto out;

		btrfs_release_path(path);
		inode = read_one_inode(root, key.offset);
		if (!inode)
			return -EIO;

		ret = fixup_inode_link_count(trans, root, inode);
		iput(inode);
		if (ret)
			goto out;

		/*
		 * fixup on a directory may create new entries,
		 * make sure we always look for the highset possible
		 * offset
		 */
		key.offset = (u64)-1;
	}
	ret = 0;
out:
	btrfs_release_path(path);
	return ret;
}
					struct extent_buffer *eb, int slot,
					struct btrfs_key *key)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret = 0;
	u32 item_size = btrfs_item_size_nr(eb, slot);
	struct btrfs_dir_item *di;
	int name_len;
	unsigned long ptr;
	unsigned long ptr_end;
	struct btrfs_path *fixup_path = NULL;

	ptr = btrfs_item_ptr_offset(eb, slot);
	ptr_end = ptr + item_size;
	while (ptr < ptr_end) {
		di = (struct btrfs_dir_item *)ptr;
		if (verify_dir_item(fs_info, eb, di))
			return -EIO;
		name_len = btrfs_dir_name_len(eb, di);
		ret = replay_one_name(trans, root, path, eb, di, key);
		if (ret < 0)
			break;
		ptr = (unsigned long)(di + 1);
		ptr += name_len;

		/*
		 * If this entry refers to a non-directory (directories can not
		 * have a link count > 1) and it was added in the transaction
		 * that was not committed, make sure we fixup the link count of
		 * the inode it the entry points to. Otherwise something like
		 * the following would result in a directory pointing to an
		 * inode with a wrong link that does not account for this dir
		 * entry:
		 *
		 * mkdir testdir
		 * touch testdir/foo
		 * touch testdir/bar
		 * sync
		 *
		 * ln testdir/bar testdir/bar_link
		 * ln testdir/foo testdir/foo_link
		 * xfs_io -c "fsync" testdir/bar
		 *
		 * <power failure>
		 *
		 * mount fs, log replay happens
		 *
		 * File foo would remain with a link count of 1 when it has two
		 * entries pointing to it in the directory testdir. This would
		 * make it impossible to ever delete the parent directory has
		 * it would result in stale dentries that can never be deleted.
		 */
		if (ret == 1 && btrfs_dir_type(eb, di) != BTRFS_FT_DIR) {
			struct btrfs_key di_key;

			if (!fixup_path) {
				fixup_path = btrfs_alloc_path();
				if (!fixup_path) {
					ret = -ENOMEM;
					break;
				}
			}

			btrfs_dir_item_key_to_cpu(eb, di, &di_key);
			ret = link_to_fixup_dir(trans, root, fixup_path,
						di_key.objectid);
			if (ret)
				break;
		}
		ret = 0;
	}
	btrfs_free_path(fixup_path);
	return ret;
}
				      struct inode *dir,
				      struct btrfs_key *dir_key)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret;
	struct extent_buffer *eb;
	int slot;
	u32 item_size;
	struct btrfs_dir_item *di;
	struct btrfs_dir_item *log_di;
	int name_len;
	unsigned long ptr;
	unsigned long ptr_end;
	char *name;
	struct inode *inode;
	struct btrfs_key location;

again:
	eb = path->nodes[0];
	slot = path->slots[0];
	item_size = btrfs_item_size_nr(eb, slot);
	ptr = btrfs_item_ptr_offset(eb, slot);
	ptr_end = ptr + item_size;
	while (ptr < ptr_end) {
		di = (struct btrfs_dir_item *)ptr;
		if (verify_dir_item(fs_info, eb, di)) {
			ret = -EIO;
			goto out;
		}

		name_len = btrfs_dir_name_len(eb, di);
		name = kmalloc(name_len, GFP_NOFS);
		if (!name) {
			ret = -ENOMEM;
			goto out;
		}
		read_extent_buffer(eb, name, (unsigned long)(di + 1),
				  name_len);
		log_di = NULL;
		if (log && dir_key->type == BTRFS_DIR_ITEM_KEY) {
			log_di = btrfs_lookup_dir_item(trans, log, log_path,
						       dir_key->objectid,
						       name, name_len, 0);
		} else if (log && dir_key->type == BTRFS_DIR_INDEX_KEY) {
			log_di = btrfs_lookup_dir_index_item(trans, log,
						     log_path,
						     dir_key->objectid,
						     dir_key->offset,
						     name, name_len, 0);
		}
		if (!log_di || (IS_ERR(log_di) && PTR_ERR(log_di) == -ENOENT)) {
			btrfs_dir_item_key_to_cpu(eb, di, &location);
			btrfs_release_path(path);
			btrfs_release_path(log_path);
			inode = read_one_inode(root, location.objectid);
			if (!inode) {
				kfree(name);
				return -EIO;
			}

			ret = link_to_fixup_dir(trans, root,
						path, location.objectid);
			if (ret) {
				kfree(name);
				iput(inode);
				goto out;
			}

			inc_nlink(inode);
			ret = btrfs_unlink_inode(trans, root, BTRFS_I(dir),
					BTRFS_I(inode), name, name_len);
			if (!ret)
				ret = btrfs_run_delayed_items(trans, fs_info);
			kfree(name);
			iput(inode);
			if (ret)
				goto out;

			/* there might still be more names under this key
			 * check and repeat if required
			 */
			ret = btrfs_search_slot(NULL, root, dir_key, path,
						0, 0);
			if (ret == 0)
				goto again;
			ret = 0;
			goto out;
		} else if (IS_ERR(log_di)) {
			kfree(name);
			return PTR_ERR(log_di);
		}
		btrfs_release_path(log_path);
		kfree(name);

		ptr = (unsigned long)(di + 1);
		ptr += name_len;
	}
	ret = 0;
out:
	btrfs_release_path(path);
	btrfs_release_path(log_path);
	return ret;
}
			      struct btrfs_path *path,
			      const u64 ino)
{
	struct btrfs_key search_key;
	struct btrfs_path *log_path;
	int i;
	int nritems;
	int ret;

	log_path = btrfs_alloc_path();
	if (!log_path)
		return -ENOMEM;

	search_key.objectid = ino;
	search_key.type = BTRFS_XATTR_ITEM_KEY;
	search_key.offset = 0;
again:
	ret = btrfs_search_slot(NULL, root, &search_key, path, 0, 0);
	if (ret < 0)
		goto out;
process_leaf:
	nritems = btrfs_header_nritems(path->nodes[0]);
	for (i = path->slots[0]; i < nritems; i++) {
		struct btrfs_key key;
		struct btrfs_dir_item *di;
		struct btrfs_dir_item *log_di;
		u32 total_size;
		u32 cur;

		btrfs_item_key_to_cpu(path->nodes[0], &key, i);
		if (key.objectid != ino || key.type != BTRFS_XATTR_ITEM_KEY) {
			ret = 0;
			goto out;
		}

		di = btrfs_item_ptr(path->nodes[0], i, struct btrfs_dir_item);
		total_size = btrfs_item_size_nr(path->nodes[0], i);
		cur = 0;
		while (cur < total_size) {
			u16 name_len = btrfs_dir_name_len(path->nodes[0], di);
			u16 data_len = btrfs_dir_data_len(path->nodes[0], di);
			u32 this_len = sizeof(*di) + name_len + data_len;
			char *name;

			name = kmalloc(name_len, GFP_NOFS);
			if (!name) {
				ret = -ENOMEM;
				goto out;
			}
			read_extent_buffer(path->nodes[0], name,
					   (unsigned long)(di + 1), name_len);

			log_di = btrfs_lookup_xattr(NULL, log, log_path, ino,
						    name, name_len, 0);
			btrfs_release_path(log_path);
			if (!log_di) {
				/* Doesn't exist in log tree, so delete it. */
				btrfs_release_path(path);
				di = btrfs_lookup_xattr(trans, root, path, ino,
							name, name_len, -1);
				kfree(name);
				if (IS_ERR(di)) {
					ret = PTR_ERR(di);
					goto out;
				}
				ASSERT(di);
				ret = btrfs_delete_one_dir_name(trans, root,
								path, di);
				if (ret)
					goto out;
				btrfs_release_path(path);
				search_key = key;
				goto again;
			}
			kfree(name);
			if (IS_ERR(log_di)) {
				ret = PTR_ERR(log_di);
				goto out;
			}
			cur += this_len;
			di = (struct btrfs_dir_item *)((char *)di + this_len);
		}
	}
	ret = btrfs_next_leaf(root, path);
	if (ret > 0)
		ret = 0;
	else if (ret == 0)
		goto process_leaf;
out:
	btrfs_free_path(log_path);
	btrfs_release_path(path);
	return ret;
}
				       struct btrfs_path *path,
				       u64 dirid, int del_all)
{
	u64 range_start;
	u64 range_end;
	int key_type = BTRFS_DIR_LOG_ITEM_KEY;
	int ret = 0;
	struct btrfs_key dir_key;
	struct btrfs_key found_key;
	struct btrfs_path *log_path;
	struct inode *dir;

	dir_key.objectid = dirid;
	dir_key.type = BTRFS_DIR_ITEM_KEY;
	log_path = btrfs_alloc_path();
	if (!log_path)
		return -ENOMEM;

	dir = read_one_inode(root, dirid);
	/* it isn't an error if the inode isn't there, that can happen
	 * because we replay the deletes before we copy in the inode item
	 * from the log
	 */
	if (!dir) {
		btrfs_free_path(log_path);
		return 0;
	}
again:
	range_start = 0;
	range_end = 0;
	while (1) {
		if (del_all)
			range_end = (u64)-1;
		else {
			ret = find_dir_range(log, path, dirid, key_type,
					     &range_start, &range_end);
			if (ret != 0)
				break;
		}

		dir_key.offset = range_start;
		while (1) {
			int nritems;
			ret = btrfs_search_slot(NULL, root, &dir_key, path,
						0, 0);
			if (ret < 0)
				goto out;

			nritems = btrfs_header_nritems(path->nodes[0]);
			if (path->slots[0] >= nritems) {
				ret = btrfs_next_leaf(root, path);
				if (ret)
					break;
			}
			btrfs_item_key_to_cpu(path->nodes[0], &found_key,
					      path->slots[0]);
			if (found_key.objectid != dirid ||
			    found_key.type != dir_key.type)
				goto next_type;

			if (found_key.offset > range_end)
				break;

			ret = check_item_in_log(trans, root, log, path,
						log_path, dir,
						&found_key);
			if (ret)
				goto out;
			if (found_key.offset == (u64)-1)
				break;
			dir_key.offset = found_key.offset + 1;
		}
		btrfs_release_path(path);
		if (range_end == (u64)-1)
			break;
		range_start = range_end + 1;
	}

next_type:
	ret = 0;
	if (key_type == BTRFS_DIR_LOG_ITEM_KEY) {
		key_type = BTRFS_DIR_LOG_INDEX_KEY;
		dir_key.type = BTRFS_DIR_INDEX_KEY;
		btrfs_release_path(path);
		goto again;
	}
out:
	btrfs_release_path(path);
	btrfs_free_path(log_path);
	iput(dir);
	return ret;
}
static int replay_one_buffer(struct btrfs_root *log, struct extent_buffer *eb,
			     struct walk_control *wc, u64 gen)
{
	int nritems;
	struct btrfs_path *path;
	struct btrfs_root *root = wc->replay_dest;
	struct btrfs_key key;
	int level;
	int i;
	int ret;

	ret = btrfs_read_buffer(eb, gen);
	if (ret)
		return ret;

	level = btrfs_header_level(eb);

	if (level != 0)
		return 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	nritems = btrfs_header_nritems(eb);
	for (i = 0; i < nritems; i++) {
		btrfs_item_key_to_cpu(eb, &key, i);

		/* inode keys are done during the first stage */
		if (key.type == BTRFS_INODE_ITEM_KEY &&
		    wc->stage == LOG_WALK_REPLAY_INODES) {
			struct btrfs_inode_item *inode_item;
			u32 mode;

			inode_item = btrfs_item_ptr(eb, i,
					    struct btrfs_inode_item);
			ret = replay_xattr_deletes(wc->trans, root, log,
						   path, key.objectid);
			if (ret)
				break;
			mode = btrfs_inode_mode(eb, inode_item);
			if (S_ISDIR(mode)) {
				ret = replay_dir_deletes(wc->trans,
					 root, log, path, key.objectid, 0);
				if (ret)
					break;
			}
			ret = overwrite_item(wc->trans, root, path,
					     eb, i, &key);
			if (ret)
				break;

			/* for regular files, make sure corresponding
			 * orphan item exist. extents past the new EOF
			 * will be truncated later by orphan cleanup.
			 */
			if (S_ISREG(mode)) {
				ret = insert_orphan_item(wc->trans, root,
							 key.objectid);
				if (ret)
					break;
			}

			ret = link_to_fixup_dir(wc->trans, root,
						path, key.objectid);
			if (ret)
				break;
		}

		if (key.type == BTRFS_DIR_INDEX_KEY &&
		    wc->stage == LOG_WALK_REPLAY_DIR_INDEX) {
			ret = replay_one_dir_item(wc->trans, root, path,
						  eb, i, &key);
			if (ret)
				break;
		}

		if (wc->stage < LOG_WALK_REPLAY_ALL)
			continue;

		/* these keys are simply copied */
		if (key.type == BTRFS_XATTR_ITEM_KEY) {
			ret = overwrite_item(wc->trans, root, path,
					     eb, i, &key);
			if (ret)
				break;
		} else if (key.type == BTRFS_INODE_REF_KEY ||
			   key.type == BTRFS_INODE_EXTREF_KEY) {
			ret = add_inode_ref(wc->trans, root, log, path,
					    eb, i, &key);
			if (ret && ret != -ENOENT)
				break;
			ret = 0;
		} else if (key.type == BTRFS_EXTENT_DATA_KEY) {
			ret = replay_one_extent(wc->trans, root, path,
						eb, i, &key);
			if (ret)
				break;
		} else if (key.type == BTRFS_DIR_ITEM_KEY) {
			ret = replay_one_dir_item(wc->trans, root, path,
						  eb, i, &key);
			if (ret)
				break;
		}
	}
	btrfs_free_path(path);
	return ret;
}
				   struct btrfs_path *path, int *level,
				   struct walk_control *wc)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 root_owner;
	u64 bytenr;
	u64 ptr_gen;
	struct extent_buffer *next;
	struct extent_buffer *cur;
	struct extent_buffer *parent;
	u32 blocksize;
	int ret = 0;

	WARN_ON(*level < 0);
	WARN_ON(*level >= BTRFS_MAX_LEVEL);

	while (*level > 0) {
		WARN_ON(*level < 0);
		WARN_ON(*level >= BTRFS_MAX_LEVEL);
		cur = path->nodes[*level];

		WARN_ON(btrfs_header_level(cur) != *level);

		if (path->slots[*level] >=
		    btrfs_header_nritems(cur))
			break;

		bytenr = btrfs_node_blockptr(cur, path->slots[*level]);
		ptr_gen = btrfs_node_ptr_generation(cur, path->slots[*level]);
		blocksize = fs_info->nodesize;

		parent = path->nodes[*level];
		root_owner = btrfs_header_owner(parent);

		next = btrfs_find_create_tree_block(fs_info, bytenr);
		if (IS_ERR(next))
			return PTR_ERR(next);

		if (*level == 1) {
			ret = wc->process_func(root, next, wc, ptr_gen);
			if (ret) {
				free_extent_buffer(next);
				return ret;
			}

			path->slots[*level]++;
			if (wc->free) {
				ret = btrfs_read_buffer(next, ptr_gen);
				if (ret) {
					free_extent_buffer(next);
					return ret;
				}

				if (trans) {
					btrfs_tree_lock(next);
					btrfs_set_lock_blocking(next);
					clean_tree_block(fs_info, next);
					btrfs_wait_tree_block_writeback(next);
					btrfs_tree_unlock(next);
				}

				WARN_ON(root_owner !=
					BTRFS_TREE_LOG_OBJECTID);
				ret = btrfs_free_and_pin_reserved_extent(
							fs_info, bytenr,
							blocksize);
				if (ret) {
					free_extent_buffer(next);
					return ret;
				}
			}
			free_extent_buffer(next);
			continue;
		}
		ret = btrfs_read_buffer(next, ptr_gen);
		if (ret) {
			free_extent_buffer(next);
			return ret;
		}

		WARN_ON(*level <= 0);
		if (path->nodes[*level-1])
			free_extent_buffer(path->nodes[*level-1]);
		path->nodes[*level-1] = next;
		*level = btrfs_header_level(next);
		path->slots[*level] = 0;
		cond_resched();
	}
	WARN_ON(*level < 0);
	WARN_ON(*level >= BTRFS_MAX_LEVEL);

	path->slots[*level] = btrfs_header_nritems(path->nodes[*level]);

	cond_resched();
	return 0;
}
				 struct btrfs_path *path, int *level,
				 struct walk_control *wc)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 root_owner;
	int i;
	int slot;
	int ret;

	for (i = *level; i < BTRFS_MAX_LEVEL - 1 && path->nodes[i]; i++) {
		slot = path->slots[i];
		if (slot + 1 < btrfs_header_nritems(path->nodes[i])) {
			path->slots[i]++;
			*level = i;
			WARN_ON(*level == 0);
			return 0;
		} else {
			struct extent_buffer *parent;
			if (path->nodes[*level] == root->node)
				parent = path->nodes[*level];
			else
				parent = path->nodes[*level + 1];

			root_owner = btrfs_header_owner(parent);
			ret = wc->process_func(root, path->nodes[*level], wc,
				 btrfs_header_generation(path->nodes[*level]));
			if (ret)
				return ret;

			if (wc->free) {
				struct extent_buffer *next;

				next = path->nodes[*level];

				if (trans) {
					btrfs_tree_lock(next);
					btrfs_set_lock_blocking(next);
					clean_tree_block(fs_info, next);
					btrfs_wait_tree_block_writeback(next);
					btrfs_tree_unlock(next);
				}

				WARN_ON(root_owner != BTRFS_TREE_LOG_OBJECTID);
				ret = btrfs_free_and_pin_reserved_extent(
						fs_info,
						path->nodes[*level]->start,
						path->nodes[*level]->len);
				if (ret)
					return ret;
			}
			free_extent_buffer(path->nodes[*level]);
			path->nodes[*level] = NULL;
			*level = i + 1;
		}
	}
	return 1;
}
static int walk_log_tree(struct btrfs_trans_handle *trans,
			 struct btrfs_root *log, struct walk_control *wc)
{
	struct btrfs_fs_info *fs_info = log->fs_info;
	int ret = 0;
	int wret;
	int level;
	struct btrfs_path *path;
	int orig_level;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	level = btrfs_header_level(log->node);
	orig_level = level;
	path->nodes[level] = log->node;
	extent_buffer_get(log->node);
	path->slots[level] = 0;

	while (1) {
		wret = walk_down_log_tree(trans, log, path, &level, wc);
		if (wret > 0)
			break;
		if (wret < 0) {
			ret = wret;
			goto out;
		}

		wret = walk_up_log_tree(trans, log, path, &level, wc);
		if (wret > 0)
			break;
		if (wret < 0) {
			ret = wret;
			goto out;
		}
	}

	/* was the root node processed? if not, catch it here */
	if (path->nodes[orig_level]) {
		ret = wc->process_func(log, path->nodes[orig_level], wc,
			 btrfs_header_generation(path->nodes[orig_level]));
		if (ret)
			goto out;
		if (wc->free) {
			struct extent_buffer *next;

			next = path->nodes[orig_level];

			if (trans) {
				btrfs_tree_lock(next);
				btrfs_set_lock_blocking(next);
				clean_tree_block(fs_info, next);
				btrfs_wait_tree_block_writeback(next);
				btrfs_tree_unlock(next);
			}

			WARN_ON(log->root_key.objectid !=
				BTRFS_TREE_LOG_OBJECTID);
			ret = btrfs_free_and_pin_reserved_extent(fs_info,
							next->start, next->len);
			if (ret)
				goto out;
		}
	}

out:
	btrfs_free_path(path);
	return ret;
}

static void wait_log_commit(struct btrfs_root *root, int transid)
{
	DEFINE_WAIT(wait);
	int index = transid % 2;

	/*
	 * we only allow two pending log transactions at a time,
	 * so we know that if ours is more than 2 older than the
	 * current transaction, we're done
	 */
	do {
		prepare_to_wait(&root->log_commit_wait[index],
				&wait, TASK_UNINTERRUPTIBLE);
		mutex_unlock(&root->log_mutex);

		if (root->log_transid_committed < transid &&
		    atomic_read(&root->log_commit[index]))
			schedule();

		finish_wait(&root->log_commit_wait[index], &wait);
		mutex_lock(&root->log_mutex);
	} while (root->log_transid_committed < transid &&
		 atomic_read(&root->log_commit[index]));
}

static void wait_for_writer(struct btrfs_root *root)
{
	DEFINE_WAIT(wait);

	while (atomic_read(&root->log_writers)) {
		prepare_to_wait(&root->log_writer_wait,
				&wait, TASK_UNINTERRUPTIBLE);
		mutex_unlock(&root->log_mutex);
		if (atomic_read(&root->log_writers))
			schedule();
		finish_wait(&root->log_writer_wait, &wait);
		mutex_lock(&root->log_mutex);
	}
}
int btrfs_sync_log(struct btrfs_trans_handle *trans,
		   struct btrfs_root *root, struct btrfs_log_ctx *ctx)
{
	int index1;
	int index2;
	int mark;
	int ret;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_root *log = root->log_root;
	struct btrfs_root *log_root_tree = fs_info->log_root_tree;
	int log_transid = 0;
	struct btrfs_log_ctx root_log_ctx;
	struct blk_plug plug;

	mutex_lock(&root->log_mutex);
	log_transid = ctx->log_transid;
	if (root->log_transid_committed >= log_transid) {
		mutex_unlock(&root->log_mutex);
		return ctx->log_ret;
	}

	index1 = log_transid % 2;
	if (atomic_read(&root->log_commit[index1])) {
		wait_log_commit(root, log_transid);
		mutex_unlock(&root->log_mutex);
		return ctx->log_ret;
	}
	ASSERT(log_transid == root->log_transid);
	atomic_set(&root->log_commit[index1], 1);

	/* wait for previous tree log sync to complete */
	if (atomic_read(&root->log_commit[(index1 + 1) % 2]))
		wait_log_commit(root, log_transid - 1);

	while (1) {
		int batch = atomic_read(&root->log_batch);
		/* when we're on an ssd, just kick the log commit out */
		if (!btrfs_test_opt(fs_info, SSD) &&
		    test_bit(BTRFS_ROOT_MULTI_LOG_TASKS, &root->state)) {
			mutex_unlock(&root->log_mutex);
			schedule_timeout_uninterruptible(1);
			mutex_lock(&root->log_mutex);
		}
		wait_for_writer(root);
		if (batch == atomic_read(&root->log_batch))
			break;
	}

	/* bail out if we need to do a full commit */
	if (btrfs_need_log_full_commit(fs_info, trans)) {
		ret = -EAGAIN;
		btrfs_free_logged_extents(log, log_transid);
		mutex_unlock(&root->log_mutex);
		goto out;
	}

	if (log_transid % 2 == 0)
		mark = EXTENT_DIRTY;
	else
		mark = EXTENT_NEW;

	/* we start IO on  all the marked extents here, but we don't actually
	 * wait for them until later.
	 */
	blk_start_plug(&plug);
	ret = btrfs_write_marked_extents(fs_info, &log->dirty_log_pages, mark);
	if (ret) {
		blk_finish_plug(&plug);
		btrfs_abort_transaction(trans, ret);
		btrfs_free_logged_extents(log, log_transid);
		btrfs_set_log_full_commit(fs_info, trans);
		mutex_unlock(&root->log_mutex);
		goto out;
	}

	btrfs_set_root_node(&log->root_item, log->node);

	root->log_transid++;
	log->log_transid = root->log_transid;
	root->log_start_pid = 0;
	/*
	 * IO has been started, blocks of the log tree have WRITTEN flag set
	 * in their headers. new modifications of the log will be written to
	 * new positions. so it's safe to allow log writers to go in.
	 */
	mutex_unlock(&root->log_mutex);

	btrfs_init_log_ctx(&root_log_ctx, NULL);

	mutex_lock(&log_root_tree->log_mutex);
	atomic_inc(&log_root_tree->log_batch);
	atomic_inc(&log_root_tree->log_writers);

	index2 = log_root_tree->log_transid % 2;
	list_add_tail(&root_log_ctx.list, &log_root_tree->log_ctxs[index2]);
	root_log_ctx.log_transid = log_root_tree->log_transid;

	mutex_unlock(&log_root_tree->log_mutex);

	ret = update_log_root(trans, log);

	mutex_lock(&log_root_tree->log_mutex);
	if (atomic_dec_and_test(&log_root_tree->log_writers)) {
		/*
		 * Implicit memory barrier after atomic_dec_and_test
		 */
		if (waitqueue_active(&log_root_tree->log_writer_wait))
			wake_up(&log_root_tree->log_writer_wait);
	}

	if (ret) {
		if (!list_empty(&root_log_ctx.list))
			list_del_init(&root_log_ctx.list);

		blk_finish_plug(&plug);
		btrfs_set_log_full_commit(fs_info, trans);

		if (ret != -ENOSPC) {
			btrfs_abort_transaction(trans, ret);
			mutex_unlock(&log_root_tree->log_mutex);
			goto out;
		}
		btrfs_wait_tree_log_extents(log, mark);
		btrfs_free_logged_extents(log, log_transid);
		mutex_unlock(&log_root_tree->log_mutex);
		ret = -EAGAIN;
		goto out;
	}

	if (log_root_tree->log_transid_committed >= root_log_ctx.log_transid) {
		blk_finish_plug(&plug);
		list_del_init(&root_log_ctx.list);
		mutex_unlock(&log_root_tree->log_mutex);
		ret = root_log_ctx.log_ret;
		goto out;
	}

	index2 = root_log_ctx.log_transid % 2;
	if (atomic_read(&log_root_tree->log_commit[index2])) {
		blk_finish_plug(&plug);
		ret = btrfs_wait_tree_log_extents(log, mark);
		btrfs_wait_logged_extents(trans, log, log_transid);
		wait_log_commit(log_root_tree,
				root_log_ctx.log_transid);
		mutex_unlock(&log_root_tree->log_mutex);
		if (!ret)
			ret = root_log_ctx.log_ret;
		goto out;
	}
	ASSERT(root_log_ctx.log_transid == log_root_tree->log_transid);
	atomic_set(&log_root_tree->log_commit[index2], 1);

	if (atomic_read(&log_root_tree->log_commit[(index2 + 1) % 2])) {
		wait_log_commit(log_root_tree,
				root_log_ctx.log_transid - 1);
	}

	wait_for_writer(log_root_tree);

	/*
	 * now that we've moved on to the tree of log tree roots,
	 * check the full commit flag again
	 */
	if (btrfs_need_log_full_commit(fs_info, trans)) {
		blk_finish_plug(&plug);
		btrfs_wait_tree_log_extents(log, mark);
		btrfs_free_logged_extents(log, log_transid);
		mutex_unlock(&log_root_tree->log_mutex);
		ret = -EAGAIN;
		goto out_wake_log_root;
	}

	ret = btrfs_write_marked_extents(fs_info,
					 &log_root_tree->dirty_log_pages,
					 EXTENT_DIRTY | EXTENT_NEW);
	blk_finish_plug(&plug);
	if (ret) {
		btrfs_set_log_full_commit(fs_info, trans);
		btrfs_abort_transaction(trans, ret);
		btrfs_free_logged_extents(log, log_transid);
		mutex_unlock(&log_root_tree->log_mutex);
		goto out_wake_log_root;
	}
	ret = btrfs_wait_tree_log_extents(log, mark);
	if (!ret)
		ret = btrfs_wait_tree_log_extents(log_root_tree,
						  EXTENT_NEW | EXTENT_DIRTY);
	if (ret) {
		btrfs_set_log_full_commit(fs_info, trans);
		btrfs_free_logged_extents(log, log_transid);
		mutex_unlock(&log_root_tree->log_mutex);
		goto out_wake_log_root;
	}
	btrfs_wait_logged_extents(trans, log, log_transid);

	btrfs_set_super_log_root(fs_info->super_for_commit,
				 log_root_tree->node->start);
	btrfs_set_super_log_root_level(fs_info->super_for_commit,
				       btrfs_header_level(log_root_tree->node));

	log_root_tree->log_transid++;
	mutex_unlock(&log_root_tree->log_mutex);

	/*
	 * nobody else is going to jump in and write the the ctree
	 * super here because the log_commit atomic below is protecting
	 * us.  We must be called with a transaction handle pinning
	 * the running transaction open, so a full commit can't hop
	 * in and cause problems either.
	 */
	ret = write_all_supers(fs_info, 1);
	if (ret) {
		btrfs_set_log_full_commit(fs_info, trans);
		btrfs_abort_transaction(trans, ret);
		goto out_wake_log_root;
	}

	mutex_lock(&root->log_mutex);
	if (root->last_log_commit < log_transid)
		root->last_log_commit = log_transid;
	mutex_unlock(&root->log_mutex);

out_wake_log_root:
	mutex_lock(&log_root_tree->log_mutex);
	btrfs_remove_all_log_ctxs(log_root_tree, index2, ret);

	log_root_tree->log_transid_committed++;
	atomic_set(&log_root_tree->log_commit[index2], 0);
	mutex_unlock(&log_root_tree->log_mutex);

	/*
	 * The barrier before waitqueue_active is implied by mutex_unlock
	 */
	if (waitqueue_active(&log_root_tree->log_commit_wait[index2]))
		wake_up(&log_root_tree->log_commit_wait[index2]);
out:
	mutex_lock(&root->log_mutex);
	btrfs_remove_all_log_ctxs(root, index1, ret);
	root->log_transid_committed++;
	atomic_set(&root->log_commit[index1], 0);
	mutex_unlock(&root->log_mutex);

	/*
	 * The barrier before waitqueue_active is implied by mutex_unlock
	 */
	if (waitqueue_active(&root->log_commit_wait[index1]))
		wake_up(&root->log_commit_wait[index1]);
	return ret;
}
static void free_log_tree(struct btrfs_trans_handle *trans,
			  struct btrfs_root *log)
{
	int ret;
	u64 start;
	u64 end;
	struct walk_control wc = {
		.free = 1,
		.process_func = process_one_buffer
	};

	ret = walk_log_tree(trans, log, &wc);
	/* I don't think this can happen but just in case */
	if (ret)
		btrfs_abort_transaction(trans, ret);

	while (1) {
		ret = find_first_extent_bit(&log->dirty_log_pages,
				0, &start, &end, EXTENT_DIRTY | EXTENT_NEW,
				NULL);
		if (ret)
			break;

		clear_extent_bits(&log->dirty_log_pages, start, end,
				  EXTENT_DIRTY | EXTENT_NEW);
	}

	/*
	 * We may have short-circuited the log tree with the full commit logic
	 * and left ordered extents on our list, so clear these out to keep us
	 * from leaking inodes and memory.
	 */
	btrfs_free_logged_extents(log, 0);
	btrfs_free_logged_extents(log, 1);

	free_extent_buffer(log->node);
	kfree(log);
}
			  struct btrfs_log_ctx *ctx,
			  u64 min_offset, u64 *last_offset_ret)
{
	struct btrfs_key min_key;
	struct btrfs_root *log = root->log_root;
	struct extent_buffer *src;
	int err = 0;
	int ret;
	int i;
	int nritems;
	u64 first_offset = min_offset;
	u64 last_offset = (u64)-1;
	u64 ino = btrfs_ino(inode);

	log = root->log_root;

	min_key.objectid = ino;
	min_key.type = key_type;
	min_key.offset = min_offset;

	ret = btrfs_search_forward(root, &min_key, path, trans->transid);

	/*
	 * we didn't find anything from this transaction, see if there
	 * is anything at all
	 */
	if (ret != 0 || min_key.objectid != ino || min_key.type != key_type) {
		min_key.objectid = ino;
		min_key.type = key_type;
		min_key.offset = (u64)-1;
		btrfs_release_path(path);
		ret = btrfs_search_slot(NULL, root, &min_key, path, 0, 0);
		if (ret < 0) {
			btrfs_release_path(path);
			return ret;
		}
		ret = btrfs_previous_item(root, path, ino, key_type);

		/* if ret == 0 there are items for this type,
		 * create a range to tell us the last key of this type.
		 * otherwise, there are no items in this directory after
		 * *min_offset, and we create a range to indicate that.
		 */
		if (ret == 0) {
			struct btrfs_key tmp;
			btrfs_item_key_to_cpu(path->nodes[0], &tmp,
					      path->slots[0]);
			if (key_type == tmp.type)
				first_offset = max(min_offset, tmp.offset) + 1;
		}
		goto done;
	}

	/* go backward to find any previous key */
	ret = btrfs_previous_item(root, path, ino, key_type);
	if (ret == 0) {
		struct btrfs_key tmp;
		btrfs_item_key_to_cpu(path->nodes[0], &tmp, path->slots[0]);
		if (key_type == tmp.type) {
			first_offset = tmp.offset;
			ret = overwrite_item(trans, log, dst_path,
					     path->nodes[0], path->slots[0],
					     &tmp);
			if (ret) {
				err = ret;
				goto done;
			}
		}
	}
	btrfs_release_path(path);

	/* find the first key from this transaction again */
	ret = btrfs_search_slot(NULL, root, &min_key, path, 0, 0);
	if (WARN_ON(ret != 0))
		goto done;

	/*
	 * we have a block from this transaction, log every item in it
	 * from our directory
	 */
	while (1) {
		struct btrfs_key tmp;
		src = path->nodes[0];
		nritems = btrfs_header_nritems(src);
		for (i = path->slots[0]; i < nritems; i++) {
			struct btrfs_dir_item *di;

			btrfs_item_key_to_cpu(src, &min_key, i);

			if (min_key.objectid != ino || min_key.type != key_type)
				goto done;
			ret = overwrite_item(trans, log, dst_path, src, i,
					     &min_key);
			if (ret) {
				err = ret;
				goto done;
			}

			/*
			 * We must make sure that when we log a directory entry,
			 * the corresponding inode, after log replay, has a
			 * matching link count. For example:
			 *
			 * touch foo
			 * mkdir mydir
			 * sync
			 * ln foo mydir/bar
			 * xfs_io -c "fsync" mydir
			 * <crash>
			 * <mount fs and log replay>
			 *
			 * Would result in a fsync log that when replayed, our
			 * file inode would have a link count of 1, but we get
			 * two directory entries pointing to the same inode.
			 * After removing one of the names, it would not be
			 * possible to remove the other name, which resulted
			 * always in stale file handle errors, and would not
			 * be possible to rmdir the parent directory, since
			 * its i_size could never decrement to the value
			 * BTRFS_EMPTY_DIR_SIZE, resulting in -ENOTEMPTY errors.
			 */
			di = btrfs_item_ptr(src, i, struct btrfs_dir_item);
			btrfs_dir_item_key_to_cpu(src, di, &tmp);
			if (ctx &&
			    (btrfs_dir_transid(src, di) == trans->transid ||
			     btrfs_dir_type(src, di) == BTRFS_FT_DIR) &&
			    tmp.type != BTRFS_ROOT_ITEM_KEY)
				ctx->log_new_dentries = true;
		}
		path->slots[0] = nritems;

		/*
		 * look ahead to the next item and see if it is also
		 * from this directory and from this transaction
		 */
		ret = btrfs_next_leaf(root, path);
		if (ret == 1) {
			last_offset = (u64)-1;
			goto done;
		}
		btrfs_item_key_to_cpu(path->nodes[0], &tmp, path->slots[0]);
		if (tmp.objectid != ino || tmp.type != key_type) {
			last_offset = (u64)-1;
			goto done;
		}
		if (btrfs_header_generation(path->nodes[0]) != trans->transid) {
			ret = overwrite_item(trans, log, dst_path,
					     path->nodes[0], path->slots[0],
					     &tmp);
			if (ret)
				err = ret;
			else
				last_offset = tmp.offset;
			goto done;
		}
	}
done:
	btrfs_release_path(path);
	btrfs_release_path(dst_path);

	if (err == 0) {
		*last_offset_ret = last_offset;
		/*
		 * insert the log range keys to indicate where the log
		 * is valid
		 */
		ret = insert_dir_log_key(trans, log, path, key_type,
					 ino, first_offset, last_offset);
		if (ret)
			err = ret;
	}
	return err;
}
			  struct btrfs_path *dst_path,
			  struct btrfs_log_ctx *ctx)
{
	u64 min_key;
	u64 max_key;
	int ret;
	int key_type = BTRFS_DIR_ITEM_KEY;

again:
	min_key = 0;
	max_key = 0;
	while (1) {
		ret = log_dir_items(trans, root, inode, path, dst_path, key_type,
				ctx, min_key, &max_key);
		if (ret)
			return ret;
		if (max_key == (u64)-1)
			break;
		min_key = max_key + 1;
	}

	if (key_type == BTRFS_DIR_ITEM_KEY) {
		key_type = BTRFS_DIR_INDEX_KEY;
		goto again;
	}
	return 0;
}
				  struct btrfs_path *path,
				  u64 objectid, int max_key_type)
{
	int ret;
	struct btrfs_key key;
	struct btrfs_key found_key;
	int start_slot;

	key.objectid = objectid;
	key.type = max_key_type;
	key.offset = (u64)-1;

	while (1) {
		ret = btrfs_search_slot(trans, log, &key, path, -1, 1);
		BUG_ON(ret == 0); /* Logic error */
		if (ret < 0)
			break;

		if (path->slots[0] == 0)
			break;

		path->slots[0]--;
		btrfs_item_key_to_cpu(path->nodes[0], &found_key,
				      path->slots[0]);

		if (found_key.objectid != objectid)
			break;

		found_key.offset = 0;
		found_key.type = 0;
		ret = btrfs_bin_search(path->nodes[0], &found_key, 0,
				       &start_slot);

		ret = btrfs_del_items(trans, log, path, start_slot,
				      path->slots[0] - start_slot + 1);
		/*
		 * If start slot isn't 0 then we don't need to re-search, we've
		 * found the last guy with the objectid in this tree.
		 */
		if (ret || start_slot != 0)
			break;
		btrfs_release_path(path);
	}
	btrfs_release_path(path);
	if (ret > 0)
		ret = 0;
	return ret;
}
			       int start_slot, int nr, int inode_only,
			       u64 logged_isize)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->vfs_inode.i_sb);
	unsigned long src_offset;
	unsigned long dst_offset;
	struct btrfs_root *log = inode->root->log_root;
	struct btrfs_file_extent_item *extent;
	struct btrfs_inode_item *inode_item;
	struct extent_buffer *src = src_path->nodes[0];
	struct btrfs_key first_key, last_key, key;
	int ret;
	struct btrfs_key *ins_keys;
	u32 *ins_sizes;
	char *ins_data;
	int i;
	struct list_head ordered_sums;
	int skip_csum = inode->flags & BTRFS_INODE_NODATASUM;
	bool has_extents = false;
	bool need_find_last_extent = true;
	bool done = false;

	INIT_LIST_HEAD(&ordered_sums);

	ins_data = kmalloc(nr * sizeof(struct btrfs_key) +
			   nr * sizeof(u32), GFP_NOFS);
	if (!ins_data)
		return -ENOMEM;

	first_key.objectid = (u64)-1;

	ins_sizes = (u32 *)ins_data;
	ins_keys = (struct btrfs_key *)(ins_data + nr * sizeof(u32));

	for (i = 0; i < nr; i++) {
		ins_sizes[i] = btrfs_item_size_nr(src, i + start_slot);
		btrfs_item_key_to_cpu(src, ins_keys + i, i + start_slot);
	}
	ret = btrfs_insert_empty_items(trans, log, dst_path,
				       ins_keys, ins_sizes, nr);
	if (ret) {
		kfree(ins_data);
		return ret;
	}

	for (i = 0; i < nr; i++, dst_path->slots[0]++) {
		dst_offset = btrfs_item_ptr_offset(dst_path->nodes[0],
						   dst_path->slots[0]);

		src_offset = btrfs_item_ptr_offset(src, start_slot + i);

		if ((i == (nr - 1)))
			last_key = ins_keys[i];

		if (ins_keys[i].type == BTRFS_INODE_ITEM_KEY) {
			inode_item = btrfs_item_ptr(dst_path->nodes[0],
						    dst_path->slots[0],
						    struct btrfs_inode_item);
			fill_inode_item(trans, dst_path->nodes[0], inode_item,
					&inode->vfs_inode,
					inode_only == LOG_INODE_EXISTS,
					logged_isize);
		} else {
			copy_extent_buffer(dst_path->nodes[0], src, dst_offset,
					   src_offset, ins_sizes[i]);
		}

		/*
		 * We set need_find_last_extent here in case we know we were
		 * processing other items and then walk into the first extent in
		 * the inode.  If we don't hit an extent then nothing changes,
		 * we'll do the last search the next time around.
		 */
		if (ins_keys[i].type == BTRFS_EXTENT_DATA_KEY) {
			has_extents = true;
			if (first_key.objectid == (u64)-1)
				first_key = ins_keys[i];
		} else {
			need_find_last_extent = false;
		}

		/* take a reference on file data extents so that truncates
		 * or deletes of this inode don't have to relog the inode
		 * again
		 */
		if (ins_keys[i].type == BTRFS_EXTENT_DATA_KEY &&
		    !skip_csum) {
			int found_type;
			extent = btrfs_item_ptr(src, start_slot + i,
						struct btrfs_file_extent_item);

			if (btrfs_file_extent_generation(src, extent) < trans->transid)
				continue;

			found_type = btrfs_file_extent_type(src, extent);
			if (found_type == BTRFS_FILE_EXTENT_REG) {
				u64 ds, dl, cs, cl;
				ds = btrfs_file_extent_disk_bytenr(src,
								extent);
				/* ds == 0 is a hole */
				if (ds == 0)
					continue;

				dl = btrfs_file_extent_disk_num_bytes(src,
								extent);
				cs = btrfs_file_extent_offset(src, extent);
				cl = btrfs_file_extent_num_bytes(src,
								extent);
				if (btrfs_file_extent_compression(src,
								  extent)) {
					cs = 0;
					cl = dl;
				}

				ret = btrfs_lookup_csums_range(
						fs_info->csum_root,
						ds + cs, ds + cs + cl - 1,
						&ordered_sums, 0);
				if (ret) {
					btrfs_release_path(dst_path);
					kfree(ins_data);
					return ret;
				}
			}
		}
	}

	btrfs_mark_buffer_dirty(dst_path->nodes[0]);
	btrfs_release_path(dst_path);
	kfree(ins_data);

	/*
	 * we have to do this after the loop above to avoid changing the
	 * log tree while trying to change the log tree.
	 */
	ret = 0;
	while (!list_empty(&ordered_sums)) {
		struct btrfs_ordered_sum *sums = list_entry(ordered_sums.next,
						   struct btrfs_ordered_sum,
						   list);
		if (!ret)
			ret = btrfs_csum_file_blocks(trans, log, sums);
		list_del(&sums->list);
		kfree(sums);
	}

	if (!has_extents)
		return ret;

	if (need_find_last_extent && *last_extent == first_key.offset) {
		/*
		 * We don't have any leafs between our current one and the one
		 * we processed before that can have file extent items for our
		 * inode (and have a generation number smaller than our current
		 * transaction id).
		 */
		need_find_last_extent = false;
	}

	/*
	 * Because we use btrfs_search_forward we could skip leaves that were
	 * not modified and then assume *last_extent is valid when it really
	 * isn't.  So back up to the previous leaf and read the end of the last
	 * extent before we go and fill in holes.
	 */
	if (need_find_last_extent) {
		u64 len;

		ret = btrfs_prev_leaf(inode->root, src_path);
		if (ret < 0)
			return ret;
		if (ret)
			goto fill_holes;
		if (src_path->slots[0])
			src_path->slots[0]--;
		src = src_path->nodes[0];
		btrfs_item_key_to_cpu(src, &key, src_path->slots[0]);
		if (key.objectid != btrfs_ino(inode) ||
		    key.type != BTRFS_EXTENT_DATA_KEY)
			goto fill_holes;
		extent = btrfs_item_ptr(src, src_path->slots[0],
					struct btrfs_file_extent_item);
		if (btrfs_file_extent_type(src, extent) ==
		    BTRFS_FILE_EXTENT_INLINE) {
			len = btrfs_file_extent_inline_len(src,
							   src_path->slots[0],
							   extent);
			*last_extent = ALIGN(key.offset + len,
					     fs_info->sectorsize);
		} else {
			len = btrfs_file_extent_num_bytes(src, extent);
			*last_extent = key.offset + len;
		}
	}
fill_holes:
	/* So we did prev_leaf, now we need to move to the next leaf, but a few
	 * things could have happened
	 *
	 * 1) A merge could have happened, so we could currently be on a leaf
	 * that holds what we were copying in the first place.
	 * 2) A split could have happened, and now not all of the items we want
	 * are on the same leaf.
	 *
	 * So we need to adjust how we search for holes, we need to drop the
	 * path and re-search for the first extent key we found, and then walk
	 * forward until we hit the last one we copied.
	 */
	if (need_find_last_extent) {
		/* btrfs_prev_leaf could return 1 without releasing the path */
		btrfs_release_path(src_path);
		ret = btrfs_search_slot(NULL, inode->root, &first_key,
				src_path, 0, 0);
		if (ret < 0)
			return ret;
		ASSERT(ret == 0);
		src = src_path->nodes[0];
		i = src_path->slots[0];
	} else {
		i = start_slot;
	}

	/*
	 * Ok so here we need to go through and fill in any holes we may have
	 * to make sure that holes are punched for those areas in case they had
	 * extents previously.
	 */
	while (!done) {
		u64 offset, len;
		u64 extent_end;

		if (i >= btrfs_header_nritems(src_path->nodes[0])) {
			ret = btrfs_next_leaf(inode->root, src_path);
			if (ret < 0)
				return ret;
			ASSERT(ret == 0);
			src = src_path->nodes[0];
			i = 0;
		}

		btrfs_item_key_to_cpu(src, &key, i);
		if (!btrfs_comp_cpu_keys(&key, &last_key))
			done = true;
		if (key.objectid != btrfs_ino(inode) ||
		    key.type != BTRFS_EXTENT_DATA_KEY) {
			i++;
			continue;
		}
		extent = btrfs_item_ptr(src, i, struct btrfs_file_extent_item);
		if (btrfs_file_extent_type(src, extent) ==
		    BTRFS_FILE_EXTENT_INLINE) {
			len = btrfs_file_extent_inline_len(src, i, extent);
			extent_end = ALIGN(key.offset + len,
					   fs_info->sectorsize);
		} else {
			len = btrfs_file_extent_num_bytes(src, extent);
			extent_end = key.offset + len;
		}
		i++;

		if (*last_extent == key.offset) {
			*last_extent = extent_end;
			continue;
		}
		offset = *last_extent;
		len = key.offset - *last_extent;
		ret = btrfs_insert_file_extent(trans, log, btrfs_ino(inode),
				offset, 0, 0, len, 0, len, 0, 0, 0);
		if (ret)
			break;
		*last_extent = extent_end;
	}
	/*
	 * Need to let the callers know we dropped the path so they should
	 * re-search.
	 */
	if (!ret && need_find_last_extent)
		ret = 1;
	return ret;
}
				const struct list_head *logged_list,
				bool *ordered_io_error)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_ordered_extent *ordered;
	struct btrfs_root *log = root->log_root;
	u64 mod_start = em->mod_start;
	u64 mod_len = em->mod_len;
	const bool skip_csum = BTRFS_I(inode)->flags & BTRFS_INODE_NODATASUM;
	u64 csum_offset;
	u64 csum_len;
	LIST_HEAD(ordered_sums);
	int ret = 0;

	*ordered_io_error = false;

	if (test_bit(EXTENT_FLAG_PREALLOC, &em->flags) ||
	    em->block_start == EXTENT_MAP_HOLE)
		return 0;

	/*
	 * Wait far any ordered extent that covers our extent map. If it
	 * finishes without an error, first check and see if our csums are on
	 * our outstanding ordered extents.
	 */
	list_for_each_entry(ordered, logged_list, log_list) {
		struct btrfs_ordered_sum *sum;

		if (!mod_len)
			break;

		if (ordered->file_offset + ordered->len <= mod_start ||
		    mod_start + mod_len <= ordered->file_offset)
			continue;

		if (!test_bit(BTRFS_ORDERED_IO_DONE, &ordered->flags) &&
		    !test_bit(BTRFS_ORDERED_IOERR, &ordered->flags) &&
		    !test_bit(BTRFS_ORDERED_DIRECT, &ordered->flags)) {
			const u64 start = ordered->file_offset;
			const u64 end = ordered->file_offset + ordered->len - 1;

			WARN_ON(ordered->inode != inode);
			filemap_fdatawrite_range(inode->i_mapping, start, end);
		}

		wait_event(ordered->wait,
			   (test_bit(BTRFS_ORDERED_IO_DONE, &ordered->flags) ||
			    test_bit(BTRFS_ORDERED_IOERR, &ordered->flags)));

		if (test_bit(BTRFS_ORDERED_IOERR, &ordered->flags)) {
			/*
			 * Clear the AS_EIO/AS_ENOSPC flags from the inode's
			 * i_mapping flags, so that the next fsync won't get
			 * an outdated io error too.
			 */
			filemap_check_errors(inode->i_mapping);
			*ordered_io_error = true;
			break;
		}
		/*
		 * We are going to copy all the csums on this ordered extent, so
		 * go ahead and adjust mod_start and mod_len in case this
		 * ordered extent has already been logged.
		 */
		if (ordered->file_offset > mod_start) {
			if (ordered->file_offset + ordered->len >=
			    mod_start + mod_len)
				mod_len = ordered->file_offset - mod_start;
			/*
			 * If we have this case
			 *
			 * |--------- logged extent ---------|
			 *       |----- ordered extent ----|
			 *
			 * Just don't mess with mod_start and mod_len, we'll
			 * just end up logging more csums than we need and it
			 * will be ok.
			 */
		} else {
			if (ordered->file_offset + ordered->len <
			    mod_start + mod_len) {
				mod_len = (mod_start + mod_len) -
					(ordered->file_offset + ordered->len);
				mod_start = ordered->file_offset +
					ordered->len;
			} else {
				mod_len = 0;
			}
		}

		if (skip_csum)
			continue;

		/*
		 * To keep us from looping for the above case of an ordered
		 * extent that falls inside of the logged extent.
		 */
		if (test_and_set_bit(BTRFS_ORDERED_LOGGED_CSUM,
				     &ordered->flags))
			continue;

		list_for_each_entry(sum, &ordered->list, list) {
			ret = btrfs_csum_file_blocks(trans, log, sum);
			if (ret)
				break;
		}
	}

	if (*ordered_io_error || !mod_len || ret || skip_csum)
		return ret;

	if (em->compress_type) {
		csum_offset = 0;
		csum_len = max(em->block_len, em->orig_block_len);
	} else {
		csum_offset = mod_start - em->start;
		csum_len = mod_len;
	}

	/* block start is already adjusted for the file extent offset. */
	ret = btrfs_lookup_csums_range(fs_info->csum_root,
				       em->block_start + csum_offset,
				       em->block_start + csum_offset +
				       csum_len - 1, &ordered_sums, 0);
	if (ret)
		return ret;

	while (!list_empty(&ordered_sums)) {
		struct btrfs_ordered_sum *sums = list_entry(ordered_sums.next,
						   struct btrfs_ordered_sum,
						   list);
		if (!ret)
			ret = btrfs_csum_file_blocks(trans, log, sums);
		list_del(&sums->list);
		kfree(sums);
	}

	return ret;
}
				     const u64 start,
				     const u64 end)
{
	struct extent_map *em, *n;
	struct list_head extents;
	struct extent_map_tree *tree = &inode->extent_tree;
	u64 test_gen;
	int ret = 0;
	int num = 0;

	INIT_LIST_HEAD(&extents);

	down_write(&inode->dio_sem);
	write_lock(&tree->lock);
	test_gen = root->fs_info->last_trans_committed;

	list_for_each_entry_safe(em, n, &tree->modified_extents, list) {
		list_del_init(&em->list);

		/*
		 * Just an arbitrary number, this can be really CPU intensive
		 * once we start getting a lot of extents, and really once we
		 * have a bunch of extents we just want to commit since it will
		 * be faster.
		 */
		if (++num > 32768) {
			list_del_init(&tree->modified_extents);
			ret = -EFBIG;
			goto process;
		}

		if (em->generation <= test_gen)
			continue;
		/* Need a ref to keep it from getting evicted from cache */
		refcount_inc(&em->refs);
		set_bit(EXTENT_FLAG_LOGGING, &em->flags);
		list_add_tail(&em->list, &extents);
		num++;
	}

	list_sort(NULL, &extents, extent_cmp);
	btrfs_get_logged_extents(inode, logged_list, start, end);
	/*
	 * Some ordered extents started by fsync might have completed
	 * before we could collect them into the list logged_list, which
	 * means they're gone, not in our logged_list nor in the inode's
	 * ordered tree. We want the application/user space to know an
	 * error happened while attempting to persist file data so that
	 * it can take proper action. If such error happened, we leave
	 * without writing to the log tree and the fsync must report the
	 * file data write error and not commit the current transaction.
	 */
	ret = filemap_check_errors(inode->vfs_inode.i_mapping);
	if (ret)
		ctx->io_err = ret;
process:
	while (!list_empty(&extents)) {
		em = list_entry(extents.next, struct extent_map, list);

		list_del_init(&em->list);

		/*
		 * If we had an error we just need to delete everybody from our
		 * private list.
		 */
		if (ret) {
			clear_em_logging(tree, em);
			free_extent_map(em);
			continue;
		}

		write_unlock(&tree->lock);

		ret = log_one_extent(trans, inode, root, em, path, logged_list,
				     ctx);
		write_lock(&tree->lock);
		clear_em_logging(tree, em);
		free_extent_map(em);
	}
	WARN_ON(!list_empty(&extents));
	write_unlock(&tree->lock);
	up_write(&inode->dio_sem);

	btrfs_release_path(path);
	return ret;
}
				struct btrfs_path *path,
				struct btrfs_path *dst_path)
{
	int ret;
	struct btrfs_key key;
	const u64 ino = btrfs_ino(inode);
	int ins_nr = 0;
	int start_slot = 0;

	key.objectid = ino;
	key.type = BTRFS_XATTR_ITEM_KEY;
	key.offset = 0;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		return ret;

	while (true) {
		int slot = path->slots[0];
		struct extent_buffer *leaf = path->nodes[0];
		int nritems = btrfs_header_nritems(leaf);

		if (slot >= nritems) {
			if (ins_nr > 0) {
				u64 last_extent = 0;

				ret = copy_items(trans, inode, dst_path, path,
						 &last_extent, start_slot,
						 ins_nr, 1, 0);
				/* can't be 1, extent items aren't processed */
				ASSERT(ret <= 0);
				if (ret < 0)
					return ret;
				ins_nr = 0;
			}
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				return ret;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);
		if (key.objectid != ino || key.type != BTRFS_XATTR_ITEM_KEY)
			break;

		if (ins_nr == 0)
			start_slot = slot;
		ins_nr++;
		path->slots[0]++;
		cond_resched();
	}
	if (ins_nr > 0) {
		u64 last_extent = 0;

		ret = copy_items(trans, inode, dst_path, path,
				 &last_extent, start_slot,
				 ins_nr, 1, 0);
		/* can't be 1, extent items aren't processed */
		ASSERT(ret <= 0);
		if (ret < 0)
			return ret;
	}

	return 0;
}
					 struct btrfs_inode *inode,
					 u64 *other_ino)
{
	int ret;
	struct btrfs_path *search_path;
	char *name = NULL;
	u32 name_len = 0;
	u32 item_size = btrfs_item_size_nr(eb, slot);
	u32 cur_offset = 0;
	unsigned long ptr = btrfs_item_ptr_offset(eb, slot);

	search_path = btrfs_alloc_path();
	if (!search_path)
		return -ENOMEM;
	search_path->search_commit_root = 1;
	search_path->skip_locking = 1;

	while (cur_offset < item_size) {
		u64 parent;
		u32 this_name_len;
		u32 this_len;
		unsigned long name_ptr;
		struct btrfs_dir_item *di;

		if (key->type == BTRFS_INODE_REF_KEY) {
			struct btrfs_inode_ref *iref;

			iref = (struct btrfs_inode_ref *)(ptr + cur_offset);
			parent = key->offset;
			this_name_len = btrfs_inode_ref_name_len(eb, iref);
			name_ptr = (unsigned long)(iref + 1);
			this_len = sizeof(*iref) + this_name_len;
		} else {
			struct btrfs_inode_extref *extref;

			extref = (struct btrfs_inode_extref *)(ptr +
							       cur_offset);
			parent = btrfs_inode_extref_parent(eb, extref);
			this_name_len = btrfs_inode_extref_name_len(eb, extref);
			name_ptr = (unsigned long)&extref->name;
			this_len = sizeof(*extref) + this_name_len;
		}

		if (this_name_len > name_len) {
			char *new_name;

			new_name = krealloc(name, this_name_len, GFP_NOFS);
			if (!new_name) {
				ret = -ENOMEM;
				goto out;
			}
			name_len = this_name_len;
			name = new_name;
		}

		read_extent_buffer(eb, name, name_ptr, this_name_len);
		di = btrfs_lookup_dir_item(NULL, inode->root, search_path,
				parent, name, this_name_len, 0);
		if (di && !IS_ERR(di)) {
			struct btrfs_key di_key;

			btrfs_dir_item_key_to_cpu(search_path->nodes[0],
						  di, &di_key);
			if (di_key.type == BTRFS_INODE_ITEM_KEY) {
				ret = 1;
				*other_ino = di_key.objectid;
			} else {
				ret = -EAGAIN;
			}
			goto out;
		} else if (IS_ERR(di)) {
			ret = PTR_ERR(di);
			goto out;
		}
		btrfs_release_path(search_path);

		cur_offset += this_len;
	}
	ret = 0;
out:
	btrfs_free_path(search_path);
	kfree(name);
	return ret;
}
			   const loff_t end,
			   struct btrfs_log_ctx *ctx)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_path *path;
	struct btrfs_path *dst_path;
	struct btrfs_key min_key;
	struct btrfs_key max_key;
	struct btrfs_root *log = root->log_root;
	struct extent_buffer *src = NULL;
	LIST_HEAD(logged_list);
	u64 last_extent = 0;
	int err = 0;
	int ret;
	int nritems;
	int ins_start_slot = 0;
	int ins_nr;
	bool fast_search = false;
	u64 ino = btrfs_ino(inode);
	struct extent_map_tree *em_tree = &inode->extent_tree;
	u64 logged_isize = 0;
	bool need_log_inode_item = true;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	dst_path = btrfs_alloc_path();
	if (!dst_path) {
		btrfs_free_path(path);
		return -ENOMEM;
	}

	min_key.objectid = ino;
	min_key.type = BTRFS_INODE_ITEM_KEY;
	min_key.offset = 0;

	max_key.objectid = ino;


	/* today the code can only do partial logging of directories */
	if (S_ISDIR(inode->vfs_inode.i_mode) ||
	    (!test_bit(BTRFS_INODE_NEEDS_FULL_SYNC,
		       &inode->runtime_flags) &&
	     inode_only >= LOG_INODE_EXISTS))
		max_key.type = BTRFS_XATTR_ITEM_KEY;
	else
		max_key.type = (u8)-1;
	max_key.offset = (u64)-1;

	/*
	 * Only run delayed items if we are a dir or a new file.
	 * Otherwise commit the delayed inode only, which is needed in
	 * order for the log replay code to mark inodes for link count
	 * fixup (create temporary BTRFS_TREE_LOG_FIXUP_OBJECTID items).
	 */
	if (S_ISDIR(inode->vfs_inode.i_mode) ||
	    inode->generation > fs_info->last_trans_committed)
		ret = btrfs_commit_inode_delayed_items(trans, inode);
	else
		ret = btrfs_commit_inode_delayed_inode(inode);

	if (ret) {
		btrfs_free_path(path);
		btrfs_free_path(dst_path);
		return ret;
	}

	if (inode_only == LOG_OTHER_INODE) {
		inode_only = LOG_INODE_EXISTS;
		mutex_lock_nested(&inode->log_mutex, SINGLE_DEPTH_NESTING);
	} else {
		mutex_lock(&inode->log_mutex);
	}

	/*
	 * a brute force approach to making sure we get the most uptodate
	 * copies of everything.
	 */
	if (S_ISDIR(inode->vfs_inode.i_mode)) {
		int max_key_type = BTRFS_DIR_LOG_INDEX_KEY;

		if (inode_only == LOG_INODE_EXISTS)
			max_key_type = BTRFS_XATTR_ITEM_KEY;
		ret = drop_objectid_items(trans, log, path, ino, max_key_type);
	} else {
		if (inode_only == LOG_INODE_EXISTS) {
			/*
			 * Make sure the new inode item we write to the log has
			 * the same isize as the current one (if it exists).
			 * This is necessary to prevent data loss after log
			 * replay, and also to prevent doing a wrong expanding
			 * truncate - for e.g. create file, write 4K into offset
			 * 0, fsync, write 4K into offset 4096, add hard link,
			 * fsync some other file (to sync log), power fail - if
			 * we use the inode's current i_size, after log replay
			 * we get a 8Kb file, with the last 4Kb extent as a hole
			 * (zeroes), as if an expanding truncate happened,
			 * instead of getting a file of 4Kb only.
			 */
			err = logged_inode_size(log, inode, path, &logged_isize);
			if (err)
				goto out_unlock;
		}
		if (test_bit(BTRFS_INODE_NEEDS_FULL_SYNC,
			     &inode->runtime_flags)) {
			if (inode_only == LOG_INODE_EXISTS) {
				max_key.type = BTRFS_XATTR_ITEM_KEY;
				ret = drop_objectid_items(trans, log, path, ino,
							  max_key.type);
			} else {
				clear_bit(BTRFS_INODE_NEEDS_FULL_SYNC,
					  &inode->runtime_flags);
				clear_bit(BTRFS_INODE_COPY_EVERYTHING,
					  &inode->runtime_flags);
				while(1) {
					ret = btrfs_truncate_inode_items(trans,
						log, &inode->vfs_inode, 0, 0);
					if (ret != -EAGAIN)
						break;
				}
			}
		} else if (test_and_clear_bit(BTRFS_INODE_COPY_EVERYTHING,
					      &inode->runtime_flags) ||
			   inode_only == LOG_INODE_EXISTS) {
			if (inode_only == LOG_INODE_ALL)
				fast_search = true;
			max_key.type = BTRFS_XATTR_ITEM_KEY;
			ret = drop_objectid_items(trans, log, path, ino,
						  max_key.type);
		} else {
			if (inode_only == LOG_INODE_ALL)
				fast_search = true;
			goto log_extents;
		}

	}
	if (ret) {
		err = ret;
		goto out_unlock;
	}

	while (1) {
		ins_nr = 0;
		ret = btrfs_search_forward(root, &min_key,
					   path, trans->transid);
		if (ret < 0) {
			err = ret;
			goto out_unlock;
		}
		if (ret != 0)
			break;
again:
		/* note, ins_nr might be > 0 here, cleanup outside the loop */
		if (min_key.objectid != ino)
			break;
		if (min_key.type > max_key.type)
			break;

		if (min_key.type == BTRFS_INODE_ITEM_KEY)
			need_log_inode_item = false;

		if ((min_key.type == BTRFS_INODE_REF_KEY ||
		     min_key.type == BTRFS_INODE_EXTREF_KEY) &&
		    inode->generation == trans->transid) {
			u64 other_ino = 0;

			ret = btrfs_check_ref_name_override(path->nodes[0],
					path->slots[0], &min_key, inode,
					&other_ino);
			if (ret < 0) {
				err = ret;
				goto out_unlock;
			} else if (ret > 0 && ctx &&
				   other_ino != btrfs_ino(BTRFS_I(ctx->inode))) {
				struct btrfs_key inode_key;
				struct inode *other_inode;

				if (ins_nr > 0) {
					ins_nr++;
				} else {
					ins_nr = 1;
					ins_start_slot = path->slots[0];
				}
				ret = copy_items(trans, inode, dst_path, path,
						 &last_extent, ins_start_slot,
						 ins_nr, inode_only,
						 logged_isize);
				if (ret < 0) {
					err = ret;
					goto out_unlock;
				}
				ins_nr = 0;
				btrfs_release_path(path);
				inode_key.objectid = other_ino;
				inode_key.type = BTRFS_INODE_ITEM_KEY;
				inode_key.offset = 0;
				other_inode = btrfs_iget(fs_info->sb,
							 &inode_key, root,
							 NULL);
				/*
				 * If the other inode that had a conflicting dir
				 * entry was deleted in the current transaction,
				 * we don't need to do more work nor fallback to
				 * a transaction commit.
				 */
				if (IS_ERR(other_inode) &&
				    PTR_ERR(other_inode) == -ENOENT) {
					goto next_key;
				} else if (IS_ERR(other_inode)) {
					err = PTR_ERR(other_inode);
					goto out_unlock;
				}
				/*
				 * We are safe logging the other inode without
				 * acquiring its i_mutex as long as we log with
				 * the LOG_INODE_EXISTS mode. We're safe against
				 * concurrent renames of the other inode as well
				 * because during a rename we pin the log and
				 * update the log with the new name before we
				 * unpin it.
				 */
				err = btrfs_log_inode(trans, root,
						BTRFS_I(other_inode),
						LOG_OTHER_INODE, 0, LLONG_MAX,
						ctx);
				iput(other_inode);
				if (err)
					goto out_unlock;
				else
					goto next_key;
			}
		}

		/* Skip xattrs, we log them later with btrfs_log_all_xattrs() */
		if (min_key.type == BTRFS_XATTR_ITEM_KEY) {
			if (ins_nr == 0)
				goto next_slot;
			ret = copy_items(trans, inode, dst_path, path,
					 &last_extent, ins_start_slot,
					 ins_nr, inode_only, logged_isize);
			if (ret < 0) {
				err = ret;
				goto out_unlock;
			}
			ins_nr = 0;
			if (ret) {
				btrfs_release_path(path);
				continue;
			}
			goto next_slot;
		}

		src = path->nodes[0];
		if (ins_nr && ins_start_slot + ins_nr == path->slots[0]) {
			ins_nr++;
			goto next_slot;
		} else if (!ins_nr) {
			ins_start_slot = path->slots[0];
			ins_nr = 1;
			goto next_slot;
		}

		ret = copy_items(trans, inode, dst_path, path, &last_extent,
				 ins_start_slot, ins_nr, inode_only,
				 logged_isize);
		if (ret < 0) {
			err = ret;
			goto out_unlock;
		}
		if (ret) {
			ins_nr = 0;
			btrfs_release_path(path);
			continue;
		}
		ins_nr = 1;
		ins_start_slot = path->slots[0];
next_slot:

		nritems = btrfs_header_nritems(path->nodes[0]);
		path->slots[0]++;
		if (path->slots[0] < nritems) {
			btrfs_item_key_to_cpu(path->nodes[0], &min_key,
					      path->slots[0]);
			goto again;
		}
		if (ins_nr) {
			ret = copy_items(trans, inode, dst_path, path,
					 &last_extent, ins_start_slot,
					 ins_nr, inode_only, logged_isize);
			if (ret < 0) {
				err = ret;
				goto out_unlock;
			}
			ret = 0;
			ins_nr = 0;
		}
		btrfs_release_path(path);
next_key:
		if (min_key.offset < (u64)-1) {
			min_key.offset++;
		} else if (min_key.type < max_key.type) {
			min_key.type++;
			min_key.offset = 0;
		} else {
			break;
		}
	}
	if (ins_nr) {
		ret = copy_items(trans, inode, dst_path, path, &last_extent,
				 ins_start_slot, ins_nr, inode_only,
				 logged_isize);
		if (ret < 0) {
			err = ret;
			goto out_unlock;
		}
		ret = 0;
		ins_nr = 0;
	}

	btrfs_release_path(path);
	btrfs_release_path(dst_path);
	err = btrfs_log_all_xattrs(trans, root, inode, path, dst_path);
	if (err)
		goto out_unlock;
	if (max_key.type >= BTRFS_EXTENT_DATA_KEY && !fast_search) {
		btrfs_release_path(path);
		btrfs_release_path(dst_path);
		err = btrfs_log_trailing_hole(trans, root, inode, path);
		if (err)
			goto out_unlock;
	}
log_extents:
	btrfs_release_path(path);
	btrfs_release_path(dst_path);
	if (need_log_inode_item) {
		err = log_inode_item(trans, log, dst_path, inode);
		if (err)
			goto out_unlock;
	}
	if (fast_search) {
		ret = btrfs_log_changed_extents(trans, root, inode, dst_path,
						&logged_list, ctx, start, end);
		if (ret) {
			err = ret;
			goto out_unlock;
		}
	} else if (inode_only == LOG_INODE_ALL) {
		struct extent_map *em, *n;

		write_lock(&em_tree->lock);
		/*
		 * We can't just remove every em if we're called for a ranged
		 * fsync - that is, one that doesn't cover the whole possible
		 * file range (0 to LLONG_MAX). This is because we can have
		 * em's that fall outside the range we're logging and therefore
		 * their ordered operations haven't completed yet
		 * (btrfs_finish_ordered_io() not invoked yet). This means we
		 * didn't get their respective file extent item in the fs/subvol
		 * tree yet, and need to let the next fast fsync (one which
		 * consults the list of modified extent maps) find the em so
		 * that it logs a matching file extent item and waits for the
		 * respective ordered operation to complete (if it's still
		 * running).
		 *
		 * Removing every em outside the range we're logging would make
		 * the next fast fsync not log their matching file extent items,
		 * therefore making us lose data after a log replay.
		 */
		list_for_each_entry_safe(em, n, &em_tree->modified_extents,
					 list) {
			const u64 mod_end = em->mod_start + em->mod_len - 1;

			if (em->mod_start >= start && mod_end <= end)
				list_del_init(&em->list);
		}
		write_unlock(&em_tree->lock);
	}

	if (inode_only == LOG_INODE_ALL && S_ISDIR(inode->vfs_inode.i_mode)) {
		ret = log_directory_changes(trans, root, inode, path, dst_path,
					ctx);
		if (ret) {
			err = ret;
			goto out_unlock;
		}
	}

	spin_lock(&inode->lock);
	inode->logged_trans = trans->transid;
	inode->last_log_commit = inode->last_sub_trans;
	spin_unlock(&inode->lock);
out_unlock:
	if (unlikely(err))
		btrfs_put_logged_extents(&logged_list);
	else
		btrfs_submit_logged_extents(&logged_list, log);
	mutex_unlock(&inode->log_mutex);

	btrfs_free_path(path);
	btrfs_free_path(dst_path);
	return err;
}
					       struct super_block *sb,
					       u64 last_committed)
{
	int ret = 0;
	struct dentry *old_parent = NULL;
	struct btrfs_inode *orig_inode = inode;

	/*
	 * for regular files, if its inode is already on disk, we don't
	 * have to worry about the parents at all.  This is because
	 * we can use the last_unlink_trans field to record renames
	 * and other fun in this file.
	 */
	if (S_ISREG(inode->vfs_inode.i_mode) &&
	    inode->generation <= last_committed &&
	    inode->last_unlink_trans <= last_committed)
		goto out;

	if (!S_ISDIR(inode->vfs_inode.i_mode)) {
		if (!parent || d_really_is_negative(parent) || sb != parent->d_sb)
			goto out;
		inode = BTRFS_I(d_inode(parent));
	}

	while (1) {
		/*
		 * If we are logging a directory then we start with our inode,
		 * not our parent's inode, so we need to skip setting the
		 * logged_trans so that further down in the log code we don't
		 * think this inode has already been logged.
		 */
		if (inode != orig_inode)
			inode->logged_trans = trans->transid;
		smp_mb();

		if (btrfs_must_commit_transaction(trans, inode)) {
			ret = 1;
			break;
		}

		if (!parent || d_really_is_negative(parent) || sb != parent->d_sb)
			break;

		if (IS_ROOT(parent)) {
			inode = BTRFS_I(d_inode(parent));
			if (btrfs_must_commit_transaction(trans, inode))
				ret = 1;
			break;
		}

		parent = dget_parent(parent);
		dput(old_parent);
		old_parent = parent;
		inode = BTRFS_I(d_inode(parent));

	}
	dput(old_parent);
out:
	return ret;
}
				struct btrfs_inode *start_inode,
				struct btrfs_log_ctx *ctx)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_root *log = root->log_root;
	struct btrfs_path *path;
	LIST_HEAD(dir_list);
	struct btrfs_dir_list *dir_elem;
	int ret = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	dir_elem = kmalloc(sizeof(*dir_elem), GFP_NOFS);
	if (!dir_elem) {
		btrfs_free_path(path);
		return -ENOMEM;
	}
	dir_elem->ino = btrfs_ino(start_inode);
	list_add_tail(&dir_elem->list, &dir_list);

	while (!list_empty(&dir_list)) {
		struct extent_buffer *leaf;
		struct btrfs_key min_key;
		int nritems;
		int i;

		dir_elem = list_first_entry(&dir_list, struct btrfs_dir_list,
					    list);
		if (ret)
			goto next_dir_inode;

		min_key.objectid = dir_elem->ino;
		min_key.type = BTRFS_DIR_ITEM_KEY;
		min_key.offset = 0;
again:
		btrfs_release_path(path);
		ret = btrfs_search_forward(log, &min_key, path, trans->transid);
		if (ret < 0) {
			goto next_dir_inode;
		} else if (ret > 0) {
			ret = 0;
			goto next_dir_inode;
		}

process_leaf:
		leaf = path->nodes[0];
		nritems = btrfs_header_nritems(leaf);
		for (i = path->slots[0]; i < nritems; i++) {
			struct btrfs_dir_item *di;
			struct btrfs_key di_key;
			struct inode *di_inode;
			struct btrfs_dir_list *new_dir_elem;
			int log_mode = LOG_INODE_EXISTS;
			int type;

			btrfs_item_key_to_cpu(leaf, &min_key, i);
			if (min_key.objectid != dir_elem->ino ||
			    min_key.type != BTRFS_DIR_ITEM_KEY)
				goto next_dir_inode;

			di = btrfs_item_ptr(leaf, i, struct btrfs_dir_item);
			type = btrfs_dir_type(leaf, di);
			if (btrfs_dir_transid(leaf, di) < trans->transid &&
			    type != BTRFS_FT_DIR)
				continue;
			btrfs_dir_item_key_to_cpu(leaf, di, &di_key);
			if (di_key.type == BTRFS_ROOT_ITEM_KEY)
				continue;

			btrfs_release_path(path);
			di_inode = btrfs_iget(fs_info->sb, &di_key, root, NULL);
			if (IS_ERR(di_inode)) {
				ret = PTR_ERR(di_inode);
				goto next_dir_inode;
			}

			if (btrfs_inode_in_log(BTRFS_I(di_inode), trans->transid)) {
				iput(di_inode);
				break;
			}

			ctx->log_new_dentries = false;
			if (type == BTRFS_FT_DIR || type == BTRFS_FT_SYMLINK)
				log_mode = LOG_INODE_ALL;
			ret = btrfs_log_inode(trans, root, BTRFS_I(di_inode),
					      log_mode, 0, LLONG_MAX, ctx);
			if (!ret &&
			    btrfs_must_commit_transaction(trans, BTRFS_I(di_inode)))
				ret = 1;
			iput(di_inode);
			if (ret)
				goto next_dir_inode;
			if (ctx->log_new_dentries) {
				new_dir_elem = kmalloc(sizeof(*new_dir_elem),
						       GFP_NOFS);
				if (!new_dir_elem) {
					ret = -ENOMEM;
					goto next_dir_inode;
				}
				new_dir_elem->ino = di_key.objectid;
				list_add_tail(&new_dir_elem->list, &dir_list);
			}
			break;
		}
		if (i == nritems) {
			ret = btrfs_next_leaf(log, path);
			if (ret < 0) {
				goto next_dir_inode;
			} else if (ret > 0) {
				ret = 0;
				goto next_dir_inode;
			}
			goto process_leaf;
		}
		if (min_key.offset < (u64)-1) {
			min_key.offset++;
			goto again;
		}
next_dir_inode:
		list_del(&dir_elem->list);
		kfree(dir_elem);
	}

	btrfs_free_path(path);
	return ret;
}
				 struct btrfs_inode *inode,
				 struct btrfs_log_ctx *ctx)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->vfs_inode.i_sb);
	int ret;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_root *root = inode->root;
	const u64 ino = btrfs_ino(inode);

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->skip_locking = 1;
	path->search_commit_root = 1;

	key.objectid = ino;
	key.type = BTRFS_INODE_REF_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (true) {
		struct extent_buffer *leaf = path->nodes[0];
		int slot = path->slots[0];
		u32 cur_offset = 0;
		u32 item_size;
		unsigned long ptr;

		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);
		/* BTRFS_INODE_EXTREF_KEY is BTRFS_INODE_REF_KEY + 1 */
		if (key.objectid != ino || key.type > BTRFS_INODE_EXTREF_KEY)
			break;

		item_size = btrfs_item_size_nr(leaf, slot);
		ptr = btrfs_item_ptr_offset(leaf, slot);
		while (cur_offset < item_size) {
			struct btrfs_key inode_key;
			struct inode *dir_inode;

			inode_key.type = BTRFS_INODE_ITEM_KEY;
			inode_key.offset = 0;

			if (key.type == BTRFS_INODE_EXTREF_KEY) {
				struct btrfs_inode_extref *extref;

				extref = (struct btrfs_inode_extref *)
					(ptr + cur_offset);
				inode_key.objectid = btrfs_inode_extref_parent(
					leaf, extref);
				cur_offset += sizeof(*extref);
				cur_offset += btrfs_inode_extref_name_len(leaf,
					extref);
			} else {
				inode_key.objectid = key.offset;
				cur_offset = item_size;
			}

			dir_inode = btrfs_iget(fs_info->sb, &inode_key,
					       root, NULL);
			/* If parent inode was deleted, skip it. */
			if (IS_ERR(dir_inode))
				continue;

			if (ctx)
				ctx->log_new_dentries = false;
			ret = btrfs_log_inode(trans, root, BTRFS_I(dir_inode),
					      LOG_INODE_ALL, 0, LLONG_MAX, ctx);
			if (!ret &&
			    btrfs_must_commit_transaction(trans, BTRFS_I(dir_inode)))
				ret = 1;
			if (!ret && ctx && ctx->log_new_dentries)
				ret = log_new_dir_dentries(trans, root,
						   BTRFS_I(dir_inode), ctx);
			iput(dir_inode);
			if (ret)
				goto out;
		}
		path->slots[0]++;
	}
	ret = 0;
out:
	btrfs_free_path(path);
	return ret;
}
				  int exists_only,
				  struct btrfs_log_ctx *ctx)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int inode_only = exists_only ? LOG_INODE_EXISTS : LOG_INODE_ALL;
	struct super_block *sb;
	struct dentry *old_parent = NULL;
	int ret = 0;
	u64 last_committed = fs_info->last_trans_committed;
	bool log_dentries = false;
	struct btrfs_inode *orig_inode = inode;

	sb = inode->vfs_inode.i_sb;

	if (btrfs_test_opt(fs_info, NOTREELOG)) {
		ret = 1;
		goto end_no_trans;
	}

	/*
	 * The prev transaction commit doesn't complete, we need do
	 * full commit by ourselves.
	 */
	if (fs_info->last_trans_log_full_commit >
	    fs_info->last_trans_committed) {
		ret = 1;
		goto end_no_trans;
	}

	if (root != inode->root || btrfs_root_refs(&root->root_item) == 0) {
		ret = 1;
		goto end_no_trans;
	}

	ret = check_parent_dirs_for_sync(trans, inode, parent, sb,
			last_committed);
	if (ret)
		goto end_no_trans;

	if (btrfs_inode_in_log(inode, trans->transid)) {
		ret = BTRFS_NO_LOG_SYNC;
		goto end_no_trans;
	}

	ret = start_log_trans(trans, root, ctx);
	if (ret)
		goto end_no_trans;

	ret = btrfs_log_inode(trans, root, inode, inode_only, start, end, ctx);
	if (ret)
		goto end_trans;

	/*
	 * for regular files, if its inode is already on disk, we don't
	 * have to worry about the parents at all.  This is because
	 * we can use the last_unlink_trans field to record renames
	 * and other fun in this file.
	 */
	if (S_ISREG(inode->vfs_inode.i_mode) &&
	    inode->generation <= last_committed &&
	    inode->last_unlink_trans <= last_committed) {
		ret = 0;
		goto end_trans;
	}

	if (S_ISDIR(inode->vfs_inode.i_mode) && ctx && ctx->log_new_dentries)
		log_dentries = true;

	/*
	 * On unlink we must make sure all our current and old parent directory
	 * inodes are fully logged. This is to prevent leaving dangling
	 * directory index entries in directories that were our parents but are
	 * not anymore. Not doing this results in old parent directory being
	 * impossible to delete after log replay (rmdir will always fail with
	 * error -ENOTEMPTY).
	 *
	 * Example 1:
	 *
	 * mkdir testdir
	 * touch testdir/foo
	 * ln testdir/foo testdir/bar
	 * sync
	 * unlink testdir/bar
	 * xfs_io -c fsync testdir/foo
	 * <power failure>
	 * mount fs, triggers log replay
	 *
	 * If we don't log the parent directory (testdir), after log replay the
	 * directory still has an entry pointing to the file inode using the bar
	 * name, but a matching BTRFS_INODE_[REF|EXTREF]_KEY does not exist and
	 * the file inode has a link count of 1.
	 *
	 * Example 2:
	 *
	 * mkdir testdir
	 * touch foo
	 * ln foo testdir/foo2
	 * ln foo testdir/foo3
	 * sync
	 * unlink testdir/foo3
	 * xfs_io -c fsync foo
	 * <power failure>
	 * mount fs, triggers log replay
	 *
	 * Similar as the first example, after log replay the parent directory
	 * testdir still has an entry pointing to the inode file with name foo3
	 * but the file inode does not have a matching BTRFS_INODE_REF_KEY item
	 * and has a link count of 2.
	 */
	if (inode->last_unlink_trans > last_committed) {
		ret = btrfs_log_all_parents(trans, orig_inode, ctx);
		if (ret)
			goto end_trans;
	}

	while (1) {
		if (!parent || d_really_is_negative(parent) || sb != parent->d_sb)
			break;

		inode = BTRFS_I(d_inode(parent));
		if (root != inode->root)
			break;

		if (inode->generation > last_committed) {
			ret = btrfs_log_inode(trans, root, inode,
					LOG_INODE_EXISTS, 0, LLONG_MAX, ctx);
			if (ret)
				goto end_trans;
		}
		if (IS_ROOT(parent))
			break;

		parent = dget_parent(parent);
		dput(old_parent);
		old_parent = parent;
	}
	if (log_dentries)
		ret = log_new_dir_dentries(trans, root, orig_inode, ctx);
	else
		ret = 0;
end_trans:
	dput(old_parent);
	if (ret < 0) {
		btrfs_set_log_full_commit(fs_info, trans);
		ret = 1;
	}

	if (ret)
		btrfs_remove_log_ctx(root, ctx);
	btrfs_end_log_trans(root);
end_no_trans:
	return ret;
}
 */
int btrfs_recover_log_trees(struct btrfs_root *log_root_tree)
{
	int ret;
	struct btrfs_path *path;
	struct btrfs_trans_handle *trans;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_key tmp_key;
	struct btrfs_root *log;
	struct btrfs_fs_info *fs_info = log_root_tree->fs_info;
	struct walk_control wc = {
		.process_func = process_one_buffer,
		.stage = 0,
	};

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	set_bit(BTRFS_FS_LOG_RECOVERING, &fs_info->flags);

	trans = btrfs_start_transaction(fs_info->tree_root, 0);
	if (IS_ERR(trans)) {
		ret = PTR_ERR(trans);
		goto error;
	}

	wc.trans = trans;
	wc.pin = 1;

	ret = walk_log_tree(trans, log_root_tree, &wc);
	if (ret) {
		btrfs_handle_fs_error(fs_info, ret,
			"Failed to pin buffers while recovering log root tree.");
		goto error;
	}

again:
	key.objectid = BTRFS_TREE_LOG_OBJECTID;
	key.offset = (u64)-1;
	key.type = BTRFS_ROOT_ITEM_KEY;

	while (1) {
		ret = btrfs_search_slot(NULL, log_root_tree, &key, path, 0, 0);

		if (ret < 0) {
			btrfs_handle_fs_error(fs_info, ret,
				    "Couldn't find tree log root.");
			goto error;
		}
		if (ret > 0) {
			if (path->slots[0] == 0)
				break;
			path->slots[0]--;
		}
		btrfs_item_key_to_cpu(path->nodes[0], &found_key,
				      path->slots[0]);
		btrfs_release_path(path);
		if (found_key.objectid != BTRFS_TREE_LOG_OBJECTID)
			break;

		log = btrfs_read_fs_root(log_root_tree, &found_key);
		if (IS_ERR(log)) {
			ret = PTR_ERR(log);
			btrfs_handle_fs_error(fs_info, ret,
				    "Couldn't read tree log root.");
			goto error;
		}

		tmp_key.objectid = found_key.offset;
		tmp_key.type = BTRFS_ROOT_ITEM_KEY;
		tmp_key.offset = (u64)-1;

		wc.replay_dest = btrfs_read_fs_root_no_name(fs_info, &tmp_key);
		if (IS_ERR(wc.replay_dest)) {
			ret = PTR_ERR(wc.replay_dest);
			free_extent_buffer(log->node);
			free_extent_buffer(log->commit_root);
			kfree(log);
			btrfs_handle_fs_error(fs_info, ret,
				"Couldn't read target root for tree log recovery.");
			goto error;
		}

		wc.replay_dest->log_root = log;
		btrfs_record_root_in_trans(trans, wc.replay_dest);
		ret = walk_log_tree(trans, log, &wc);

		if (!ret && wc.stage == LOG_WALK_REPLAY_ALL) {
			ret = fixup_inode_link_counts(trans, wc.replay_dest,
						      path);
		}

		key.offset = found_key.offset - 1;
		wc.replay_dest->log_root = NULL;
		free_extent_buffer(log->node);
		free_extent_buffer(log->commit_root);
		kfree(log);

		if (ret)
			goto error;

		if (found_key.offset == 0)
			break;
	}
	btrfs_release_path(path);

	/* step one is to pin it all, step two is to replay just inodes */
	if (wc.pin) {
		wc.pin = 0;
		wc.process_func = replay_one_buffer;
		wc.stage = LOG_WALK_REPLAY_INODES;
		goto again;
	}
	/* step three is to replay everything */
	if (wc.stage < LOG_WALK_REPLAY_ALL) {
		wc.stage++;
		goto again;
	}

	btrfs_free_path(path);

	/* step 4: commit the transaction, which also unpins the blocks */
	ret = btrfs_commit_transaction(trans);
	if (ret)
		return ret;

	free_extent_buffer(log_root_tree->node);
	log_root_tree->log_root = NULL;
	clear_bit(BTRFS_FS_LOG_RECOVERING, &fs_info->flags);
	kfree(log_root_tree);

	return 0;
error:
	if (wc.trans)
		btrfs_end_transaction(wc.trans);
	btrfs_free_path(path);
	return ret;
}
