/* Free all nodes in the ref tree, and reinit ref_root */
static void ref_root_fini(struct ref_root *ref_tree)
{
	struct ref_node *node;
	struct rb_node *next;

	while ((next = rb_first(&ref_tree->rb_root)) != NULL) {
		node = rb_entry(next, struct ref_node, rb_node);
		rb_erase(next, &ref_tree->rb_root);
		kfree(node);
	}

	ref_tree->rb_root = RB_ROOT;
	ref_tree->unique_refs = 0;
}
					  u64 root_id, u64 object_id,
					  u64 offset, u64 parent)
{
	struct ref_node *cur = NULL;
	struct ref_node entry;
	int ret;

	entry.root_id = root_id;
	entry.object_id = object_id;
	entry.offset = offset;
	entry.parent = parent;

	*pos = &ref_tree->rb_root.rb_node;

	while (**pos) {
		*pos_parent = **pos;
		cur = rb_entry(*pos_parent, struct ref_node, rb_node);

		ret = ref_node_cmp(cur, &entry);
		if (ret > 0)
			*pos = &(**pos)->rb_left;
		else if (ret < 0)
			*pos = &(**pos)->rb_right;
		else
			return cur;
	}

	return NULL;
}

static void free_inode_elem_list(struct extent_inode_elem *eie)
{
	struct extent_inode_elem *eie_next;

	for (; eie; eie = eie_next) {
		eie_next = eie->next;
		kfree(eie);
	}
}
				u64 extent_item_pos,
				struct extent_inode_elem **eie)
{
	u64 disk_byte;
	struct btrfs_key key;
	struct btrfs_file_extent_item *fi;
	int slot;
	int nritems;
	int extent_type;
	int ret;

	/*
	 * from the shared data ref, we only have the leaf but we need
	 * the key. thus, we must look into all items and see that we
	 * find one (some) with a reference to our extent item.
	 */
	nritems = btrfs_header_nritems(eb);
	for (slot = 0; slot < nritems; ++slot) {
		btrfs_item_key_to_cpu(eb, &key, slot);
		if (key.type != BTRFS_EXTENT_DATA_KEY)
			continue;
		fi = btrfs_item_ptr(eb, slot, struct btrfs_file_extent_item);
		extent_type = btrfs_file_extent_type(eb, fi);
		if (extent_type == BTRFS_FILE_EXTENT_INLINE)
			continue;
		/* don't skip BTRFS_FILE_EXTENT_PREALLOC, we can handle that */
		disk_byte = btrfs_file_extent_disk_bytenr(eb, fi);
		if (disk_byte != wanted_disk_byte)
			continue;

		ret = check_extent_in_eb(&key, eb, fi, extent_item_pos, eie);
		if (ret < 0)
			return ret;
	}

	return 0;
}
			   int level, u64 time_seq, const u64 *extent_item_pos,
			   u64 total_refs)
{
	int ret = 0;
	int slot;
	struct extent_buffer *eb;
	struct btrfs_key key;
	struct btrfs_key *key_for_search = &ref->key_for_search;
	struct btrfs_file_extent_item *fi;
	struct extent_inode_elem *eie = NULL, *old = NULL;
	u64 disk_byte;
	u64 wanted_disk_byte = ref->wanted_disk_byte;
	u64 count = 0;

	if (level != 0) {
		eb = path->nodes[level];
		ret = ulist_add(parents, eb->start, 0, GFP_NOFS);
		if (ret < 0)
			return ret;
		return 0;
	}

	/*
	 * We normally enter this function with the path already pointing to
	 * the first item to check. But sometimes, we may enter it with
	 * slot==nritems. In that case, go to the next leaf before we continue.
	 */
	if (path->slots[0] >= btrfs_header_nritems(path->nodes[0])) {
		if (time_seq == SEQ_LAST)
			ret = btrfs_next_leaf(root, path);
		else
			ret = btrfs_next_old_leaf(root, path, time_seq);
	}

	while (!ret && count < total_refs) {
		eb = path->nodes[0];
		slot = path->slots[0];

		btrfs_item_key_to_cpu(eb, &key, slot);

		if (key.objectid != key_for_search->objectid ||
		    key.type != BTRFS_EXTENT_DATA_KEY)
			break;

		fi = btrfs_item_ptr(eb, slot, struct btrfs_file_extent_item);
		disk_byte = btrfs_file_extent_disk_bytenr(eb, fi);

		if (disk_byte == wanted_disk_byte) {
			eie = NULL;
			old = NULL;
			count++;
			if (extent_item_pos) {
				ret = check_extent_in_eb(&key, eb, fi,
						*extent_item_pos,
						&eie);
				if (ret < 0)
					break;
			}
			if (ret > 0)
				goto next;
			ret = ulist_add_merge_ptr(parents, eb->start,
						  eie, (void **)&old, GFP_NOFS);
			if (ret < 0)
				break;
			if (!ret && extent_item_pos) {
				while (old->next)
					old = old->next;
				old->next = eie;
			}
			eie = NULL;
		}
next:
		if (time_seq == SEQ_LAST)
			ret = btrfs_next_item(root, path);
		else
			ret = btrfs_next_old_item(root, path, time_seq);
	}

	if (ret > 0)
		ret = 0;
	else if (ret < 0)
		free_inode_elem_list(eie);
	return ret;
}
				  struct ulist *parents,
				  const u64 *extent_item_pos, u64 total_refs)
{
	struct btrfs_root *root;
	struct btrfs_key root_key;
	struct extent_buffer *eb;
	int ret = 0;
	int root_level;
	int level = ref->level;
	int index;

	root_key.objectid = ref->root_id;
	root_key.type = BTRFS_ROOT_ITEM_KEY;
	root_key.offset = (u64)-1;

	index = srcu_read_lock(&fs_info->subvol_srcu);

	root = btrfs_get_fs_root(fs_info, &root_key, false);
	if (IS_ERR(root)) {
		srcu_read_unlock(&fs_info->subvol_srcu, index);
		ret = PTR_ERR(root);
		goto out;
	}

	if (btrfs_is_testing(fs_info)) {
		srcu_read_unlock(&fs_info->subvol_srcu, index);
		ret = -ENOENT;
		goto out;
	}

	if (path->search_commit_root)
		root_level = btrfs_header_level(root->commit_root);
	else if (time_seq == SEQ_LAST)
		root_level = btrfs_header_level(root->node);
	else
		root_level = btrfs_old_root_level(root, time_seq);

	if (root_level + 1 == level) {
		srcu_read_unlock(&fs_info->subvol_srcu, index);
		goto out;
	}

	path->lowest_level = level;
	if (time_seq == SEQ_LAST)
		ret = btrfs_search_slot(NULL, root, &ref->key_for_search, path,
					0, 0);
	else
		ret = btrfs_search_old_slot(root, &ref->key_for_search, path,
					    time_seq);

	/* root node has been locked, we can release @subvol_srcu safely here */
	srcu_read_unlock(&fs_info->subvol_srcu, index);

	btrfs_debug(fs_info,
		"search slot in root %llu (level %d, ref count %d) returned %d for key (%llu %u %llu)",
		 ref->root_id, level, ref->count, ret,
		 ref->key_for_search.objectid, ref->key_for_search.type,
		 ref->key_for_search.offset);
	if (ret < 0)
		goto out;

	eb = path->nodes[level];
	while (!eb) {
		if (WARN_ON(!level)) {
			ret = 1;
			goto out;
		}
		level--;
		eb = path->nodes[level];
	}

	ret = add_all_parents(root, path, parents, ref, level, time_seq,
			      extent_item_pos, total_refs);
out:
	path->lowest_level = 0;
	btrfs_release_path(path);
	return ret;
}
				   const u64 *extent_item_pos, u64 total_refs,
				   u64 root_objectid)
{
	int err;
	int ret = 0;
	struct __prelim_ref *ref;
	struct __prelim_ref *ref_safe;
	struct __prelim_ref *new_ref;
	struct ulist *parents;
	struct ulist_node *node;
	struct ulist_iterator uiter;

	parents = ulist_alloc(GFP_NOFS);
	if (!parents)
		return -ENOMEM;

	/*
	 * _safe allows us to insert directly after the current item without
	 * iterating over the newly inserted items.
	 * we're also allowed to re-assign ref during iteration.
	 */
	list_for_each_entry_safe(ref, ref_safe, head, list) {
		if (ref->parent)	/* already direct */
			continue;
		if (ref->count == 0)
			continue;
		if (root_objectid && ref->root_id != root_objectid) {
			ret = BACKREF_FOUND_SHARED;
			goto out;
		}
		err = __resolve_indirect_ref(fs_info, path, time_seq, ref,
					     parents, extent_item_pos,
					     total_refs);
		/*
		 * we can only tolerate ENOENT,otherwise,we should catch error
		 * and return directly.
		 */
		if (err == -ENOENT) {
			continue;
		} else if (err) {
			ret = err;
			goto out;
		}

		/* we put the first parent into the ref at hand */
		ULIST_ITER_INIT(&uiter);
		node = ulist_next(parents, &uiter);
		ref->parent = node ? node->val : 0;
		ref->inode_list = node ?
			(struct extent_inode_elem *)(uintptr_t)node->aux : NULL;

		/* additional parents require new refs being added here */
		while ((node = ulist_next(parents, &uiter))) {
			new_ref = kmem_cache_alloc(btrfs_prelim_ref_cache,
						   GFP_NOFS);
			if (!new_ref) {
				ret = -ENOMEM;
				goto out;
			}
			memcpy(new_ref, ref, sizeof(*ref));
			new_ref->parent = node->val;
			new_ref->inode_list = (struct extent_inode_elem *)
							(uintptr_t)node->aux;
			list_add(&new_ref->list, &ref->list);
		}
		ulist_reinit(parents);
	}
out:
	ulist_free(parents);
	return ret;
}
 */
static void __merge_refs(struct list_head *head, enum merge_mode mode)
{
	struct __prelim_ref *pos1;

	list_for_each_entry(pos1, head, list) {
		struct __prelim_ref *pos2 = pos1, *tmp;

		list_for_each_entry_safe_continue(pos2, tmp, head, list) {
			struct __prelim_ref *ref1 = pos1, *ref2 = pos2;
			struct extent_inode_elem *eie;

			if (!ref_for_same_block(ref1, ref2))
				continue;
			if (mode == MERGE_IDENTICAL_KEYS) {
				if (!ref1->parent && ref2->parent)
					swap(ref1, ref2);
			} else {
				if (ref1->parent != ref2->parent)
					continue;
			}

			eie = ref1->inode_list;
			while (eie && eie->next)
				eie = eie->next;
			if (eie)
				eie->next = ref2->inode_list;
			else
				ref1->inode_list = ref2->inode_list;
			ref1->count += ref2->count;

			list_del(&ref2->list);
			kmem_cache_free(btrfs_prelim_ref_cache, ref2);
			cond_resched();
		}

	}
}
			     struct ref_root *ref_tree,
			     u64 *total_refs, u64 inum)
{
	int ret = 0;
	int slot;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	struct btrfs_key found_key;
	unsigned long ptr;
	unsigned long end;
	struct btrfs_extent_item *ei;
	u64 flags;
	u64 item_size;

	/*
	 * enumerate all inline refs
	 */
	leaf = path->nodes[0];
	slot = path->slots[0];

	item_size = btrfs_item_size_nr(leaf, slot);
	BUG_ON(item_size < sizeof(*ei));

	ei = btrfs_item_ptr(leaf, slot, struct btrfs_extent_item);
	flags = btrfs_extent_flags(leaf, ei);
	*total_refs += btrfs_extent_refs(leaf, ei);
	btrfs_item_key_to_cpu(leaf, &found_key, slot);

	ptr = (unsigned long)(ei + 1);
	end = (unsigned long)ei + item_size;

	if (found_key.type == BTRFS_EXTENT_ITEM_KEY &&
	    flags & BTRFS_EXTENT_FLAG_TREE_BLOCK) {
		struct btrfs_tree_block_info *info;

		info = (struct btrfs_tree_block_info *)ptr;
		*info_level = btrfs_tree_block_level(leaf, info);
		ptr += sizeof(struct btrfs_tree_block_info);
		BUG_ON(ptr > end);
	} else if (found_key.type == BTRFS_METADATA_ITEM_KEY) {
		*info_level = found_key.offset;
	} else {
		BUG_ON(!(flags & BTRFS_EXTENT_FLAG_DATA));
	}

	while (ptr < end) {
		struct btrfs_extent_inline_ref *iref;
		u64 offset;
		int type;

		iref = (struct btrfs_extent_inline_ref *)ptr;
		type = btrfs_extent_inline_ref_type(leaf, iref);
		offset = btrfs_extent_inline_ref_offset(leaf, iref);

		switch (type) {
		case BTRFS_SHARED_BLOCK_REF_KEY:
			ret = __add_prelim_ref(prefs, 0, NULL,
						*info_level + 1, offset,
						bytenr, 1, GFP_NOFS);
			break;
		case BTRFS_SHARED_DATA_REF_KEY: {
			struct btrfs_shared_data_ref *sdref;
			int count;

			sdref = (struct btrfs_shared_data_ref *)(iref + 1);
			count = btrfs_shared_data_ref_count(leaf, sdref);
			ret = __add_prelim_ref(prefs, 0, NULL, 0, offset,
					       bytenr, count, GFP_NOFS);
			if (ref_tree) {
				if (!ret)
					ret = ref_tree_add(ref_tree, 0, 0, 0,
							   bytenr, count);
				if (!ret && ref_tree->unique_refs > 1)
					ret = BACKREF_FOUND_SHARED;
			}
			break;
		}
		case BTRFS_TREE_BLOCK_REF_KEY:
			ret = __add_prelim_ref(prefs, offset, NULL,
					       *info_level + 1, 0,
					       bytenr, 1, GFP_NOFS);
			break;
		case BTRFS_EXTENT_DATA_REF_KEY: {
			struct btrfs_extent_data_ref *dref;
			int count;
			u64 root;

			dref = (struct btrfs_extent_data_ref *)(&iref->offset);
			count = btrfs_extent_data_ref_count(leaf, dref);
			key.objectid = btrfs_extent_data_ref_objectid(leaf,
								      dref);
			key.type = BTRFS_EXTENT_DATA_KEY;
			key.offset = btrfs_extent_data_ref_offset(leaf, dref);

			if (inum && key.objectid != inum) {
				ret = BACKREF_FOUND_SHARED;
				break;
			}

			root = btrfs_extent_data_ref_root(leaf, dref);
			ret = __add_prelim_ref(prefs, root, &key, 0, 0,
					       bytenr, count, GFP_NOFS);
			if (ref_tree) {
				if (!ret)
					ret = ref_tree_add(ref_tree, root,
							   key.objectid,
							   key.offset, 0,
							   count);
				if (!ret && ref_tree->unique_refs > 1)
					ret = BACKREF_FOUND_SHARED;
			}
			break;
		}
		default:
			WARN_ON(1);
		}
		if (ret)
			return ret;
		ptr += btrfs_extent_inline_ref_size(type);
	}

	return 0;
}
			    int info_level, struct list_head *prefs,
			    struct ref_root *ref_tree, u64 inum)
{
	struct btrfs_root *extent_root = fs_info->extent_root;
	int ret;
	int slot;
	struct extent_buffer *leaf;
	struct btrfs_key key;

	while (1) {
		ret = btrfs_next_item(extent_root, path);
		if (ret < 0)
			break;
		if (ret) {
			ret = 0;
			break;
		}

		slot = path->slots[0];
		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &key, slot);

		if (key.objectid != bytenr)
			break;
		if (key.type < BTRFS_TREE_BLOCK_REF_KEY)
			continue;
		if (key.type > BTRFS_SHARED_DATA_REF_KEY)
			break;

		switch (key.type) {
		case BTRFS_SHARED_BLOCK_REF_KEY:
			ret = __add_prelim_ref(prefs, 0, NULL,
						info_level + 1, key.offset,
						bytenr, 1, GFP_NOFS);
			break;
		case BTRFS_SHARED_DATA_REF_KEY: {
			struct btrfs_shared_data_ref *sdref;
			int count;

			sdref = btrfs_item_ptr(leaf, slot,
					      struct btrfs_shared_data_ref);
			count = btrfs_shared_data_ref_count(leaf, sdref);
			ret = __add_prelim_ref(prefs, 0, NULL, 0, key.offset,
						bytenr, count, GFP_NOFS);
			if (ref_tree) {
				if (!ret)
					ret = ref_tree_add(ref_tree, 0, 0, 0,
							   bytenr, count);
				if (!ret && ref_tree->unique_refs > 1)
					ret = BACKREF_FOUND_SHARED;
			}
			break;
		}
		case BTRFS_TREE_BLOCK_REF_KEY:
			ret = __add_prelim_ref(prefs, key.offset, NULL,
					       info_level + 1, 0,
					       bytenr, 1, GFP_NOFS);
			break;
		case BTRFS_EXTENT_DATA_REF_KEY: {
			struct btrfs_extent_data_ref *dref;
			int count;
			u64 root;

			dref = btrfs_item_ptr(leaf, slot,
					      struct btrfs_extent_data_ref);
			count = btrfs_extent_data_ref_count(leaf, dref);
			key.objectid = btrfs_extent_data_ref_objectid(leaf,
								      dref);
			key.type = BTRFS_EXTENT_DATA_KEY;
			key.offset = btrfs_extent_data_ref_offset(leaf, dref);

			if (inum && key.objectid != inum) {
				ret = BACKREF_FOUND_SHARED;
				break;
			}

			root = btrfs_extent_data_ref_root(leaf, dref);
			ret = __add_prelim_ref(prefs, root, &key, 0, 0,
					       bytenr, count, GFP_NOFS);
			if (ref_tree) {
				if (!ret)
					ret = ref_tree_add(ref_tree, root,
							   key.objectid,
							   key.offset, 0,
							   count);
				if (!ret && ref_tree->unique_refs > 1)
					ret = BACKREF_FOUND_SHARED;
			}
			break;
		}
		default:
			WARN_ON(1);
		}
		if (ret)
			return ret;

	}

	return ret;
}
			     struct ulist *roots, const u64 *extent_item_pos,
			     u64 root_objectid, u64 inum, int check_shared)
{
	struct btrfs_key key;
	struct btrfs_path *path;
	struct btrfs_delayed_ref_root *delayed_refs = NULL;
	struct btrfs_delayed_ref_head *head;
	int info_level = 0;
	int ret;
	struct list_head prefs_delayed;
	struct list_head prefs;
	struct __prelim_ref *ref;
	struct extent_inode_elem *eie = NULL;
	struct ref_root *ref_tree = NULL;
	u64 total_refs = 0;

	INIT_LIST_HEAD(&prefs);
	INIT_LIST_HEAD(&prefs_delayed);

	key.objectid = bytenr;
	key.offset = (u64)-1;
	if (btrfs_fs_incompat(fs_info, SKINNY_METADATA))
		key.type = BTRFS_METADATA_ITEM_KEY;
	else
		key.type = BTRFS_EXTENT_ITEM_KEY;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	if (!trans) {
		path->search_commit_root = 1;
		path->skip_locking = 1;
	}

	if (time_seq == SEQ_LAST)
		path->skip_locking = 1;

	/*
	 * grab both a lock on the path and a lock on the delayed ref head.
	 * We need both to get a consistent picture of how the refs look
	 * at a specified point in time
	 */
again:
	head = NULL;

	if (check_shared) {
		if (!ref_tree) {
			ref_tree = ref_root_alloc();
			if (!ref_tree) {
				ret = -ENOMEM;
				goto out;
			}
		} else {
			ref_root_fini(ref_tree);
		}
	}

	ret = btrfs_search_slot(trans, fs_info->extent_root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	BUG_ON(ret == 0);

#ifdef CONFIG_BTRFS_FS_RUN_SANITY_TESTS
	if (trans && likely(trans->type != __TRANS_DUMMY) &&
	    time_seq != SEQ_LAST) {
#else
	if (trans && time_seq != SEQ_LAST) {
#endif
		/*
		 * look if there are updates for this ref queued and lock the
		 * head
		 */
		delayed_refs = &trans->transaction->delayed_refs;
		spin_lock(&delayed_refs->lock);
		head = btrfs_find_delayed_ref_head(delayed_refs, bytenr);
		if (head) {
			if (!mutex_trylock(&head->mutex)) {
				refcount_inc(&head->node.refs);
				spin_unlock(&delayed_refs->lock);

				btrfs_release_path(path);

				/*
				 * Mutex was contended, block until it's
				 * released and try again
				 */
				mutex_lock(&head->mutex);
				mutex_unlock(&head->mutex);
				btrfs_put_delayed_ref(&head->node);
				goto again;
			}
			spin_unlock(&delayed_refs->lock);
			ret = __add_delayed_refs(head, time_seq,
						 &prefs_delayed, &total_refs,
						 inum);
			mutex_unlock(&head->mutex);
			if (ret)
				goto out;
		} else {
			spin_unlock(&delayed_refs->lock);
		}

		if (check_shared && !list_empty(&prefs_delayed)) {
			/*
			 * Add all delay_ref to the ref_tree and check if there
			 * are multiple ref items added.
			 */
			list_for_each_entry(ref, &prefs_delayed, list) {
				if (ref->key_for_search.type) {
					ret = ref_tree_add(ref_tree,
						ref->root_id,
						ref->key_for_search.objectid,
						ref->key_for_search.offset,
						0, ref->count);
					if (ret)
						goto out;
				} else {
					ret = ref_tree_add(ref_tree, 0, 0, 0,
						     ref->parent, ref->count);
					if (ret)
						goto out;
				}

			}

			if (ref_tree->unique_refs > 1) {
				ret = BACKREF_FOUND_SHARED;
				goto out;
			}

		}
	}

	if (path->slots[0]) {
		struct extent_buffer *leaf;
		int slot;

		path->slots[0]--;
		leaf = path->nodes[0];
		slot = path->slots[0];
		btrfs_item_key_to_cpu(leaf, &key, slot);
		if (key.objectid == bytenr &&
		    (key.type == BTRFS_EXTENT_ITEM_KEY ||
		     key.type == BTRFS_METADATA_ITEM_KEY)) {
			ret = __add_inline_refs(path, bytenr,
						&info_level, &prefs,
						ref_tree, &total_refs,
						inum);
			if (ret)
				goto out;
			ret = __add_keyed_refs(fs_info, path, bytenr,
					       info_level, &prefs,
					       ref_tree, inum);
			if (ret)
				goto out;
		}
	}
	btrfs_release_path(path);

	list_splice_init(&prefs_delayed, &prefs);

	ret = __add_missing_keys(fs_info, &prefs);
	if (ret)
		goto out;

	__merge_refs(&prefs, MERGE_IDENTICAL_KEYS);

	ret = __resolve_indirect_refs(fs_info, path, time_seq, &prefs,
				      extent_item_pos, total_refs,
				      root_objectid);
	if (ret)
		goto out;

	__merge_refs(&prefs, MERGE_IDENTICAL_PARENTS);

	while (!list_empty(&prefs)) {
		ref = list_first_entry(&prefs, struct __prelim_ref, list);
		WARN_ON(ref->count < 0);
		if (roots && ref->count && ref->root_id && ref->parent == 0) {
			if (root_objectid && ref->root_id != root_objectid) {
				ret = BACKREF_FOUND_SHARED;
				goto out;
			}

			/* no parent == root of tree */
			ret = ulist_add(roots, ref->root_id, 0, GFP_NOFS);
			if (ret < 0)
				goto out;
		}
		if (ref->count && ref->parent) {
			if (extent_item_pos && !ref->inode_list &&
			    ref->level == 0) {
				struct extent_buffer *eb;

				eb = read_tree_block(fs_info, ref->parent, 0);
				if (IS_ERR(eb)) {
					ret = PTR_ERR(eb);
					goto out;
				} else if (!extent_buffer_uptodate(eb)) {
					free_extent_buffer(eb);
					ret = -EIO;
					goto out;
				}
				btrfs_tree_read_lock(eb);
				btrfs_set_lock_blocking_rw(eb, BTRFS_READ_LOCK);
				ret = find_extent_in_eb(eb, bytenr,
							*extent_item_pos, &eie);
				btrfs_tree_read_unlock_blocking(eb);
				free_extent_buffer(eb);
				if (ret < 0)
					goto out;
				ref->inode_list = eie;
			}
			ret = ulist_add_merge_ptr(refs, ref->parent,
						  ref->inode_list,
						  (void **)&eie, GFP_NOFS);
			if (ret < 0)
				goto out;
			if (!ret && extent_item_pos) {
				/*
				 * we've recorded that parent, so we must extend
				 * its inode list here
				 */
				BUG_ON(!eie);
				while (eie->next)
					eie = eie->next;
				eie->next = ref->inode_list;
			}
			eie = NULL;
		}
		list_del(&ref->list);
		kmem_cache_free(btrfs_prelim_ref_cache, ref);
	}

out:
	btrfs_free_path(path);
	ref_root_free(ref_tree);
	while (!list_empty(&prefs)) {
		ref = list_first_entry(&prefs, struct __prelim_ref, list);
		list_del(&ref->list);
		kmem_cache_free(btrfs_prelim_ref_cache, ref);
	}
	while (!list_empty(&prefs_delayed)) {
		ref = list_first_entry(&prefs_delayed, struct __prelim_ref,
				       list);
		list_del(&ref->list);
		kmem_cache_free(btrfs_prelim_ref_cache, ref);
	}
	if (ret < 0)
		free_inode_elem_list(eie);
	return ret;
}

static void free_leaf_list(struct ulist *blocks)
{
	struct ulist_node *node = NULL;
	struct extent_inode_elem *eie;
	struct ulist_iterator uiter;

	ULIST_ITER_INIT(&uiter);
	while ((node = ulist_next(blocks, &uiter))) {
		if (!node->aux)
			continue;
		eie = (struct extent_inode_elem *)(uintptr_t)node->aux;
		free_inode_elem_list(eie);
		node->aux = 0;
	}

	ulist_free(blocks);
}
				  struct btrfs_fs_info *fs_info, u64 bytenr,
				  u64 time_seq, struct ulist **roots)
{
	struct ulist *tmp;
	struct ulist_node *node = NULL;
	struct ulist_iterator uiter;
	int ret;

	tmp = ulist_alloc(GFP_NOFS);
	if (!tmp)
		return -ENOMEM;
	*roots = ulist_alloc(GFP_NOFS);
	if (!*roots) {
		ulist_free(tmp);
		return -ENOMEM;
	}

	ULIST_ITER_INIT(&uiter);
	while (1) {
		ret = find_parent_nodes(trans, fs_info, bytenr, time_seq,
					tmp, *roots, NULL, 0, 0, 0);
		if (ret < 0 && ret != -ENOENT) {
			ulist_free(tmp);
			ulist_free(*roots);
			return ret;
		}
		node = ulist_next(tmp, &uiter);
		if (!node)
			break;
		bytenr = node->val;
		cond_resched();
	}

	ulist_free(tmp);
	return 0;
}
		       struct btrfs_fs_info *fs_info, u64 root_objectid,
		       u64 inum, u64 bytenr)
{
	struct ulist *tmp = NULL;
	struct ulist *roots = NULL;
	struct ulist_iterator uiter;
	struct ulist_node *node;
	struct seq_list elem = SEQ_LIST_INIT(elem);
	int ret = 0;

	tmp = ulist_alloc(GFP_NOFS);
	roots = ulist_alloc(GFP_NOFS);
	if (!tmp || !roots) {
		ulist_free(tmp);
		ulist_free(roots);
		return -ENOMEM;
	}

	if (trans)
		btrfs_get_tree_mod_seq(fs_info, &elem);
	else
		down_read(&fs_info->commit_root_sem);
	ULIST_ITER_INIT(&uiter);
	while (1) {
		ret = find_parent_nodes(trans, fs_info, bytenr, elem.seq, tmp,
					roots, NULL, root_objectid, inum, 1);
		if (ret == BACKREF_FOUND_SHARED) {
			/* this is the only condition under which we return 1 */
			ret = 1;
			break;
		}
		if (ret < 0 && ret != -ENOENT)
			break;
		ret = 0;
		node = ulist_next(tmp, &uiter);
		if (!node)
			break;
		bytenr = node->val;
		cond_resched();
	}
	if (trans)
		btrfs_put_tree_mod_seq(fs_info, &elem);
	else
		up_read(&fs_info->commit_root_sem);
	ulist_free(tmp);
	ulist_free(roots);
	return ret;
}
			  struct btrfs_inode_extref **ret_extref,
			  u64 *found_off)
{
	int ret, slot;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_inode_extref *extref;
	struct extent_buffer *leaf;
	unsigned long ptr;

	key.objectid = inode_objectid;
	key.type = BTRFS_INODE_EXTREF_KEY;
	key.offset = start_off;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		return ret;

	while (1) {
		leaf = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(leaf)) {
			/*
			 * If the item at offset is not found,
			 * btrfs_search_slot will point us to the slot
			 * where it should be inserted. In our case
			 * that will be the slot directly before the
			 * next INODE_REF_KEY_V2 item. In the case
			 * that we're pointing to the last slot in a
			 * leaf, we must move one leaf over.
			 */
			ret = btrfs_next_leaf(root, path);
			if (ret) {
				if (ret >= 1)
					ret = -ENOENT;
				break;
			}
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		/*
		 * Check that we're still looking at an extended ref key for
		 * this particular objectid. If we have different
		 * objectid or type then there are no more to be found
		 * in the tree and we can exit.
		 */
		ret = -ENOENT;
		if (found_key.objectid != inode_objectid)
			break;
		if (found_key.type != BTRFS_INODE_EXTREF_KEY)
			break;

		ret = 0;
		ptr = btrfs_item_ptr_offset(leaf, path->slots[0]);
		extref = (struct btrfs_inode_extref *)ptr;
		*ret_extref = extref;
		if (found_off)
			*found_off = found_key.offset;
		break;
	}

	return ret;
}
			struct extent_buffer *eb_in, u64 parent,
			char *dest, u32 size)
{
	int slot;
	u64 next_inum;
	int ret;
	s64 bytes_left = ((s64)size) - 1;
	struct extent_buffer *eb = eb_in;
	struct btrfs_key found_key;
	int leave_spinning = path->leave_spinning;
	struct btrfs_inode_ref *iref;

	if (bytes_left >= 0)
		dest[bytes_left] = '\0';

	path->leave_spinning = 1;
	while (1) {
		bytes_left -= name_len;
		if (bytes_left >= 0)
			read_extent_buffer(eb, dest + bytes_left,
					   name_off, name_len);
		if (eb != eb_in) {
			if (!path->skip_locking)
				btrfs_tree_read_unlock_blocking(eb);
			free_extent_buffer(eb);
		}
		ret = btrfs_find_item(fs_root, path, parent, 0,
				BTRFS_INODE_REF_KEY, &found_key);
		if (ret > 0)
			ret = -ENOENT;
		if (ret)
			break;

		next_inum = found_key.offset;

		/* regular exit ahead */
		if (parent == next_inum)
			break;

		slot = path->slots[0];
		eb = path->nodes[0];
		/* make sure we can use eb after releasing the path */
		if (eb != eb_in) {
			if (!path->skip_locking)
				btrfs_set_lock_blocking_rw(eb, BTRFS_READ_LOCK);
			path->nodes[0] = NULL;
			path->locks[0] = 0;
		}
		btrfs_release_path(path);
		iref = btrfs_item_ptr(eb, slot, struct btrfs_inode_ref);

		name_len = btrfs_inode_ref_name_len(eb, iref);
		name_off = (unsigned long)(iref + 1);

		parent = next_inum;
		--bytes_left;
		if (bytes_left >= 0)
			dest[bytes_left] = '/';
	}

	btrfs_release_path(path);
	path->leave_spinning = leave_spinning;

	if (ret)
		return ERR_PTR(ret);

	return dest + bytes_left;
}
			    struct btrfs_key *key, struct btrfs_extent_item *ei,
			    u32 item_size, u64 *out_root, u8 *out_level)
{
	int ret;
	int type;
	struct btrfs_extent_inline_ref *eiref;

	if (*ptr == (unsigned long)-1)
		return 1;

	while (1) {
		ret = __get_extent_inline_ref(ptr, eb, key, ei, item_size,
					      &eiref, &type);
		if (ret < 0)
			return ret;

		if (type == BTRFS_TREE_BLOCK_REF_KEY ||
		    type == BTRFS_SHARED_BLOCK_REF_KEY)
			break;

		if (ret == 1)
			return 1;
	}

	/* we can treat both ref types equally here */
	*out_root = btrfs_extent_inline_ref_offset(eb, eiref);

	if (key->type == BTRFS_EXTENT_ITEM_KEY) {
		struct btrfs_tree_block_info *info;

		info = (struct btrfs_tree_block_info *)(ei + 1);
		*out_level = btrfs_tree_block_level(eb, info);
	} else {
		ASSERT(key->type == BTRFS_METADATA_ITEM_KEY);
		*out_level = (u8)key->offset;
	}

	if (ret == 1)
		*ptr = (unsigned long)-1;

	return 0;
}
			     u64 root, u64 extent_item_objectid,
			     iterate_extent_inodes_t *iterate, void *ctx)
{
	struct extent_inode_elem *eie;
	int ret = 0;

	for (eie = inode_list; eie; eie = eie->next) {
		btrfs_debug(fs_info,
			    "ref for %llu resolved, key (%llu EXTEND_DATA %llu), root %llu",
			    extent_item_objectid, eie->inum,
			    eie->offset, root);
		ret = iterate(eie->inum, eie->offset, root, ctx);
		if (ret) {
			btrfs_debug(fs_info,
				    "stopping iteration for %llu due to ret=%d",
				    extent_item_objectid, ret);
			break;
		}
	}

	return ret;
}
				int search_commit_root,
				iterate_extent_inodes_t *iterate, void *ctx)
{
	int ret;
	struct btrfs_trans_handle *trans = NULL;
	struct ulist *refs = NULL;
	struct ulist *roots = NULL;
	struct ulist_node *ref_node = NULL;
	struct ulist_node *root_node = NULL;
	struct seq_list tree_mod_seq_elem = SEQ_LIST_INIT(tree_mod_seq_elem);
	struct ulist_iterator ref_uiter;
	struct ulist_iterator root_uiter;

	btrfs_debug(fs_info, "resolving all inodes for extent %llu",
			extent_item_objectid);

	if (!search_commit_root) {
		trans = btrfs_join_transaction(fs_info->extent_root);
		if (IS_ERR(trans))
			return PTR_ERR(trans);
		btrfs_get_tree_mod_seq(fs_info, &tree_mod_seq_elem);
	} else {
		down_read(&fs_info->commit_root_sem);
	}

	ret = btrfs_find_all_leafs(trans, fs_info, extent_item_objectid,
				   tree_mod_seq_elem.seq, &refs,
				   &extent_item_pos);
	if (ret)
		goto out;

	ULIST_ITER_INIT(&ref_uiter);
	while (!ret && (ref_node = ulist_next(refs, &ref_uiter))) {
		ret = __btrfs_find_all_roots(trans, fs_info, ref_node->val,
					     tree_mod_seq_elem.seq, &roots);
		if (ret)
			break;
		ULIST_ITER_INIT(&root_uiter);
		while (!ret && (root_node = ulist_next(roots, &root_uiter))) {
			btrfs_debug(fs_info,
				    "root %llu references leaf %llu, data list %#llx",
				    root_node->val, ref_node->val,
				    ref_node->aux);
			ret = iterate_leaf_refs(fs_info,
						(struct extent_inode_elem *)
						(uintptr_t)ref_node->aux,
						root_node->val,
						extent_item_objectid,
						iterate, ctx);
		}
		ulist_free(roots);
	}

	free_leaf_list(refs);
out:
	if (!search_commit_root) {
		btrfs_put_tree_mod_seq(fs_info, &tree_mod_seq_elem);
		btrfs_end_transaction(trans);
	} else {
		up_read(&fs_info->commit_root_sem);
	}

	return ret;
}
			      struct btrfs_path *path,
			      iterate_irefs_t *iterate, void *ctx)
{
	int ret = 0;
	int slot;
	u32 cur;
	u32 len;
	u32 name_len;
	u64 parent = 0;
	int found = 0;
	struct extent_buffer *eb;
	struct btrfs_item *item;
	struct btrfs_inode_ref *iref;
	struct btrfs_key found_key;

	while (!ret) {
		ret = btrfs_find_item(fs_root, path, inum,
				parent ? parent + 1 : 0, BTRFS_INODE_REF_KEY,
				&found_key);

		if (ret < 0)
			break;
		if (ret) {
			ret = found ? 0 : -ENOENT;
			break;
		}
		++found;

		parent = found_key.offset;
		slot = path->slots[0];
		eb = btrfs_clone_extent_buffer(path->nodes[0]);
		if (!eb) {
			ret = -ENOMEM;
			break;
		}
		extent_buffer_get(eb);
		btrfs_tree_read_lock(eb);
		btrfs_set_lock_blocking_rw(eb, BTRFS_READ_LOCK);
		btrfs_release_path(path);

		item = btrfs_item_nr(slot);
		iref = btrfs_item_ptr(eb, slot, struct btrfs_inode_ref);

		for (cur = 0; cur < btrfs_item_size(eb, item); cur += len) {
			name_len = btrfs_inode_ref_name_len(eb, iref);
			/* path must be released before calling iterate()! */
			btrfs_debug(fs_root->fs_info,
				"following ref at offset %u for inode %llu in tree %llu",
				cur, found_key.objectid, fs_root->objectid);
			ret = iterate(parent, name_len,
				      (unsigned long)(iref + 1), eb, ctx);
			if (ret)
				break;
			len = sizeof(*iref) + name_len;
			iref = (struct btrfs_inode_ref *)((char *)iref + len);
		}
		btrfs_tree_read_unlock_blocking(eb);
		free_extent_buffer(eb);
	}

	btrfs_release_path(path);

	return ret;
}
				 struct btrfs_path *path,
				 iterate_irefs_t *iterate, void *ctx)
{
	int ret;
	int slot;
	u64 offset = 0;
	u64 parent;
	int found = 0;
	struct extent_buffer *eb;
	struct btrfs_inode_extref *extref;
	u32 item_size;
	u32 cur_offset;
	unsigned long ptr;

	while (1) {
		ret = btrfs_find_one_extref(fs_root, inum, offset, path, &extref,
					    &offset);
		if (ret < 0)
			break;
		if (ret) {
			ret = found ? 0 : -ENOENT;
			break;
		}
		++found;

		slot = path->slots[0];
		eb = btrfs_clone_extent_buffer(path->nodes[0]);
		if (!eb) {
			ret = -ENOMEM;
			break;
		}
		extent_buffer_get(eb);

		btrfs_tree_read_lock(eb);
		btrfs_set_lock_blocking_rw(eb, BTRFS_READ_LOCK);
		btrfs_release_path(path);

		item_size = btrfs_item_size_nr(eb, slot);
		ptr = btrfs_item_ptr_offset(eb, slot);
		cur_offset = 0;

		while (cur_offset < item_size) {
			u32 name_len;

			extref = (struct btrfs_inode_extref *)(ptr + cur_offset);
			parent = btrfs_inode_extref_parent(eb, extref);
			name_len = btrfs_inode_extref_name_len(eb, extref);
			ret = iterate(parent, name_len,
				      (unsigned long)&extref->name, eb, ctx);
			if (ret)
				break;

			cur_offset += btrfs_inode_extref_name_len(eb, extref);
			cur_offset += sizeof(*extref);
		}
		btrfs_tree_read_unlock_blocking(eb);
		free_extent_buffer(eb);

		offset++;
	}

	btrfs_release_path(path);

	return ret;
}
