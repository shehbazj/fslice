static struct btrfs_qgroup *find_qgroup_rb(struct btrfs_fs_info *fs_info,
					   u64 qgroupid)
{
	struct rb_node *n = fs_info->qgroup_tree.rb_node;
	struct btrfs_qgroup *qgroup;

	while (n) {
		qgroup = rb_entry(n, struct btrfs_qgroup, node);
		if (qgroup->qgroupid < qgroupid)
			n = n->rb_left;
		else if (qgroup->qgroupid > qgroupid)
			n = n->rb_right;
		else
			return qgroup;
	}
	return NULL;
}
static struct btrfs_qgroup *add_qgroup_rb(struct btrfs_fs_info *fs_info,
					  u64 qgroupid)
{
	struct rb_node **p = &fs_info->qgroup_tree.rb_node;
	struct rb_node *parent = NULL;
	struct btrfs_qgroup *qgroup;

	while (*p) {
		parent = *p;
		qgroup = rb_entry(parent, struct btrfs_qgroup, node);

		if (qgroup->qgroupid < qgroupid)
			p = &(*p)->rb_left;
		else if (qgroup->qgroupid > qgroupid)
			p = &(*p)->rb_right;
		else
			return qgroup;
	}

	qgroup = kzalloc(sizeof(*qgroup), GFP_ATOMIC);
	if (!qgroup)
		return ERR_PTR(-ENOMEM);

	qgroup->qgroupid = qgroupid;
	INIT_LIST_HEAD(&qgroup->groups);
	INIT_LIST_HEAD(&qgroup->members);
	INIT_LIST_HEAD(&qgroup->dirty);

	rb_link_node(&qgroup->node, parent, p);
	rb_insert_color(&qgroup->node, &fs_info->qgroup_tree);

	return qgroup;
}

static void __del_qgroup_rb(struct btrfs_qgroup *qgroup)
{
	struct btrfs_qgroup_list *list;

	list_del(&qgroup->dirty);
	while (!list_empty(&qgroup->groups)) {
		list = list_first_entry(&qgroup->groups,
					struct btrfs_qgroup_list, next_group);
		list_del(&list->next_group);
		list_del(&list->next_member);
		kfree(list);
	}

	while (!list_empty(&qgroup->members)) {
		list = list_first_entry(&qgroup->members,
					struct btrfs_qgroup_list, next_member);
		list_del(&list->next_group);
		list_del(&list->next_member);
		kfree(list);
	}
	kfree(qgroup);
}
 */
int btrfs_read_qgroup_config(struct btrfs_fs_info *fs_info)
{
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_root *quota_root = fs_info->quota_root;
	struct btrfs_path *path = NULL;
	struct extent_buffer *l;
	int slot;
	int ret = 0;
	u64 flags = 0;
	u64 rescan_progress = 0;

	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags))
		return 0;

	fs_info->qgroup_ulist = ulist_alloc(GFP_KERNEL);
	if (!fs_info->qgroup_ulist) {
		ret = -ENOMEM;
		goto out;
	}

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	/* default this to quota off, in case no status key is found */
	fs_info->qgroup_flags = 0;

	/*
	 * pass 1: read status, all qgroup infos and limits
	 */
	key.objectid = 0;
	key.type = 0;
	key.offset = 0;
	ret = btrfs_search_slot_for_read(quota_root, &key, path, 1, 1);
	if (ret)
		goto out;

	while (1) {
		struct btrfs_qgroup *qgroup;

		slot = path->slots[0];
		l = path->nodes[0];
		btrfs_item_key_to_cpu(l, &found_key, slot);

		if (found_key.type == BTRFS_QGROUP_STATUS_KEY) {
			struct btrfs_qgroup_status_item *ptr;

			ptr = btrfs_item_ptr(l, slot,
					     struct btrfs_qgroup_status_item);

			if (btrfs_qgroup_status_version(l, ptr) !=
			    BTRFS_QGROUP_STATUS_VERSION) {
				btrfs_err(fs_info,
				 "old qgroup version, quota disabled");
				goto out;
			}
			if (btrfs_qgroup_status_generation(l, ptr) !=
			    fs_info->generation) {
				flags |= BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
				btrfs_err(fs_info,
					"qgroup generation mismatch, marked as inconsistent");
			}
			fs_info->qgroup_flags = btrfs_qgroup_status_flags(l,
									  ptr);
			rescan_progress = btrfs_qgroup_status_rescan(l, ptr);
			goto next1;
		}

		if (found_key.type != BTRFS_QGROUP_INFO_KEY &&
		    found_key.type != BTRFS_QGROUP_LIMIT_KEY)
			goto next1;

		qgroup = find_qgroup_rb(fs_info, found_key.offset);
		if ((qgroup && found_key.type == BTRFS_QGROUP_INFO_KEY) ||
		    (!qgroup && found_key.type == BTRFS_QGROUP_LIMIT_KEY)) {
			btrfs_err(fs_info, "inconsistent qgroup config");
			flags |= BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
		}
		if (!qgroup) {
			qgroup = add_qgroup_rb(fs_info, found_key.offset);
			if (IS_ERR(qgroup)) {
				ret = PTR_ERR(qgroup);
				goto out;
			}
		}
		switch (found_key.type) {
		case BTRFS_QGROUP_INFO_KEY: {
			struct btrfs_qgroup_info_item *ptr;

			ptr = btrfs_item_ptr(l, slot,
					     struct btrfs_qgroup_info_item);
			qgroup->rfer = btrfs_qgroup_info_rfer(l, ptr);
			qgroup->rfer_cmpr = btrfs_qgroup_info_rfer_cmpr(l, ptr);
			qgroup->excl = btrfs_qgroup_info_excl(l, ptr);
			qgroup->excl_cmpr = btrfs_qgroup_info_excl_cmpr(l, ptr);
			/* generation currently unused */
			break;
		}
		case BTRFS_QGROUP_LIMIT_KEY: {
			struct btrfs_qgroup_limit_item *ptr;

			ptr = btrfs_item_ptr(l, slot,
					     struct btrfs_qgroup_limit_item);
			qgroup->lim_flags = btrfs_qgroup_limit_flags(l, ptr);
			qgroup->max_rfer = btrfs_qgroup_limit_max_rfer(l, ptr);
			qgroup->max_excl = btrfs_qgroup_limit_max_excl(l, ptr);
			qgroup->rsv_rfer = btrfs_qgroup_limit_rsv_rfer(l, ptr);
			qgroup->rsv_excl = btrfs_qgroup_limit_rsv_excl(l, ptr);
			break;
		}
		}
next1:
		ret = btrfs_next_item(quota_root, path);
		if (ret < 0)
			goto out;
		if (ret)
			break;
	}
	btrfs_release_path(path);

	/*
	 * pass 2: read all qgroup relations
	 */
	key.objectid = 0;
	key.type = BTRFS_QGROUP_RELATION_KEY;
	key.offset = 0;
	ret = btrfs_search_slot_for_read(quota_root, &key, path, 1, 0);
	if (ret)
		goto out;
	while (1) {
		slot = path->slots[0];
		l = path->nodes[0];
		btrfs_item_key_to_cpu(l, &found_key, slot);

		if (found_key.type != BTRFS_QGROUP_RELATION_KEY)
			goto next2;

		if (found_key.objectid > found_key.offset) {
			/* parent <- member, not needed to build config */
			/* FIXME should we omit the key completely? */
			goto next2;
		}

		ret = add_relation_rb(fs_info, found_key.objectid,
				      found_key.offset);
		if (ret == -ENOENT) {
			btrfs_warn(fs_info,
				"orphan qgroup relation 0x%llx->0x%llx",
				found_key.objectid, found_key.offset);
			ret = 0;	/* ignore the error */
		}
		if (ret)
			goto out;
next2:
		ret = btrfs_next_item(quota_root, path);
		if (ret < 0)
			goto out;
		if (ret)
			break;
	}
out:
	fs_info->qgroup_flags |= flags;
	if (!(fs_info->qgroup_flags & BTRFS_QGROUP_STATUS_FLAG_ON))
		clear_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags);
	else if (fs_info->qgroup_flags & BTRFS_QGROUP_STATUS_FLAG_RESCAN &&
		 ret >= 0)
		ret = qgroup_rescan_init(fs_info, rescan_progress, 0);
	btrfs_free_path(path);

	if (ret < 0) {
		ulist_free(fs_info->qgroup_ulist);
		fs_info->qgroup_ulist = NULL;
		fs_info->qgroup_flags &= ~BTRFS_QGROUP_STATUS_FLAG_RESCAN;
	}

	return ret < 0 ? ret : 0;
}
 */
void btrfs_free_qgroup_config(struct btrfs_fs_info *fs_info)
{
	struct rb_node *n;
	struct btrfs_qgroup *qgroup;

	while ((n = rb_first(&fs_info->qgroup_tree))) {
		qgroup = rb_entry(n, struct btrfs_qgroup, node);
		rb_erase(n, &fs_info->qgroup_tree);
		__del_qgroup_rb(qgroup);
	}
	/*
	 * we call btrfs_free_qgroup_config() when umounting
	 * filesystem and disabling quota, so we set qgroup_ulist
	 * to be null here to avoid double free.
	 */
	ulist_free(fs_info->qgroup_ulist);
	fs_info->qgroup_ulist = NULL;
}
static int btrfs_clean_quota_tree(struct btrfs_trans_handle *trans,
				  struct btrfs_root *root)
{
	struct btrfs_path *path;
	struct btrfs_key key;
	struct extent_buffer *leaf = NULL;
	int ret;
	int nr = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->leave_spinning = 1;

	key.objectid = 0;
	key.offset = 0;
	key.type = 0;

	while (1) {
		ret = btrfs_search_slot(trans, root, &key, path, -1, 1);
		if (ret < 0)
			goto out;
		leaf = path->nodes[0];
		nr = btrfs_header_nritems(leaf);
		if (!nr)
			break;
		/*
		 * delete the leaf one by one
		 * since the whole tree is going
		 * to be deleted.
		 */
		path->slots[0] = 0;
		ret = btrfs_del_items(trans, root, path, 0, nr);
		if (ret)
			goto out;

		btrfs_release_path(path);
	}
	ret = 0;
out:
	set_bit(BTRFS_FS_QUOTA_DISABLING, &root->fs_info->flags);
	btrfs_free_path(path);
	return ret;
}
int btrfs_quota_enable(struct btrfs_trans_handle *trans,
		       struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *quota_root;
	struct btrfs_root *tree_root = fs_info->tree_root;
	struct btrfs_path *path = NULL;
	struct btrfs_qgroup_status_item *ptr;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_qgroup *qgroup = NULL;
	int ret = 0;
	int slot;

	mutex_lock(&fs_info->qgroup_ioctl_lock);
	if (fs_info->quota_root) {
		set_bit(BTRFS_FS_QUOTA_ENABLING, &fs_info->flags);
		goto out;
	}

	fs_info->qgroup_ulist = ulist_alloc(GFP_KERNEL);
	if (!fs_info->qgroup_ulist) {
		ret = -ENOMEM;
		goto out;
	}

	/*
	 * initially create the quota tree
	 */
	quota_root = btrfs_create_tree(trans, fs_info,
				       BTRFS_QUOTA_TREE_OBJECTID);
	if (IS_ERR(quota_root)) {
		ret =  PTR_ERR(quota_root);
		goto out;
	}

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out_free_root;
	}

	key.objectid = 0;
	key.type = BTRFS_QGROUP_STATUS_KEY;
	key.offset = 0;

	ret = btrfs_insert_empty_item(trans, quota_root, path, &key,
				      sizeof(*ptr));
	if (ret)
		goto out_free_path;

	leaf = path->nodes[0];
	ptr = btrfs_item_ptr(leaf, path->slots[0],
				 struct btrfs_qgroup_status_item);
	btrfs_set_qgroup_status_generation(leaf, ptr, trans->transid);
	btrfs_set_qgroup_status_version(leaf, ptr, BTRFS_QGROUP_STATUS_VERSION);
	fs_info->qgroup_flags = BTRFS_QGROUP_STATUS_FLAG_ON |
				BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
	btrfs_set_qgroup_status_flags(leaf, ptr, fs_info->qgroup_flags);
	btrfs_set_qgroup_status_rescan(leaf, ptr, 0);

	btrfs_mark_buffer_dirty(leaf);

	key.objectid = 0;
	key.type = BTRFS_ROOT_REF_KEY;
	key.offset = 0;

	btrfs_release_path(path);
	ret = btrfs_search_slot_for_read(tree_root, &key, path, 1, 0);
	if (ret > 0)
		goto out_add_root;
	if (ret < 0)
		goto out_free_path;


	while (1) {
		slot = path->slots[0];
		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		if (found_key.type == BTRFS_ROOT_REF_KEY) {
			ret = add_qgroup_item(trans, quota_root,
					      found_key.offset);
			if (ret)
				goto out_free_path;

			qgroup = add_qgroup_rb(fs_info, found_key.offset);
			if (IS_ERR(qgroup)) {
				ret = PTR_ERR(qgroup);
				goto out_free_path;
			}
		}
		ret = btrfs_next_item(tree_root, path);
		if (ret < 0)
			goto out_free_path;
		if (ret)
			break;
	}

out_add_root:
	btrfs_release_path(path);
	ret = add_qgroup_item(trans, quota_root, BTRFS_FS_TREE_OBJECTID);
	if (ret)
		goto out_free_path;

	qgroup = add_qgroup_rb(fs_info, BTRFS_FS_TREE_OBJECTID);
	if (IS_ERR(qgroup)) {
		ret = PTR_ERR(qgroup);
		goto out_free_path;
	}
	spin_lock(&fs_info->qgroup_lock);
	fs_info->quota_root = quota_root;
	set_bit(BTRFS_FS_QUOTA_ENABLING, &fs_info->flags);
	spin_unlock(&fs_info->qgroup_lock);
out_free_path:
	btrfs_free_path(path);
out_free_root:
	if (ret) {
		free_extent_buffer(quota_root->node);
		free_extent_buffer(quota_root->commit_root);
		kfree(quota_root);
	}
out:
	if (ret) {
		ulist_free(fs_info->qgroup_ulist);
		fs_info->qgroup_ulist = NULL;
	}
	mutex_unlock(&fs_info->qgroup_ioctl_lock);
	return ret;
}
				    struct ulist *tmp, u64 ref_root,
				    u64 num_bytes, int sign)
{
	struct btrfs_qgroup *qgroup;
	struct btrfs_qgroup_list *glist;
	struct ulist_node *unode;
	struct ulist_iterator uiter;
	int ret = 0;

	qgroup = find_qgroup_rb(fs_info, ref_root);
	if (!qgroup)
		goto out;

	qgroup->rfer += sign * num_bytes;
	qgroup->rfer_cmpr += sign * num_bytes;

	WARN_ON(sign < 0 && qgroup->excl < num_bytes);
	qgroup->excl += sign * num_bytes;
	qgroup->excl_cmpr += sign * num_bytes;
	if (sign > 0) {
		trace_qgroup_update_reserve(fs_info, qgroup, -(s64)num_bytes);
		if (qgroup->reserved < num_bytes)
			report_reserved_underflow(fs_info, qgroup, num_bytes);
		else
			qgroup->reserved -= num_bytes;
	}

	qgroup_dirty(fs_info, qgroup);

	/* Get all of the parent groups that contain this qgroup */
	list_for_each_entry(glist, &qgroup->groups, next_group) {
		ret = ulist_add(tmp, glist->group->qgroupid,
				qgroup_to_aux(glist->group), GFP_ATOMIC);
		if (ret < 0)
			goto out;
	}

	/* Iterate all of the parents and adjust their reference counts */
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(tmp, &uiter))) {
		qgroup = unode_aux_to_qgroup(unode);
		qgroup->rfer += sign * num_bytes;
		qgroup->rfer_cmpr += sign * num_bytes;
		WARN_ON(sign < 0 && qgroup->excl < num_bytes);
		qgroup->excl += sign * num_bytes;
		if (sign > 0) {
			trace_qgroup_update_reserve(fs_info, qgroup,
						    -(s64)num_bytes);
			if (qgroup->reserved < num_bytes)
				report_reserved_underflow(fs_info, qgroup,
							  num_bytes);
			else
				qgroup->reserved -= num_bytes;
		}
		qgroup->excl_cmpr += sign * num_bytes;
		qgroup_dirty(fs_info, qgroup);

		/* Add any parents of the parents */
		list_for_each_entry(glist, &qgroup->groups, next_group) {
			ret = ulist_add(tmp, glist->group->qgroupid,
					qgroup_to_aux(glist->group), GFP_ATOMIC);
			if (ret < 0)
				goto out;
		}
	}
	ret = 0;
out:
	return ret;
}
int btrfs_remove_qgroup(struct btrfs_trans_handle *trans,
			struct btrfs_fs_info *fs_info, u64 qgroupid)
{
	struct btrfs_root *quota_root;
	struct btrfs_qgroup *qgroup;
	struct btrfs_qgroup_list *list;
	int ret = 0;

	mutex_lock(&fs_info->qgroup_ioctl_lock);
	quota_root = fs_info->quota_root;
	if (!quota_root) {
		ret = -EINVAL;
		goto out;
	}

	qgroup = find_qgroup_rb(fs_info, qgroupid);
	if (!qgroup) {
		ret = -ENOENT;
		goto out;
	} else {
		/* check if there are no children of this qgroup */
		if (!list_empty(&qgroup->members)) {
			ret = -EBUSY;
			goto out;
		}
	}
	ret = del_qgroup_item(trans, quota_root, qgroupid);

	while (!list_empty(&qgroup->groups)) {
		list = list_first_entry(&qgroup->groups,
					struct btrfs_qgroup_list, next_group);
		ret = __del_qgroup_relation(trans, fs_info,
					   qgroupid,
					   list->group->qgroupid);
		if (ret)
			goto out;
	}

	spin_lock(&fs_info->qgroup_lock);
	del_qgroup_rb(fs_info, qgroupid);
	spin_unlock(&fs_info->qgroup_lock);
out:
	mutex_unlock(&fs_info->qgroup_ioctl_lock);
	return ret;
}
int btrfs_qgroup_prepare_account_extents(struct btrfs_trans_handle *trans,
					 struct btrfs_fs_info *fs_info)
{
	struct btrfs_qgroup_extent_record *record;
	struct btrfs_delayed_ref_root *delayed_refs;
	struct rb_node *node;
	u64 qgroup_to_skip;
	int ret = 0;

	delayed_refs = &trans->transaction->delayed_refs;
	qgroup_to_skip = delayed_refs->qgroup_to_skip;

	/*
	 * No need to do lock, since this function will only be called in
	 * btrfs_commit_transaction().
	 */
	node = rb_first(&delayed_refs->dirty_extent_root);
	while (node) {
		record = rb_entry(node, struct btrfs_qgroup_extent_record,
				  node);
		if (WARN_ON(!record->old_roots))
			ret = btrfs_find_all_roots(NULL, fs_info,
					record->bytenr, 0, &record->old_roots);
		if (ret < 0)
			break;
		if (qgroup_to_skip)
			ulist_del(record->old_roots, qgroup_to_skip, 0);
		node = rb_next(node);
	}
	return ret;
}
				struct btrfs_delayed_ref_root *delayed_refs,
				struct btrfs_qgroup_extent_record *record)
{
	struct rb_node **p = &delayed_refs->dirty_extent_root.rb_node;
	struct rb_node *parent_node = NULL;
	struct btrfs_qgroup_extent_record *entry;
	u64 bytenr = record->bytenr;

	assert_spin_locked(&delayed_refs->lock);
	trace_btrfs_qgroup_trace_extent(fs_info, record);

	while (*p) {
		parent_node = *p;
		entry = rb_entry(parent_node, struct btrfs_qgroup_extent_record,
				 node);
		if (bytenr < entry->bytenr)
			p = &(*p)->rb_left;
		else if (bytenr > entry->bytenr)
			p = &(*p)->rb_right;
		else
			return 1;
	}

	rb_link_node(&record->node, parent_node, p);
	rb_insert_color(&record->node, &delayed_refs->dirty_extent_root);
	return 0;
}
				  struct btrfs_fs_info *fs_info,
				  struct extent_buffer *eb)
{
	int nr = btrfs_header_nritems(eb);
	int i, extent_type, ret;
	struct btrfs_key key;
	struct btrfs_file_extent_item *fi;
	u64 bytenr, num_bytes;

	/* We can be called directly from walk_up_proc() */
	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags))
		return 0;

	for (i = 0; i < nr; i++) {
		btrfs_item_key_to_cpu(eb, &key, i);

		if (key.type != BTRFS_EXTENT_DATA_KEY)
			continue;

		fi = btrfs_item_ptr(eb, i, struct btrfs_file_extent_item);
		/* filter out non qgroup-accountable extents  */
		extent_type = btrfs_file_extent_type(eb, fi);

		if (extent_type == BTRFS_FILE_EXTENT_INLINE)
			continue;

		bytenr = btrfs_file_extent_disk_bytenr(eb, fi);
		if (!bytenr)
			continue;

		num_bytes = btrfs_file_extent_disk_num_bytes(eb, fi);

		ret = btrfs_qgroup_trace_extent(trans, fs_info, bytenr,
						num_bytes, GFP_NOFS);
		if (ret)
			return ret;
	}
	return 0;
}
 */
static int adjust_slots_upwards(struct btrfs_path *path, int root_level)
{
	int level = 0;
	int nr, slot;
	struct extent_buffer *eb;

	if (root_level == 0)
		return 1;

	while (level <= root_level) {
		eb = path->nodes[level];
		nr = btrfs_header_nritems(eb);
		path->slots[level]++;
		slot = path->slots[level];
		if (slot >= nr || level == 0) {
			/*
			 * Don't free the root -  we will detect this
			 * condition after our loop and return a
			 * positive value for caller to stop walking the tree.
			 */
			if (level != root_level) {
				btrfs_tree_unlock_rw(eb, path->locks[level]);
				path->locks[level] = 0;

				free_extent_buffer(eb);
				path->nodes[level] = NULL;
				path->slots[level] = 0;
			}
		} else {
			/*
			 * We have a valid slot to walk back down
			 * from. Stop here so caller can process these
			 * new nodes.
			 */
			break;
		}

		level++;
	}

	eb = path->nodes[root_level];
	if (path->slots[root_level] >= btrfs_header_nritems(eb))
		return 1;

	return 0;
}
			       struct extent_buffer *root_eb,
			       u64 root_gen, int root_level)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	int ret = 0;
	int level;
	struct extent_buffer *eb = root_eb;
	struct btrfs_path *path = NULL;

	BUG_ON(root_level < 0 || root_level > BTRFS_MAX_LEVEL);
	BUG_ON(root_eb == NULL);

	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags))
		return 0;

	if (!extent_buffer_uptodate(root_eb)) {
		ret = btrfs_read_buffer(root_eb, root_gen);
		if (ret)
			goto out;
	}

	if (root_level == 0) {
		ret = btrfs_qgroup_trace_leaf_items(trans, fs_info, root_eb);
		goto out;
	}

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	/*
	 * Walk down the tree.  Missing extent blocks are filled in as
	 * we go. Metadata is accounted every time we read a new
	 * extent block.
	 *
	 * When we reach a leaf, we account for file extent items in it,
	 * walk back up the tree (adjusting slot pointers as we go)
	 * and restart the search process.
	 */
	extent_buffer_get(root_eb); /* For path */
	path->nodes[root_level] = root_eb;
	path->slots[root_level] = 0;
	path->locks[root_level] = 0; /* so release_path doesn't try to unlock */
walk_down:
	level = root_level;
	while (level >= 0) {
		if (path->nodes[level] == NULL) {
			int parent_slot;
			u64 child_gen;
			u64 child_bytenr;

			/*
			 * We need to get child blockptr/gen from parent before
			 * we can read it.
			  */
			eb = path->nodes[level + 1];
			parent_slot = path->slots[level + 1];
			child_bytenr = btrfs_node_blockptr(eb, parent_slot);
			child_gen = btrfs_node_ptr_generation(eb, parent_slot);

			eb = read_tree_block(fs_info, child_bytenr, child_gen);
			if (IS_ERR(eb)) {
				ret = PTR_ERR(eb);
				goto out;
			} else if (!extent_buffer_uptodate(eb)) {
				free_extent_buffer(eb);
				ret = -EIO;
				goto out;
			}

			path->nodes[level] = eb;
			path->slots[level] = 0;

			btrfs_tree_read_lock(eb);
			btrfs_set_lock_blocking_rw(eb, BTRFS_READ_LOCK);
			path->locks[level] = BTRFS_READ_LOCK_BLOCKING;

			ret = btrfs_qgroup_trace_extent(trans, fs_info,
							child_bytenr,
							fs_info->nodesize,
							GFP_NOFS);
			if (ret)
				goto out;
		}

		if (level == 0) {
			ret = btrfs_qgroup_trace_leaf_items(trans,fs_info,
							   path->nodes[level]);
			if (ret)
				goto out;

			/* Nonzero return here means we completed our search */
			ret = adjust_slots_upwards(path, root_level);
			if (ret)
				break;

			/* Restart search with new slots */
			goto walk_down;
		}

		level--;
	}

	ret = 0;
out:
	btrfs_free_path(path);

	return ret;
}
				struct ulist *roots, struct ulist *tmp,
				struct ulist *qgroups, u64 seq, int update_old)
{
	struct ulist_node *unode;
	struct ulist_iterator uiter;
	struct ulist_node *tmp_unode;
	struct ulist_iterator tmp_uiter;
	struct btrfs_qgroup *qg;
	int ret = 0;

	if (!roots)
		return 0;
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(roots, &uiter))) {
		qg = find_qgroup_rb(fs_info, unode->val);
		if (!qg)
			continue;

		ulist_reinit(tmp);
		ret = ulist_add(qgroups, qg->qgroupid, qgroup_to_aux(qg),
				GFP_ATOMIC);
		if (ret < 0)
			return ret;
		ret = ulist_add(tmp, qg->qgroupid, qgroup_to_aux(qg), GFP_ATOMIC);
		if (ret < 0)
			return ret;
		ULIST_ITER_INIT(&tmp_uiter);
		while ((tmp_unode = ulist_next(tmp, &tmp_uiter))) {
			struct btrfs_qgroup_list *glist;

			qg = unode_aux_to_qgroup(tmp_unode);
			if (update_old)
				btrfs_qgroup_update_old_refcnt(qg, seq, 1);
			else
				btrfs_qgroup_update_new_refcnt(qg, seq, 1);
			list_for_each_entry(glist, &qg->groups, next_group) {
				ret = ulist_add(qgroups, glist->group->qgroupid,
						qgroup_to_aux(glist->group),
						GFP_ATOMIC);
				if (ret < 0)
					return ret;
				ret = ulist_add(tmp, glist->group->qgroupid,
						qgroup_to_aux(glist->group),
						GFP_ATOMIC);
				if (ret < 0)
					return ret;
			}
		}
	}
	return 0;
}
				  u64 nr_new_roots,
				  u64 num_bytes, u64 seq)
{
	struct ulist_node *unode;
	struct ulist_iterator uiter;
	struct btrfs_qgroup *qg;
	u64 cur_new_count, cur_old_count;

	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(qgroups, &uiter))) {
		bool dirty = false;

		qg = unode_aux_to_qgroup(unode);
		cur_old_count = btrfs_qgroup_get_old_refcnt(qg, seq);
		cur_new_count = btrfs_qgroup_get_new_refcnt(qg, seq);

		trace_qgroup_update_counters(fs_info, qg->qgroupid,
					     cur_old_count, cur_new_count);

		/* Rfer update part */
		if (cur_old_count == 0 && cur_new_count > 0) {
			qg->rfer += num_bytes;
			qg->rfer_cmpr += num_bytes;
			dirty = true;
		}
		if (cur_old_count > 0 && cur_new_count == 0) {
			qg->rfer -= num_bytes;
			qg->rfer_cmpr -= num_bytes;
			dirty = true;
		}

		/* Excl update part */
		/* Exclusive/none -> shared case */
		if (cur_old_count == nr_old_roots &&
		    cur_new_count < nr_new_roots) {
			/* Exclusive -> shared */
			if (cur_old_count != 0) {
				qg->excl -= num_bytes;
				qg->excl_cmpr -= num_bytes;
				dirty = true;
			}
		}

		/* Shared -> exclusive/none case */
		if (cur_old_count < nr_old_roots &&
		    cur_new_count == nr_new_roots) {
			/* Shared->exclusive */
			if (cur_new_count != 0) {
				qg->excl += num_bytes;
				qg->excl_cmpr += num_bytes;
				dirty = true;
			}
		}

		/* Exclusive/none -> exclusive/none case */
		if (cur_old_count == nr_old_roots &&
		    cur_new_count == nr_new_roots) {
			if (cur_old_count == 0) {
				/* None -> exclusive/none */

				if (cur_new_count != 0) {
					/* None -> exclusive */
					qg->excl += num_bytes;
					qg->excl_cmpr += num_bytes;
					dirty = true;
				}
				/* None -> none, nothing changed */
			} else {
				/* Exclusive -> exclusive/none */

				if (cur_new_count == 0) {
					/* Exclusive -> none */
					qg->excl -= num_bytes;
					qg->excl_cmpr -= num_bytes;
					dirty = true;
				}
				/* Exclusive -> exclusive, nothing changed */
			}
		}

		if (dirty)
			qgroup_dirty(fs_info, qg);
	}
	return 0;
}
int btrfs_qgroup_account_extents(struct btrfs_trans_handle *trans,
				 struct btrfs_fs_info *fs_info)
{
	struct btrfs_qgroup_extent_record *record;
	struct btrfs_delayed_ref_root *delayed_refs;
	struct ulist *new_roots = NULL;
	struct rb_node *node;
	u64 qgroup_to_skip;
	int ret = 0;

	delayed_refs = &trans->transaction->delayed_refs;
	qgroup_to_skip = delayed_refs->qgroup_to_skip;
	while ((node = rb_first(&delayed_refs->dirty_extent_root))) {
		record = rb_entry(node, struct btrfs_qgroup_extent_record,
				  node);

		trace_btrfs_qgroup_account_extents(fs_info, record);

		if (!ret) {
			/*
			 * Use SEQ_LAST as time_seq to do special search, which
			 * doesn't lock tree or delayed_refs and search current
			 * root. It's safe inside commit_transaction().
			 */
			ret = btrfs_find_all_roots(trans, fs_info,
					record->bytenr, SEQ_LAST, &new_roots);
			if (ret < 0)
				goto cleanup;
			if (qgroup_to_skip)
				ulist_del(new_roots, qgroup_to_skip, 0);
			ret = btrfs_qgroup_account_extent(trans, fs_info,
					record->bytenr, record->num_bytes,
					record->old_roots, new_roots);
			record->old_roots = NULL;
			new_roots = NULL;
		}
cleanup:
		ulist_free(record->old_roots);
		ulist_free(new_roots);
		new_roots = NULL;
		rb_erase(node, &delayed_refs->dirty_extent_root);
		kfree(record);

	}
	return ret;
}
int btrfs_run_qgroups(struct btrfs_trans_handle *trans,
		      struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *quota_root = fs_info->quota_root;
	int ret = 0;
	int start_rescan_worker = 0;

	if (!quota_root)
		goto out;

	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags) &&
	    test_bit(BTRFS_FS_QUOTA_ENABLING, &fs_info->flags))
		start_rescan_worker = 1;

	if (test_and_clear_bit(BTRFS_FS_QUOTA_ENABLING, &fs_info->flags))
		set_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags);
	if (test_and_clear_bit(BTRFS_FS_QUOTA_DISABLING, &fs_info->flags))
		clear_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags);

	spin_lock(&fs_info->qgroup_lock);
	while (!list_empty(&fs_info->dirty_qgroups)) {
		struct btrfs_qgroup *qgroup;
		qgroup = list_first_entry(&fs_info->dirty_qgroups,
					  struct btrfs_qgroup, dirty);
		list_del_init(&qgroup->dirty);
		spin_unlock(&fs_info->qgroup_lock);
		ret = update_qgroup_info_item(trans, quota_root, qgroup);
		if (ret)
			fs_info->qgroup_flags |=
					BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
		ret = update_qgroup_limit_item(trans, quota_root, qgroup);
		if (ret)
			fs_info->qgroup_flags |=
					BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
		spin_lock(&fs_info->qgroup_lock);
	}
	if (test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags))
		fs_info->qgroup_flags |= BTRFS_QGROUP_STATUS_FLAG_ON;
	else
		fs_info->qgroup_flags &= ~BTRFS_QGROUP_STATUS_FLAG_ON;
	spin_unlock(&fs_info->qgroup_lock);

	ret = update_qgroup_status_item(trans, fs_info, quota_root);
	if (ret)
		fs_info->qgroup_flags |= BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;

	if (!ret && start_rescan_worker) {
		ret = qgroup_rescan_init(fs_info, 0, 1);
		if (!ret) {
			qgroup_rescan_zero_tracking(fs_info);
			btrfs_queue_work(fs_info->qgroup_rescan_workers,
					 &fs_info->qgroup_rescan_work);
		}
		ret = 0;
	}

out:

	return ret;
}
			 struct btrfs_fs_info *fs_info, u64 srcid, u64 objectid,
			 struct btrfs_qgroup_inherit *inherit)
{
	int ret = 0;
	int i;
	u64 *i_qgroups;
	struct btrfs_root *quota_root = fs_info->quota_root;
	struct btrfs_qgroup *srcgroup;
	struct btrfs_qgroup *dstgroup;
	u32 level_size = 0;
	u64 nums;

	mutex_lock(&fs_info->qgroup_ioctl_lock);
	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags))
		goto out;

	if (!quota_root) {
		ret = -EINVAL;
		goto out;
	}

	if (inherit) {
		i_qgroups = (u64 *)(inherit + 1);
		nums = inherit->num_qgroups + 2 * inherit->num_ref_copies +
		       2 * inherit->num_excl_copies;
		for (i = 0; i < nums; ++i) {
			srcgroup = find_qgroup_rb(fs_info, *i_qgroups);

			/*
			 * Zero out invalid groups so we can ignore
			 * them later.
			 */
			if (!srcgroup ||
			    ((srcgroup->qgroupid >> 48) <= (objectid >> 48)))
				*i_qgroups = 0ULL;

			++i_qgroups;
		}
	}

	/*
	 * create a tracking group for the subvol itself
	 */
	ret = add_qgroup_item(trans, quota_root, objectid);
	if (ret)
		goto out;

	if (srcid) {
		struct btrfs_root *srcroot;
		struct btrfs_key srckey;

		srckey.objectid = srcid;
		srckey.type = BTRFS_ROOT_ITEM_KEY;
		srckey.offset = (u64)-1;
		srcroot = btrfs_read_fs_root_no_name(fs_info, &srckey);
		if (IS_ERR(srcroot)) {
			ret = PTR_ERR(srcroot);
			goto out;
		}

		level_size = fs_info->nodesize;
	}

	/*
	 * add qgroup to all inherited groups
	 */
	if (inherit) {
		i_qgroups = (u64 *)(inherit + 1);
		for (i = 0; i < inherit->num_qgroups; ++i, ++i_qgroups) {
			if (*i_qgroups == 0)
				continue;
			ret = add_qgroup_relation_item(trans, quota_root,
						       objectid, *i_qgroups);
			if (ret && ret != -EEXIST)
				goto out;
			ret = add_qgroup_relation_item(trans, quota_root,
						       *i_qgroups, objectid);
			if (ret && ret != -EEXIST)
				goto out;
		}
		ret = 0;
	}


	spin_lock(&fs_info->qgroup_lock);

	dstgroup = add_qgroup_rb(fs_info, objectid);
	if (IS_ERR(dstgroup)) {
		ret = PTR_ERR(dstgroup);
		goto unlock;
	}

	if (inherit && inherit->flags & BTRFS_QGROUP_INHERIT_SET_LIMITS) {
		dstgroup->lim_flags = inherit->lim.flags;
		dstgroup->max_rfer = inherit->lim.max_rfer;
		dstgroup->max_excl = inherit->lim.max_excl;
		dstgroup->rsv_rfer = inherit->lim.rsv_rfer;
		dstgroup->rsv_excl = inherit->lim.rsv_excl;

		ret = update_qgroup_limit_item(trans, quota_root, dstgroup);
		if (ret) {
			fs_info->qgroup_flags |= BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
			btrfs_info(fs_info,
				   "unable to update quota limit for %llu",
				   dstgroup->qgroupid);
			goto unlock;
		}
	}

	if (srcid) {
		srcgroup = find_qgroup_rb(fs_info, srcid);
		if (!srcgroup)
			goto unlock;

		/*
		 * We call inherit after we clone the root in order to make sure
		 * our counts don't go crazy, so at this point the only
		 * difference between the two roots should be the root node.
		 */
		dstgroup->rfer = srcgroup->rfer;
		dstgroup->rfer_cmpr = srcgroup->rfer_cmpr;
		dstgroup->excl = level_size;
		dstgroup->excl_cmpr = level_size;
		srcgroup->excl = level_size;
		srcgroup->excl_cmpr = level_size;

		/* inherit the limit info */
		dstgroup->lim_flags = srcgroup->lim_flags;
		dstgroup->max_rfer = srcgroup->max_rfer;
		dstgroup->max_excl = srcgroup->max_excl;
		dstgroup->rsv_rfer = srcgroup->rsv_rfer;
		dstgroup->rsv_excl = srcgroup->rsv_excl;

		qgroup_dirty(fs_info, dstgroup);
		qgroup_dirty(fs_info, srcgroup);
	}

	if (!inherit)
		goto unlock;

	i_qgroups = (u64 *)(inherit + 1);
	for (i = 0; i < inherit->num_qgroups; ++i) {
		if (*i_qgroups) {
			ret = add_relation_rb(fs_info, objectid, *i_qgroups);
			if (ret)
				goto unlock;
		}
		++i_qgroups;
	}

	for (i = 0; i <  inherit->num_ref_copies; ++i, i_qgroups += 2) {
		struct btrfs_qgroup *src;
		struct btrfs_qgroup *dst;

		if (!i_qgroups[0] || !i_qgroups[1])
			continue;

		src = find_qgroup_rb(fs_info, i_qgroups[0]);
		dst = find_qgroup_rb(fs_info, i_qgroups[1]);

		if (!src || !dst) {
			ret = -EINVAL;
			goto unlock;
		}

		dst->rfer = src->rfer - level_size;
		dst->rfer_cmpr = src->rfer_cmpr - level_size;
	}
	for (i = 0; i <  inherit->num_excl_copies; ++i, i_qgroups += 2) {
		struct btrfs_qgroup *src;
		struct btrfs_qgroup *dst;

		if (!i_qgroups[0] || !i_qgroups[1])
			continue;

		src = find_qgroup_rb(fs_info, i_qgroups[0]);
		dst = find_qgroup_rb(fs_info, i_qgroups[1]);

		if (!src || !dst) {
			ret = -EINVAL;
			goto unlock;
		}

		dst->excl = src->excl + level_size;
		dst->excl_cmpr = src->excl_cmpr + level_size;
	}

unlock:
	spin_unlock(&fs_info->qgroup_lock);
out:
	mutex_unlock(&fs_info->qgroup_ioctl_lock);
	return ret;
}

static int qgroup_reserve(struct btrfs_root *root, u64 num_bytes, bool enforce)
{
	struct btrfs_root *quota_root;
	struct btrfs_qgroup *qgroup;
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 ref_root = root->root_key.objectid;
	int ret = 0;
	int retried = 0;
	struct ulist_node *unode;
	struct ulist_iterator uiter;

	if (!is_fstree(ref_root))
		return 0;

	if (num_bytes == 0)
		return 0;
retry:
	spin_lock(&fs_info->qgroup_lock);
	quota_root = fs_info->quota_root;
	if (!quota_root)
		goto out;

	qgroup = find_qgroup_rb(fs_info, ref_root);
	if (!qgroup)
		goto out;

	/*
	 * in a first step, we check all affected qgroups if any limits would
	 * be exceeded
	 */
	ulist_reinit(fs_info->qgroup_ulist);
	ret = ulist_add(fs_info->qgroup_ulist, qgroup->qgroupid,
			(uintptr_t)qgroup, GFP_ATOMIC);
	if (ret < 0)
		goto out;
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(fs_info->qgroup_ulist, &uiter))) {
		struct btrfs_qgroup *qg;
		struct btrfs_qgroup_list *glist;

		qg = unode_aux_to_qgroup(unode);

		if (enforce && !qgroup_check_limits(qg, num_bytes)) {
			/*
			 * Commit the tree and retry, since we may have
			 * deletions which would free up space.
			 */
			if (!retried && qg->reserved > 0) {
				struct btrfs_trans_handle *trans;

				spin_unlock(&fs_info->qgroup_lock);
				ret = btrfs_start_delalloc_inodes(root, 0);
				if (ret)
					return ret;
				btrfs_wait_ordered_extents(root, -1, 0, (u64)-1);
				trans = btrfs_join_transaction(root);
				if (IS_ERR(trans))
					return PTR_ERR(trans);
				ret = btrfs_commit_transaction(trans);
				if (ret)
					return ret;
				retried++;
				goto retry;
			}
			ret = -EDQUOT;
			goto out;
		}

		list_for_each_entry(glist, &qg->groups, next_group) {
			ret = ulist_add(fs_info->qgroup_ulist,
					glist->group->qgroupid,
					(uintptr_t)glist->group, GFP_ATOMIC);
			if (ret < 0)
				goto out;
		}
	}
	ret = 0;
	/*
	 * no limits exceeded, now record the reservation into all qgroups
	 */
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(fs_info->qgroup_ulist, &uiter))) {
		struct btrfs_qgroup *qg;

		qg = unode_aux_to_qgroup(unode);

		trace_qgroup_update_reserve(fs_info, qg, num_bytes);
		qg->reserved += num_bytes;
	}

out:
	spin_unlock(&fs_info->qgroup_lock);
	return ret;
}
void btrfs_qgroup_free_refroot(struct btrfs_fs_info *fs_info,
			       u64 ref_root, u64 num_bytes)
{
	struct btrfs_root *quota_root;
	struct btrfs_qgroup *qgroup;
	struct ulist_node *unode;
	struct ulist_iterator uiter;
	int ret = 0;

	if (!is_fstree(ref_root))
		return;

	if (num_bytes == 0)
		return;

	spin_lock(&fs_info->qgroup_lock);

	quota_root = fs_info->quota_root;
	if (!quota_root)
		goto out;

	qgroup = find_qgroup_rb(fs_info, ref_root);
	if (!qgroup)
		goto out;

	ulist_reinit(fs_info->qgroup_ulist);
	ret = ulist_add(fs_info->qgroup_ulist, qgroup->qgroupid,
			(uintptr_t)qgroup, GFP_ATOMIC);
	if (ret < 0)
		goto out;
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(fs_info->qgroup_ulist, &uiter))) {
		struct btrfs_qgroup *qg;
		struct btrfs_qgroup_list *glist;

		qg = unode_aux_to_qgroup(unode);

		trace_qgroup_update_reserve(fs_info, qg, -(s64)num_bytes);
		if (qg->reserved < num_bytes)
			report_reserved_underflow(fs_info, qg, num_bytes);
		else
			qg->reserved -= num_bytes;

		list_for_each_entry(glist, &qg->groups, next_group) {
			ret = ulist_add(fs_info->qgroup_ulist,
					glist->group->qgroupid,
					(uintptr_t)glist->group, GFP_ATOMIC);
			if (ret < 0)
				goto out;
		}
	}

out:
	spin_unlock(&fs_info->qgroup_lock);
}
qgroup_rescan_leaf(struct btrfs_fs_info *fs_info, struct btrfs_path *path,
		   struct btrfs_trans_handle *trans)
{
	struct btrfs_key found;
	struct extent_buffer *scratch_leaf = NULL;
	struct ulist *roots = NULL;
	struct seq_list tree_mod_seq_elem = SEQ_LIST_INIT(tree_mod_seq_elem);
	u64 num_bytes;
	int slot;
	int ret;

	mutex_lock(&fs_info->qgroup_rescan_lock);
	ret = btrfs_search_slot_for_read(fs_info->extent_root,
					 &fs_info->qgroup_rescan_progress,
					 path, 1, 0);

	btrfs_debug(fs_info,
		"current progress key (%llu %u %llu), search_slot ret %d",
		fs_info->qgroup_rescan_progress.objectid,
		fs_info->qgroup_rescan_progress.type,
		fs_info->qgroup_rescan_progress.offset, ret);

	if (ret) {
		/*
		 * The rescan is about to end, we will not be scanning any
		 * further blocks. We cannot unset the RESCAN flag here, because
		 * we want to commit the transaction if everything went well.
		 * To make the live accounting work in this phase, we set our
		 * scan progress pointer such that every real extent objectid
		 * will be smaller.
		 */
		fs_info->qgroup_rescan_progress.objectid = (u64)-1;
		btrfs_release_path(path);
		mutex_unlock(&fs_info->qgroup_rescan_lock);
		return ret;
	}

	btrfs_item_key_to_cpu(path->nodes[0], &found,
			      btrfs_header_nritems(path->nodes[0]) - 1);
	fs_info->qgroup_rescan_progress.objectid = found.objectid + 1;

	btrfs_get_tree_mod_seq(fs_info, &tree_mod_seq_elem);
	scratch_leaf = btrfs_clone_extent_buffer(path->nodes[0]);
	if (!scratch_leaf) {
		ret = -ENOMEM;
		mutex_unlock(&fs_info->qgroup_rescan_lock);
		goto out;
	}
	extent_buffer_get(scratch_leaf);
	btrfs_tree_read_lock(scratch_leaf);
	btrfs_set_lock_blocking_rw(scratch_leaf, BTRFS_READ_LOCK);
	slot = path->slots[0];
	btrfs_release_path(path);
	mutex_unlock(&fs_info->qgroup_rescan_lock);

	for (; slot < btrfs_header_nritems(scratch_leaf); ++slot) {
		btrfs_item_key_to_cpu(scratch_leaf, &found, slot);
		if (found.type != BTRFS_EXTENT_ITEM_KEY &&
		    found.type != BTRFS_METADATA_ITEM_KEY)
			continue;
		if (found.type == BTRFS_METADATA_ITEM_KEY)
			num_bytes = fs_info->nodesize;
		else
			num_bytes = found.offset;

		ret = btrfs_find_all_roots(NULL, fs_info, found.objectid, 0,
					   &roots);
		if (ret < 0)
			goto out;
		/* For rescan, just pass old_roots as NULL */
		ret = btrfs_qgroup_account_extent(trans, fs_info,
				found.objectid, num_bytes, NULL, roots);
		if (ret < 0)
			goto out;
	}
out:
	if (scratch_leaf) {
		btrfs_tree_read_unlock_blocking(scratch_leaf);
		free_extent_buffer(scratch_leaf);
	}
	btrfs_put_tree_mod_seq(fs_info, &tree_mod_seq_elem);

	return ret;
}

static void btrfs_qgroup_rescan_worker(struct btrfs_work *work)
{
	struct btrfs_fs_info *fs_info = container_of(work, struct btrfs_fs_info,
						     qgroup_rescan_work);
	struct btrfs_path *path;
	struct btrfs_trans_handle *trans = NULL;
	int err = -ENOMEM;
	int ret = 0;

	path = btrfs_alloc_path();
	if (!path)
		goto out;

	err = 0;
	while (!err && !btrfs_fs_closing(fs_info)) {
		trans = btrfs_start_transaction(fs_info->fs_root, 0);
		if (IS_ERR(trans)) {
			err = PTR_ERR(trans);
			break;
		}
		if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &fs_info->flags)) {
			err = -EINTR;
		} else {
			err = qgroup_rescan_leaf(fs_info, path, trans);
		}
		if (err > 0)
			btrfs_commit_transaction(trans);
		else
			btrfs_end_transaction(trans);
	}

out:
	btrfs_free_path(path);

	mutex_lock(&fs_info->qgroup_rescan_lock);
	if (!btrfs_fs_closing(fs_info))
		fs_info->qgroup_flags &= ~BTRFS_QGROUP_STATUS_FLAG_RESCAN;

	if (err > 0 &&
	    fs_info->qgroup_flags & BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT) {
		fs_info->qgroup_flags &= ~BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
	} else if (err < 0) {
		fs_info->qgroup_flags |= BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT;
	}
	mutex_unlock(&fs_info->qgroup_rescan_lock);

	/*
	 * only update status, since the previous part has already updated the
	 * qgroup info.
	 */
	trans = btrfs_start_transaction(fs_info->quota_root, 1);
	if (IS_ERR(trans)) {
		err = PTR_ERR(trans);
		btrfs_err(fs_info,
			  "fail to start transaction for status update: %d\n",
			  err);
		goto done;
	}
	ret = update_qgroup_status_item(trans, fs_info, fs_info->quota_root);
	if (ret < 0) {
		err = ret;
		btrfs_err(fs_info, "fail to update qgroup status: %d", err);
	}
	btrfs_end_transaction(trans);

	if (btrfs_fs_closing(fs_info)) {
		btrfs_info(fs_info, "qgroup scan paused");
	} else if (err >= 0) {
		btrfs_info(fs_info, "qgroup scan completed%s",
			err > 0 ? " (inconsistency flag cleared)" : "");
	} else {
		btrfs_err(fs_info, "qgroup scan failed with %d", err);
	}

done:
	mutex_lock(&fs_info->qgroup_rescan_lock);
	fs_info->qgroup_rescan_running = false;
	mutex_unlock(&fs_info->qgroup_rescan_lock);
	complete_all(&fs_info->qgroup_rescan_completion);
}
static void
qgroup_rescan_zero_tracking(struct btrfs_fs_info *fs_info)
{
	struct rb_node *n;
	struct btrfs_qgroup *qgroup;

	spin_lock(&fs_info->qgroup_lock);
	/* clear all current qgroup tracking information */
	for (n = rb_first(&fs_info->qgroup_tree); n; n = rb_next(n)) {
		qgroup = rb_entry(n, struct btrfs_qgroup, node);
		qgroup->rfer = 0;
		qgroup->rfer_cmpr = 0;
		qgroup->excl = 0;
		qgroup->excl_cmpr = 0;
	}
	spin_unlock(&fs_info->qgroup_lock);
}
 */
int btrfs_qgroup_reserve_data(struct inode *inode, u64 start, u64 len)
{
	struct btrfs_root *root = BTRFS_I(inode)->root;
	struct extent_changeset changeset;
	struct ulist_node *unode;
	struct ulist_iterator uiter;
	int ret;

	if (!test_bit(BTRFS_FS_QUOTA_ENABLED, &root->fs_info->flags) ||
	    !is_fstree(root->objectid) || len == 0)
		return 0;

	changeset.bytes_changed = 0;
	ulist_init(&changeset.range_changed);
	ret = set_record_extent_bits(&BTRFS_I(inode)->io_tree, start,
			start + len -1, EXTENT_QGROUP_RESERVED, &changeset);
	trace_btrfs_qgroup_reserve_data(inode, start, len,
					changeset.bytes_changed,
					QGROUP_RESERVE);
	if (ret < 0)
		goto cleanup;
	ret = qgroup_reserve(root, changeset.bytes_changed, true);
	if (ret < 0)
		goto cleanup;

	ulist_release(&changeset.range_changed);
	return ret;

cleanup:
	/* cleanup already reserved ranges */
	ULIST_ITER_INIT(&uiter);
	while ((unode = ulist_next(&changeset.range_changed, &uiter)))
		clear_extent_bit(&BTRFS_I(inode)->io_tree, unode->val,
				 unode->aux, EXTENT_QGROUP_RESERVED, 0, 0, NULL,
				 GFP_NOFS);
	ulist_release(&changeset.range_changed);
	return ret;
}
 */
void btrfs_qgroup_check_reserved_leak(struct inode *inode)
{
	struct extent_changeset changeset;
	struct ulist_node *unode;
	struct ulist_iterator iter;
	int ret;

	changeset.bytes_changed = 0;
	ulist_init(&changeset.range_changed);
	ret = clear_record_extent_bits(&BTRFS_I(inode)->io_tree, 0, (u64)-1,
			EXTENT_QGROUP_RESERVED, &changeset);

	WARN_ON(ret < 0);
	if (WARN_ON(changeset.bytes_changed)) {
		ULIST_ITER_INIT(&iter);
		while ((unode = ulist_next(&changeset.range_changed, &iter))) {
			btrfs_warn(BTRFS_I(inode)->root->fs_info,
				"leaking qgroup reserved space, ino: %lu, start: %llu, end: %llu",
				inode->i_ino, unode->val, unode->aux);
		}
		btrfs_qgroup_free_refroot(BTRFS_I(inode)->root->fs_info,
				BTRFS_I(inode)->root->objectid,
				changeset.bytes_changed);

	}
	ulist_release(&changeset.range_changed);
}
