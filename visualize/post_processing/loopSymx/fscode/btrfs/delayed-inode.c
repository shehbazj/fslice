				struct btrfs_delayed_item **prev,
				struct btrfs_delayed_item **next)
{
	struct rb_node *node, *prev_node = NULL;
	struct btrfs_delayed_item *delayed_item = NULL;
	int ret = 0;

	node = root->rb_node;

	while (node) {
		delayed_item = rb_entry(node, struct btrfs_delayed_item,
					rb_node);
		prev_node = node;
		ret = btrfs_comp_cpu_keys(&delayed_item->key, key);
		if (ret < 0)
			node = node->rb_right;
		else if (ret > 0)
			node = node->rb_left;
		else
			return delayed_item;
	}

	if (prev) {
		if (!prev_node)
			*prev = NULL;
		else if (ret < 0)
			*prev = delayed_item;
		else if ((node = rb_prev(prev_node)) != NULL) {
			*prev = rb_entry(node, struct btrfs_delayed_item,
					 rb_node);
		} else
			*prev = NULL;
	}

	if (next) {
		if (!prev_node)
			*next = NULL;
		else if (ret > 0)
			*next = delayed_item;
		else if ((node = rb_next(prev_node)) != NULL) {
			*next = rb_entry(node, struct btrfs_delayed_item,
					 rb_node);
		} else
			*next = NULL;
	}
	return NULL;
}
				    struct btrfs_delayed_item *ins,
				    int action)
{
	struct rb_node **p, *node;
	struct rb_node *parent_node = NULL;
	struct rb_root *root;
	struct btrfs_delayed_item *item;
	int cmp;

	if (action == BTRFS_DELAYED_INSERTION_ITEM)
		root = &delayed_node->ins_root;
	else if (action == BTRFS_DELAYED_DELETION_ITEM)
		root = &delayed_node->del_root;
	else
		BUG();
	p = &root->rb_node;
	node = &ins->rb_node;

	while (*p) {
		parent_node = *p;
		item = rb_entry(parent_node, struct btrfs_delayed_item,
				 rb_node);

		cmp = btrfs_comp_cpu_keys(&item->key, &ins->key);
		if (cmp < 0)
			p = &(*p)->rb_right;
		else if (cmp > 0)
			p = &(*p)->rb_left;
		else
			return -EEXIST;
	}

	rb_link_node(node, parent_node, p);
	rb_insert_color(node, root);
	ins->delayed_node = delayed_node;
	ins->ins_or_del = action;

	if (ins->key.type == BTRFS_DIR_INDEX_KEY &&
	    action == BTRFS_DELAYED_INSERTION_ITEM &&
	    ins->key.offset >= delayed_node->index_cnt)
			delayed_node->index_cnt = ins->key.offset + 1;

	delayed_node->count++;
	atomic_inc(&delayed_node->root->fs_info->delayed_root->items);
	return 0;
}
				    struct btrfs_path *path,
				    struct btrfs_delayed_item *item)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_delayed_item *curr, *next;
	int free_space;
	int total_data_size = 0, total_size = 0;
	struct extent_buffer *leaf;
	char *data_ptr;
	struct btrfs_key *keys;
	u32 *data_size;
	struct list_head head;
	int slot;
	int nitems;
	int i;
	int ret = 0;

	BUG_ON(!path->nodes[0]);

	leaf = path->nodes[0];
	free_space = btrfs_leaf_free_space(fs_info, leaf);
	INIT_LIST_HEAD(&head);

	next = item;
	nitems = 0;

	/*
	 * count the number of the continuous items that we can insert in batch
	 */
	while (total_size + next->data_len + sizeof(struct btrfs_item) <=
	       free_space) {
		total_data_size += next->data_len;
		total_size += next->data_len + sizeof(struct btrfs_item);
		list_add_tail(&next->tree_list, &head);
		nitems++;

		curr = next;
		next = __btrfs_next_delayed_item(curr);
		if (!next)
			break;

		if (!btrfs_is_continuous_delayed_item(curr, next))
			break;
	}

	if (!nitems) {
		ret = 0;
		goto out;
	}

	/*
	 * we need allocate some memory space, but it might cause the task
	 * to sleep, so we set all locked nodes in the path to blocking locks
	 * first.
	 */
	btrfs_set_path_blocking(path);

	keys = kmalloc_array(nitems, sizeof(struct btrfs_key), GFP_NOFS);
	if (!keys) {
		ret = -ENOMEM;
		goto out;
	}

	data_size = kmalloc_array(nitems, sizeof(u32), GFP_NOFS);
	if (!data_size) {
		ret = -ENOMEM;
		goto error;
	}

	/* get keys of all the delayed items */
	i = 0;
	list_for_each_entry(next, &head, tree_list) {
		keys[i] = next->key;
		data_size[i] = next->data_len;
		i++;
	}

	/* reset all the locked nodes in the patch to spinning locks. */
	btrfs_clear_path_blocking(path, NULL, 0);

	/* insert the keys of the items */
	setup_items_for_insert(root, path, keys, data_size,
			       total_data_size, total_size, nitems);

	/* insert the dir index items */
	slot = path->slots[0];
	list_for_each_entry_safe(curr, next, &head, tree_list) {
		data_ptr = btrfs_item_ptr(leaf, slot, char);
		write_extent_buffer(leaf, &curr->data,
				    (unsigned long)data_ptr,
				    curr->data_len);
		slot++;

		btrfs_delayed_item_release_metadata(fs_info, curr);

		list_del(&curr->tree_list);
		btrfs_release_delayed_item(curr);
	}

error:
	kfree(data_size);
	kfree(keys);
out:
	return ret;
}
				    struct btrfs_path *path,
				    struct btrfs_delayed_item *item)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_delayed_item *curr, *next;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	struct list_head head;
	int nitems, i, last_item;
	int ret = 0;

	BUG_ON(!path->nodes[0]);

	leaf = path->nodes[0];

	i = path->slots[0];
	last_item = btrfs_header_nritems(leaf) - 1;
	if (i > last_item)
		return -ENOENT;	/* FIXME: Is errno suitable? */

	next = item;
	INIT_LIST_HEAD(&head);
	btrfs_item_key_to_cpu(leaf, &key, i);
	nitems = 0;
	/*
	 * count the number of the dir index items that we can delete in batch
	 */
	while (btrfs_comp_cpu_keys(&next->key, &key) == 0) {
		list_add_tail(&next->tree_list, &head);
		nitems++;

		curr = next;
		next = __btrfs_next_delayed_item(curr);
		if (!next)
			break;

		if (!btrfs_is_continuous_delayed_item(curr, next))
			break;

		i++;
		if (i > last_item)
			break;
		btrfs_item_key_to_cpu(leaf, &key, i);
	}

	if (!nitems)
		return 0;

	ret = btrfs_del_items(trans, root, path, path->slots[0], nitems);
	if (ret)
		goto out;

	list_for_each_entry_safe(curr, next, &head, tree_list) {
		btrfs_delayed_item_release_metadata(fs_info, curr);
		list_del(&curr->tree_list);
		btrfs_release_delayed_item(curr);
	}

out:
	return ret;
}
static int __btrfs_run_delayed_items(struct btrfs_trans_handle *trans,
				     struct btrfs_fs_info *fs_info, int nr)
{
	struct btrfs_delayed_root *delayed_root;
	struct btrfs_delayed_node *curr_node, *prev_node;
	struct btrfs_path *path;
	struct btrfs_block_rsv *block_rsv;
	int ret = 0;
	bool count = (nr > 0);

	if (trans->aborted)
		return -EIO;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->leave_spinning = 1;

	block_rsv = trans->block_rsv;
	trans->block_rsv = &fs_info->delayed_block_rsv;

	delayed_root = fs_info->delayed_root;

	curr_node = btrfs_first_delayed_node(delayed_root);
	while (curr_node && (!count || (count && nr--))) {
		ret = __btrfs_commit_inode_delayed_items(trans, path,
							 curr_node);
		if (ret) {
			btrfs_release_delayed_node(curr_node);
			curr_node = NULL;
			btrfs_abort_transaction(trans, ret);
			break;
		}

		prev_node = curr_node;
		curr_node = btrfs_next_delayed_node(curr_node);
		btrfs_release_delayed_node(prev_node);
	}

	if (curr_node)
		btrfs_release_delayed_node(curr_node);
	btrfs_free_path(path);
	trans->block_rsv = block_rsv;

	return ret;
}
				     struct list_head *ins_list,
				     struct list_head *del_list)
{
	struct btrfs_delayed_node *delayed_node;
	struct btrfs_delayed_item *item;

	delayed_node = btrfs_get_delayed_node(BTRFS_I(inode));
	if (!delayed_node)
		return false;

	/*
	 * We can only do one readdir with delayed items at a time because of
	 * item->readdir_list.
	 */
	inode_unlock_shared(inode);
	inode_lock(inode);

	mutex_lock(&delayed_node->mutex);
	item = __btrfs_first_delayed_insertion_item(delayed_node);
	while (item) {
		refcount_inc(&item->refs);
		list_add_tail(&item->readdir_list, ins_list);
		item = __btrfs_next_delayed_item(item);
	}

	item = __btrfs_first_delayed_deletion_item(delayed_node);
	while (item) {
		refcount_inc(&item->refs);
		list_add_tail(&item->readdir_list, del_list);
		item = __btrfs_next_delayed_item(item);
	}
	mutex_unlock(&delayed_node->mutex);
	/*
	 * This delayed node is still cached in the btrfs inode, so refs
	 * must be > 1 now, and we needn't check it is going to be freed
	 * or not.
	 *
	 * Besides that, this function is used to read dir, we do not
	 * insert/delete delayed items in this period. So we also needn't
	 * requeue or dequeue this delayed node.
	 */
	refcount_dec(&delayed_node->refs);

	return true;
}

static void __btrfs_kill_delayed_node(struct btrfs_delayed_node *delayed_node)
{
	struct btrfs_root *root = delayed_node->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_delayed_item *curr_item, *prev_item;

	mutex_lock(&delayed_node->mutex);
	curr_item = __btrfs_first_delayed_insertion_item(delayed_node);
	while (curr_item) {
		btrfs_delayed_item_release_metadata(fs_info, curr_item);
		prev_item = curr_item;
		curr_item = __btrfs_next_delayed_item(prev_item);
		btrfs_release_delayed_item(prev_item);
	}

	curr_item = __btrfs_first_delayed_deletion_item(delayed_node);
	while (curr_item) {
		btrfs_delayed_item_release_metadata(fs_info, curr_item);
		prev_item = curr_item;
		curr_item = __btrfs_next_delayed_item(prev_item);
		btrfs_release_delayed_item(prev_item);
	}

	if (test_bit(BTRFS_DELAYED_NODE_DEL_IREF, &delayed_node->flags))
		btrfs_release_delayed_iref(delayed_node);

	if (test_bit(BTRFS_DELAYED_NODE_INODE_DIRTY, &delayed_node->flags)) {
		btrfs_delayed_inode_release_metadata(fs_info, delayed_node);
		btrfs_release_delayed_inode(delayed_node);
	}
	mutex_unlock(&delayed_node->mutex);
}

void btrfs_kill_all_delayed_nodes(struct btrfs_root *root)
{
	u64 inode_id = 0;
	struct btrfs_delayed_node *delayed_nodes[8];
	int i, n;

	while (1) {
		spin_lock(&root->inode_lock);
		n = radix_tree_gang_lookup(&root->delayed_nodes_tree,
					   (void **)delayed_nodes, inode_id,
					   ARRAY_SIZE(delayed_nodes));
		if (!n) {
			spin_unlock(&root->inode_lock);
			break;
		}

		inode_id = delayed_nodes[n - 1]->inode_id + 1;

		for (i = 0; i < n; i++)
			refcount_inc(&delayed_nodes[i]->refs);
		spin_unlock(&root->inode_lock);

		for (i = 0; i < n; i++) {
			__btrfs_kill_delayed_node(delayed_nodes[i]);
			btrfs_release_delayed_node(delayed_nodes[i]);
		}
	}
}

void btrfs_destroy_delayed_inodes(struct btrfs_fs_info *fs_info)
{
	struct btrfs_delayed_node *curr_node, *prev_node;

	curr_node = btrfs_first_delayed_node(fs_info->delayed_root);
	while (curr_node) {
		__btrfs_kill_delayed_node(curr_node);

		prev_node = curr_node;
		curr_node = btrfs_next_delayed_node(curr_node);
		btrfs_release_delayed_node(prev_node);
	}
}
