static struct rb_node *tree_insert(struct rb_root *root, u64 file_offset,
				   struct rb_node *node)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent = NULL;
	struct btrfs_ordered_extent *entry;

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct btrfs_ordered_extent, rb_node);

		if (file_offset < entry->file_offset)
			p = &(*p)->rb_left;
		else if (file_offset >= entry_end(entry))
			p = &(*p)->rb_right;
		else
			return parent;
	}

	rb_link_node(node, parent, p);
	rb_insert_color(node, root);
	return NULL;
}
static struct rb_node *__tree_search(struct rb_root *root, u64 file_offset,
				     struct rb_node **prev_ret)
{
	struct rb_node *n = root->rb_node;
	struct rb_node *prev = NULL;
	struct rb_node *test;
	struct btrfs_ordered_extent *entry;
	struct btrfs_ordered_extent *prev_entry = NULL;

	while (n) {
		entry = rb_entry(n, struct btrfs_ordered_extent, rb_node);
		prev = n;
		prev_entry = entry;

		if (file_offset < entry->file_offset)
			n = n->rb_left;
		else if (file_offset >= entry_end(entry))
			n = n->rb_right;
		else
			return n;
	}
	if (!prev_ret)
		return NULL;

	while (prev && file_offset >= entry_end(prev_entry)) {
		test = rb_next(prev);
		if (!test)
			break;
		prev_entry = rb_entry(test, struct btrfs_ordered_extent,
				      rb_node);
		if (file_offset < entry_end(prev_entry))
			break;

		prev = test;
	}
	if (prev)
		prev_entry = rb_entry(prev, struct btrfs_ordered_extent,
				      rb_node);
	while (prev && file_offset < entry_end(prev_entry)) {
		test = rb_prev(prev);
		if (!test)
			break;
		prev_entry = rb_entry(test, struct btrfs_ordered_extent,
				      rb_node);
		prev = test;
	}
	*prev_ret = prev;
	return NULL;
}
			      const loff_t start,
			      const loff_t end)
{
	struct btrfs_ordered_inode_tree *tree;
	struct btrfs_ordered_extent *ordered;
	struct rb_node *n;
	struct rb_node *prev;

	tree = &inode->ordered_tree;
	spin_lock_irq(&tree->lock);
	n = __tree_search(&tree->tree, end, &prev);
	if (!n)
		n = prev;
	for (; n; n = rb_prev(n)) {
		ordered = rb_entry(n, struct btrfs_ordered_extent, rb_node);
		if (ordered->file_offset > end)
			continue;
		if (entry_end(ordered) <= start)
			break;
		if (test_and_set_bit(BTRFS_ORDERED_LOGGED, &ordered->flags))
			continue;
		list_add(&ordered->log_list, logged_list);
		refcount_inc(&ordered->refs);
	}
	spin_unlock_irq(&tree->lock);
}

void btrfs_put_logged_extents(struct list_head *logged_list)
{
	struct btrfs_ordered_extent *ordered;

	while (!list_empty(logged_list)) {
		ordered = list_first_entry(logged_list,
					   struct btrfs_ordered_extent,
					   log_list);
		list_del_init(&ordered->log_list);
		btrfs_put_ordered_extent(ordered);
	}
}
void btrfs_wait_logged_extents(struct btrfs_trans_handle *trans,
			       struct btrfs_root *log, u64 transid)
{
	struct btrfs_ordered_extent *ordered;
	int index = transid % 2;

	spin_lock_irq(&log->log_extents_lock[index]);
	while (!list_empty(&log->logged_list[index])) {
		struct inode *inode;
		ordered = list_first_entry(&log->logged_list[index],
					   struct btrfs_ordered_extent,
					   log_list);
		list_del_init(&ordered->log_list);
		inode = ordered->inode;
		spin_unlock_irq(&log->log_extents_lock[index]);

		if (!test_bit(BTRFS_ORDERED_IO_DONE, &ordered->flags) &&
		    !test_bit(BTRFS_ORDERED_DIRECT, &ordered->flags)) {
			u64 start = ordered->file_offset;
			u64 end = ordered->file_offset + ordered->len - 1;

			WARN_ON(!inode);
			filemap_fdatawrite_range(inode->i_mapping, start, end);
		}
		wait_event(ordered->wait, test_bit(BTRFS_ORDERED_IO_DONE,
						   &ordered->flags));

		/*
		 * In order to keep us from losing our ordered extent
		 * information when committing the transaction we have to make
		 * sure that any logged extents are completed when we go to
		 * commit the transaction.  To do this we simply increase the
		 * current transactions pending_ordered counter and decrement it
		 * when the ordered extent completes.
		 */
		if (!test_bit(BTRFS_ORDERED_COMPLETE, &ordered->flags)) {
			struct btrfs_ordered_inode_tree *tree;

			tree = &BTRFS_I(inode)->ordered_tree;
			spin_lock_irq(&tree->lock);
			if (!test_bit(BTRFS_ORDERED_COMPLETE, &ordered->flags)) {
				set_bit(BTRFS_ORDERED_PENDING, &ordered->flags);
				atomic_inc(&trans->transaction->pending_ordered);
			}
			spin_unlock_irq(&tree->lock);
		}
		btrfs_put_ordered_extent(ordered);
		spin_lock_irq(&log->log_extents_lock[index]);
	}
	spin_unlock_irq(&log->log_extents_lock[index]);
}

void btrfs_free_logged_extents(struct btrfs_root *log, u64 transid)
{
	struct btrfs_ordered_extent *ordered;
	int index = transid % 2;

	spin_lock_irq(&log->log_extents_lock[index]);
	while (!list_empty(&log->logged_list[index])) {
		ordered = list_first_entry(&log->logged_list[index],
					   struct btrfs_ordered_extent,
					   log_list);
		list_del_init(&ordered->log_list);
		spin_unlock_irq(&log->log_extents_lock[index]);
		btrfs_put_ordered_extent(ordered);
		spin_lock_irq(&log->log_extents_lock[index]);
	}
	spin_unlock_irq(&log->log_extents_lock[index]);
}
 */
void btrfs_put_ordered_extent(struct btrfs_ordered_extent *entry)
{
	struct list_head *cur;
	struct btrfs_ordered_sum *sum;

	trace_btrfs_ordered_extent_put(entry->inode, entry);

	if (refcount_dec_and_test(&entry->refs)) {
		ASSERT(list_empty(&entry->log_list));
		ASSERT(list_empty(&entry->trans_list));
		ASSERT(list_empty(&entry->root_extent_list));
		ASSERT(RB_EMPTY_NODE(&entry->rb_node));
		if (entry->inode)
			btrfs_add_delayed_iput(entry->inode);
		while (!list_empty(&entry->list)) {
			cur = entry->list.next;
			sum = list_entry(cur, struct btrfs_ordered_sum, list);
			list_del(&sum->list);
			kfree(sum);
		}
		kmem_cache_free(btrfs_ordered_extent_cache, entry);
	}
}
int btrfs_wait_ordered_extents(struct btrfs_root *root, int nr,
			       const u64 range_start, const u64 range_len)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	LIST_HEAD(splice);
	LIST_HEAD(skipped);
	LIST_HEAD(works);
	struct btrfs_ordered_extent *ordered, *next;
	int count = 0;
	const u64 range_end = range_start + range_len;

	mutex_lock(&root->ordered_extent_mutex);
	spin_lock(&root->ordered_extent_lock);
	list_splice_init(&root->ordered_extents, &splice);
	while (!list_empty(&splice) && nr) {
		ordered = list_first_entry(&splice, struct btrfs_ordered_extent,
					   root_extent_list);

		if (range_end <= ordered->start ||
		    ordered->start + ordered->disk_len <= range_start) {
			list_move_tail(&ordered->root_extent_list, &skipped);
			cond_resched_lock(&root->ordered_extent_lock);
			continue;
		}

		list_move_tail(&ordered->root_extent_list,
			       &root->ordered_extents);
		refcount_inc(&ordered->refs);
		spin_unlock(&root->ordered_extent_lock);

		btrfs_init_work(&ordered->flush_work,
				btrfs_flush_delalloc_helper,
				btrfs_run_ordered_extent_work, NULL, NULL);
		list_add_tail(&ordered->work_list, &works);
		btrfs_queue_work(fs_info->flush_workers, &ordered->flush_work);

		cond_resched();
		spin_lock(&root->ordered_extent_lock);
		if (nr != -1)
			nr--;
		count++;
	}
	list_splice_tail(&skipped, &root->ordered_extents);
	list_splice_tail(&splice, &root->ordered_extents);
	spin_unlock(&root->ordered_extent_lock);

	list_for_each_entry_safe(ordered, next, &works, work_list) {
		list_del_init(&ordered->work_list);
		wait_for_completion(&ordered->completion);
		btrfs_put_ordered_extent(ordered);
		cond_resched();
	}
	mutex_unlock(&root->ordered_extent_mutex);

	return count;
}
int btrfs_wait_ordered_roots(struct btrfs_fs_info *fs_info, int nr,
			      const u64 range_start, const u64 range_len)
{
	struct btrfs_root *root;
	struct list_head splice;
	int done;
	int total_done = 0;

	INIT_LIST_HEAD(&splice);

	mutex_lock(&fs_info->ordered_operations_mutex);
	spin_lock(&fs_info->ordered_root_lock);
	list_splice_init(&fs_info->ordered_roots, &splice);
	while (!list_empty(&splice) && nr) {
		root = list_first_entry(&splice, struct btrfs_root,
					ordered_root);
		root = btrfs_grab_fs_root(root);
		BUG_ON(!root);
		list_move_tail(&root->ordered_root,
			       &fs_info->ordered_roots);
		spin_unlock(&fs_info->ordered_root_lock);

		done = btrfs_wait_ordered_extents(root, nr,
						  range_start, range_len);
		btrfs_put_fs_root(root);
		total_done += done;

		spin_lock(&fs_info->ordered_root_lock);
		if (nr != -1) {
			nr -= done;
			WARN_ON(nr < 0);
		}
	}
	list_splice_tail(&splice, &fs_info->ordered_roots);
	spin_unlock(&fs_info->ordered_root_lock);
	mutex_unlock(&fs_info->ordered_operations_mutex);

	return total_done;
}
 */
int btrfs_wait_ordered_range(struct inode *inode, u64 start, u64 len)
{
	int ret = 0;
	int ret_wb = 0;
	u64 end;
	u64 orig_end;
	struct btrfs_ordered_extent *ordered;

	if (start + len < start) {
		orig_end = INT_LIMIT(loff_t);
	} else {
		orig_end = start + len - 1;
		if (orig_end > INT_LIMIT(loff_t))
			orig_end = INT_LIMIT(loff_t);
	}

	/* start IO across the range first to instantiate any delalloc
	 * extents
	 */
	ret = btrfs_fdatawrite_range(inode, start, orig_end);
	if (ret)
		return ret;

	/*
	 * If we have a writeback error don't return immediately. Wait first
	 * for any ordered extents that haven't completed yet. This is to make
	 * sure no one can dirty the same page ranges and call writepages()
	 * before the ordered extents complete - to avoid failures (-EEXIST)
	 * when adding the new ordered extents to the ordered tree.
	 */
	ret_wb = filemap_fdatawait_range(inode->i_mapping, start, orig_end);

	end = orig_end;
	while (1) {
		ordered = btrfs_lookup_first_ordered_extent(inode, end);
		if (!ordered)
			break;
		if (ordered->file_offset > orig_end) {
			btrfs_put_ordered_extent(ordered);
			break;
		}
		if (ordered->file_offset + ordered->len <= start) {
			btrfs_put_ordered_extent(ordered);
			break;
		}
		btrfs_start_ordered_extent(inode, ordered, 1);
		end = ordered->file_offset;
		if (test_bit(BTRFS_ORDERED_IOERR, &ordered->flags))
			ret = -EIO;
		btrfs_put_ordered_extent(ordered);
		if (ret || end == 0 || end == start)
			break;
		end--;
	}
	return ret_wb ? ret_wb : ret;
}
struct btrfs_ordered_extent *btrfs_lookup_ordered_range(
		struct btrfs_inode *inode, u64 file_offset, u64 len)
{
	struct btrfs_ordered_inode_tree *tree;
	struct rb_node *node;
	struct btrfs_ordered_extent *entry = NULL;

	tree = &inode->ordered_tree;
	spin_lock_irq(&tree->lock);
	node = tree_search(tree, file_offset);
	if (!node) {
		node = tree_search(tree, file_offset + len);
		if (!node)
			goto out;
	}

	while (1) {
		entry = rb_entry(node, struct btrfs_ordered_extent, rb_node);
		if (range_overlaps(entry, file_offset, len))
			break;

		if (entry->file_offset >= file_offset + len) {
			entry = NULL;
			break;
		}
		entry = NULL;
		node = rb_next(node);
		if (!node)
			break;
	}
out:
	if (entry)
		refcount_inc(&entry->refs);
	spin_unlock_irq(&tree->lock);
	return entry;
}
int btrfs_ordered_update_i_size(struct inode *inode, u64 offset,
				struct btrfs_ordered_extent *ordered)
{
	struct btrfs_ordered_inode_tree *tree = &BTRFS_I(inode)->ordered_tree;
	u64 disk_i_size;
	u64 new_i_size;
	u64 i_size = i_size_read(inode);
	struct rb_node *node;
	struct rb_node *prev = NULL;
	struct btrfs_ordered_extent *test;
	int ret = 1;
	u64 orig_offset = offset;

	spin_lock_irq(&tree->lock);
	if (ordered) {
		offset = entry_end(ordered);
		if (test_bit(BTRFS_ORDERED_TRUNCATED, &ordered->flags))
			offset = min(offset,
				     ordered->file_offset +
				     ordered->truncated_len);
	} else {
		offset = ALIGN(offset, btrfs_inode_sectorsize(inode));
	}
	disk_i_size = BTRFS_I(inode)->disk_i_size;

	/*
	 * truncate file.
	 * If ordered is not NULL, then this is called from endio and
	 * disk_i_size will be updated by either truncate itself or any
	 * in-flight IOs which are inside the disk_i_size.
	 *
	 * Because btrfs_setsize() may set i_size with disk_i_size if truncate
	 * fails somehow, we need to make sure we have a precise disk_i_size by
	 * updating it as usual.
	 *
	 */
	if (!ordered && disk_i_size > i_size) {
		BTRFS_I(inode)->disk_i_size = orig_offset;
		ret = 0;
		goto out;
	}

	/*
	 * if the disk i_size is already at the inode->i_size, or
	 * this ordered extent is inside the disk i_size, we're done
	 */
	if (disk_i_size == i_size)
		goto out;

	/*
	 * We still need to update disk_i_size if outstanding_isize is greater
	 * than disk_i_size.
	 */
	if (offset <= disk_i_size &&
	    (!ordered || ordered->outstanding_isize <= disk_i_size))
		goto out;

	/*
	 * walk backward from this ordered extent to disk_i_size.
	 * if we find an ordered extent then we can't update disk i_size
	 * yet
	 */
	if (ordered) {
		node = rb_prev(&ordered->rb_node);
	} else {
		prev = tree_search(tree, offset);
		/*
		 * we insert file extents without involving ordered struct,
		 * so there should be no ordered struct cover this offset
		 */
		if (prev) {
			test = rb_entry(prev, struct btrfs_ordered_extent,
					rb_node);
			BUG_ON(offset_in_entry(test, offset));
		}
		node = prev;
	}
	for (; node; node = rb_prev(node)) {
		test = rb_entry(node, struct btrfs_ordered_extent, rb_node);

		/* We treat this entry as if it doesn't exist */
		if (test_bit(BTRFS_ORDERED_UPDATED_ISIZE, &test->flags))
			continue;

		if (entry_end(test) <= disk_i_size)
			break;
		if (test->file_offset >= i_size)
			break;

		/*
		 * We don't update disk_i_size now, so record this undealt
		 * i_size. Or we will not know the real i_size.
		 */
		if (test->outstanding_isize < offset)
			test->outstanding_isize = offset;
		if (ordered &&
		    ordered->outstanding_isize > test->outstanding_isize)
			test->outstanding_isize = ordered->outstanding_isize;
		goto out;
	}
	new_i_size = min_t(u64, offset, i_size);

	/*
	 * Some ordered extents may completed before the current one, and
	 * we hold the real i_size in ->outstanding_isize.
	 */
	if (ordered && ordered->outstanding_isize > new_i_size)
		new_i_size = min_t(u64, ordered->outstanding_isize, i_size);
	BTRFS_I(inode)->disk_i_size = new_i_size;
	ret = 0;
out:
	/*
	 * We need to do this because we can't remove ordered extents until
	 * after the i_disk_size has been updated and then the inode has been
	 * updated to reflect the change, so we need to tell anybody who finds
	 * this ordered extent that we've already done all the real work, we
	 * just haven't completed all the other work.
	 */
	if (ordered)
		set_bit(BTRFS_ORDERED_UPDATED_ISIZE, &ordered->flags);
	spin_unlock_irq(&tree->lock);
	return ret;
}
