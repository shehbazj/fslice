#ifdef ES_DEBUG__
static void ext4_es_print_tree(struct inode *inode)
{
	struct ext4_es_tree *tree;
	struct rb_node *node;

	printk(KERN_DEBUG "status extents for inode %lu:", inode->i_ino);
	tree = &EXT4_I(inode)->i_es_tree;
	node = rb_first(&tree->root);
	while (node) {
		struct extent_status *es;
		es = rb_entry(node, struct extent_status, rb_node);
		printk(KERN_DEBUG " [%u/%u) %llu %x",
		       es->es_lblk, es->es_len,
		       ext4_es_pblock(es), ext4_es_status(es));
		node = rb_next(node);
	}
	printk(KERN_DEBUG "\n");
}
static struct extent_status *__es_tree_search(struct rb_root *root,
					      ext4_lblk_t lblk)
{
	struct rb_node *node = root->rb_node;
	struct extent_status *es = NULL;

	while (node) {
		es = rb_entry(node, struct extent_status, rb_node);
		if (lblk < es->es_lblk)
			node = node->rb_left;
		else if (lblk > ext4_es_end(es))
			node = node->rb_right;
		else
			return es;
	}

	if (es && lblk < es->es_lblk)
		return es;

	if (es && lblk > ext4_es_end(es)) {
		node = rb_next(&es->rb_node);
		return node ? rb_entry(node, struct extent_status, rb_node) :
			      NULL;
	}

	return NULL;
}
				 ext4_lblk_t lblk, ext4_lblk_t end,
				 struct extent_status *es)
{
	struct ext4_es_tree *tree = NULL;
	struct extent_status *es1 = NULL;
	struct rb_node *node;

	BUG_ON(es == NULL);
	BUG_ON(end < lblk);
	trace_ext4_es_find_delayed_extent_range_enter(inode, lblk);

	read_lock(&EXT4_I(inode)->i_es_lock);
	tree = &EXT4_I(inode)->i_es_tree;

	/* find extent in cache firstly */
	es->es_lblk = es->es_len = es->es_pblk = 0;
	if (tree->cache_es) {
		es1 = tree->cache_es;
		if (in_range(lblk, es1->es_lblk, es1->es_len)) {
			es_debug("%u cached by [%u/%u) %llu %x\n",
				 lblk, es1->es_lblk, es1->es_len,
				 ext4_es_pblock(es1), ext4_es_status(es1));
			goto out;
		}
	}

	es1 = __es_tree_search(&tree->root, lblk);

out:
	if (es1 && !ext4_es_is_delayed(es1)) {
		while ((node = rb_next(&es1->rb_node)) != NULL) {
			es1 = rb_entry(node, struct extent_status, rb_node);
			if (es1->es_lblk > end) {
				es1 = NULL;
				break;
			}
			if (ext4_es_is_delayed(es1))
				break;
		}
	}

	if (es1 && ext4_es_is_delayed(es1)) {
		tree->cache_es = es1;
		es->es_lblk = es1->es_lblk;
		es->es_len = es1->es_len;
		es->es_pblk = es1->es_pblk;
	}

	read_unlock(&EXT4_I(inode)->i_es_lock);

	trace_ext4_es_find_delayed_extent_range_exit(inode, es);
}

static int __es_insert_extent(struct inode *inode, struct extent_status *newes)
{
	struct ext4_es_tree *tree = &EXT4_I(inode)->i_es_tree;
	struct rb_node **p = &tree->root.rb_node;
	struct rb_node *parent = NULL;
	struct extent_status *es;

	while (*p) {
		parent = *p;
		es = rb_entry(parent, struct extent_status, rb_node);

		if (newes->es_lblk < es->es_lblk) {
			if (ext4_es_can_be_merged(newes, es)) {
				/*
				 * Here we can modify es_lblk directly
				 * because it isn't overlapped.
				 */
				es->es_lblk = newes->es_lblk;
				es->es_len += newes->es_len;
				if (ext4_es_is_written(es) ||
				    ext4_es_is_unwritten(es))
					ext4_es_store_pblock(es,
							     newes->es_pblk);
				es = ext4_es_try_to_merge_left(inode, es);
				goto out;
			}
			p = &(*p)->rb_left;
		} else if (newes->es_lblk > ext4_es_end(es)) {
			if (ext4_es_can_be_merged(es, newes)) {
				es->es_len += newes->es_len;
				es = ext4_es_try_to_merge_right(inode, es);
				goto out;
			}
			p = &(*p)->rb_right;
		} else {
			BUG_ON(1);
			return -EINVAL;
		}
	}

	es = ext4_es_alloc_extent(inode, newes->es_lblk, newes->es_len,
				  newes->es_pblk);
	if (!es)
		return -ENOMEM;
	rb_link_node(&es->rb_node, parent, p);
	rb_insert_color(&es->rb_node, &tree->root);

out:
	tree->cache_es = es;
	return 0;
}
int ext4_es_lookup_extent(struct inode *inode, ext4_lblk_t lblk,
			  struct extent_status *es)
{
	struct ext4_es_tree *tree;
	struct ext4_es_stats *stats;
	struct extent_status *es1 = NULL;
	struct rb_node *node;
	int found = 0;

	trace_ext4_es_lookup_extent_enter(inode, lblk);
	es_debug("lookup extent in block %u\n", lblk);

	tree = &EXT4_I(inode)->i_es_tree;
	read_lock(&EXT4_I(inode)->i_es_lock);

	/* find extent in cache firstly */
	es->es_lblk = es->es_len = es->es_pblk = 0;
	if (tree->cache_es) {
		es1 = tree->cache_es;
		if (in_range(lblk, es1->es_lblk, es1->es_len)) {
			es_debug("%u cached by [%u/%u)\n",
				 lblk, es1->es_lblk, es1->es_len);
			found = 1;
			goto out;
		}
	}

	node = tree->root.rb_node;
	while (node) {
		es1 = rb_entry(node, struct extent_status, rb_node);
		if (lblk < es1->es_lblk)
			node = node->rb_left;
		else if (lblk > ext4_es_end(es1))
			node = node->rb_right;
		else {
			found = 1;
			break;
		}
	}

out:
	stats = &EXT4_SB(inode->i_sb)->s_es_stats;
	if (found) {
		BUG_ON(!es1);
		es->es_lblk = es1->es_lblk;
		es->es_len = es1->es_len;
		es->es_pblk = es1->es_pblk;
		if (!ext4_es_is_referenced(es1))
			ext4_es_set_referenced(es1);
		stats->es_stats_cache_hits++;
	} else {
		stats->es_stats_cache_misses++;
	}

	read_unlock(&EXT4_I(inode)->i_es_lock);

	trace_ext4_es_lookup_extent_exit(inode, es, found);
	return found;
}
static int __es_remove_extent(struct inode *inode, ext4_lblk_t lblk,
			      ext4_lblk_t end)
{
	struct ext4_es_tree *tree = &EXT4_I(inode)->i_es_tree;
	struct rb_node *node;
	struct extent_status *es;
	struct extent_status orig_es;
	ext4_lblk_t len1, len2;
	ext4_fsblk_t block;
	int err;

retry:
	err = 0;
	es = __es_tree_search(&tree->root, lblk);
	if (!es)
		goto out;
	if (es->es_lblk > end)
		goto out;

	/* Simply invalidate cache_es. */
	tree->cache_es = NULL;

	orig_es.es_lblk = es->es_lblk;
	orig_es.es_len = es->es_len;
	orig_es.es_pblk = es->es_pblk;

	len1 = lblk > es->es_lblk ? lblk - es->es_lblk : 0;
	len2 = ext4_es_end(es) > end ? ext4_es_end(es) - end : 0;
	if (len1 > 0)
		es->es_len = len1;
	if (len2 > 0) {
		if (len1 > 0) {
			struct extent_status newes;

			newes.es_lblk = end + 1;
			newes.es_len = len2;
			block = 0x7FDEADBEEFULL;
			if (ext4_es_is_written(&orig_es) ||
			    ext4_es_is_unwritten(&orig_es))
				block = ext4_es_pblock(&orig_es) +
					orig_es.es_len - len2;
			ext4_es_store_pblock_status(&newes, block,
						    ext4_es_status(&orig_es));
			err = __es_insert_extent(inode, &newes);
			if (err) {
				es->es_lblk = orig_es.es_lblk;
				es->es_len = orig_es.es_len;
				if ((err == -ENOMEM) &&
				    __es_shrink(EXT4_SB(inode->i_sb),
							128, EXT4_I(inode)))
					goto retry;
				goto out;
			}
		} else {
			es->es_lblk = end + 1;
			es->es_len = len2;
			if (ext4_es_is_written(es) ||
			    ext4_es_is_unwritten(es)) {
				block = orig_es.es_pblk + orig_es.es_len - len2;
				ext4_es_store_pblock(es, block);
			}
		}
		goto out;
	}

	if (len1 > 0) {
		node = rb_next(&es->rb_node);
		if (node)
			es = rb_entry(node, struct extent_status, rb_node);
		else
			es = NULL;
	}

	while (es && ext4_es_end(es) <= end) {
		node = rb_next(&es->rb_node);
		rb_erase(&es->rb_node, &tree->root);
		ext4_es_free_extent(inode, es);
		if (!node) {
			es = NULL;
			break;
		}
		es = rb_entry(node, struct extent_status, rb_node);
	}

	if (es && es->es_lblk < end + 1) {
		ext4_lblk_t orig_len = es->es_len;

		len1 = ext4_es_end(es) - end;
		es->es_lblk = end + 1;
		es->es_len = len1;
		if (ext4_es_is_written(es) || ext4_es_is_unwritten(es)) {
			block = es->es_pblk + orig_len - len1;
			ext4_es_store_pblock(es, block);
		}
	}

out:
	return err;
}
static int __es_shrink(struct ext4_sb_info *sbi, int nr_to_scan,
		       struct ext4_inode_info *locked_ei)
{
	struct ext4_inode_info *ei;
	struct ext4_es_stats *es_stats;
	ktime_t start_time;
	u64 scan_time;
	int nr_to_walk;
	int nr_shrunk = 0;
	int retried = 0, nr_skipped = 0;

	es_stats = &sbi->s_es_stats;
	start_time = ktime_get();

retry:
	spin_lock(&sbi->s_es_lock);
	nr_to_walk = sbi->s_es_nr_inode;
	while (nr_to_walk-- > 0) {
		if (list_empty(&sbi->s_es_list)) {
			spin_unlock(&sbi->s_es_lock);
			goto out;
		}
		ei = list_first_entry(&sbi->s_es_list, struct ext4_inode_info,
				      i_es_list);
		/* Move the inode to the tail */
		list_move_tail(&ei->i_es_list, &sbi->s_es_list);

		/*
		 * Normally we try hard to avoid shrinking precached inodes,
		 * but we will as a last resort.
		 */
		if (!retried && ext4_test_inode_state(&ei->vfs_inode,
						EXT4_STATE_EXT_PRECACHED)) {
			nr_skipped++;
			continue;
		}

		if (ei == locked_ei || !write_trylock(&ei->i_es_lock)) {
			nr_skipped++;
			continue;
		}
		/*
		 * Now we hold i_es_lock which protects us from inode reclaim
		 * freeing inode under us
		 */
		spin_unlock(&sbi->s_es_lock);

		nr_shrunk += es_reclaim_extents(ei, &nr_to_scan);
		write_unlock(&ei->i_es_lock);

		if (nr_to_scan <= 0)
			goto out;
		spin_lock(&sbi->s_es_lock);
	}
	spin_unlock(&sbi->s_es_lock);

	/*
	 * If we skipped any inodes, and we weren't able to make any
	 * forward progress, try again to scan precached inodes.
	 */
	if ((nr_shrunk == 0) && nr_skipped && !retried) {
		retried++;
		goto retry;
	}

	if (locked_ei && nr_shrunk == 0)
		nr_shrunk = es_reclaim_extents(locked_ei, &nr_to_scan);

out:
	scan_time = ktime_to_ns(ktime_sub(ktime_get(), start_time));
	if (likely(es_stats->es_stats_scan_time))
		es_stats->es_stats_scan_time = (scan_time +
				es_stats->es_stats_scan_time*3) / 4;
	else
		es_stats->es_stats_scan_time = scan_time;
	if (scan_time > es_stats->es_stats_max_scan_time)
		es_stats->es_stats_max_scan_time = scan_time;
	if (likely(es_stats->es_stats_shrunk))
		es_stats->es_stats_shrunk = (nr_shrunk +
				es_stats->es_stats_shrunk*3) / 4;
	else
		es_stats->es_stats_shrunk = nr_shrunk;

	trace_ext4_es_shrink(sbi->s_sb, nr_shrunk, scan_time,
			     nr_skipped, retried);
	return nr_shrunk;
}
static int es_do_reclaim_extents(struct ext4_inode_info *ei, ext4_lblk_t end,
				 int *nr_to_scan, int *nr_shrunk)
{
	struct inode *inode = &ei->vfs_inode;
	struct ext4_es_tree *tree = &ei->i_es_tree;
	struct extent_status *es;
	struct rb_node *node;

	es = __es_tree_search(&tree->root, ei->i_es_shrink_lblk);
	if (!es)
		goto out_wrap;
	node = &es->rb_node;
	while (*nr_to_scan > 0) {
		if (es->es_lblk > end) {
			ei->i_es_shrink_lblk = end + 1;
			return 0;
		}

		(*nr_to_scan)--;
		node = rb_next(&es->rb_node);
		/*
		 * We can't reclaim delayed extent from status tree because
		 * fiemap, bigallic, and seek_data/hole need to use it.
		 */
		if (ext4_es_is_delayed(es))
			goto next;
		if (ext4_es_is_referenced(es)) {
			ext4_es_clear_referenced(es);
			goto next;
		}

		rb_erase(&es->rb_node, &tree->root);
		ext4_es_free_extent(inode, es);
		(*nr_shrunk)++;
next:
		if (!node)
			goto out_wrap;
		es = rb_entry(node, struct extent_status, rb_node);
	}
	ei->i_es_shrink_lblk = es->es_lblk;
	return 1;
out_wrap:
	ei->i_es_shrink_lblk = 0;
	return 0;
}
