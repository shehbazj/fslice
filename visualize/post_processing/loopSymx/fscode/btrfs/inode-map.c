
static int caching_kthread(void *data)
{
	struct btrfs_root *root = data;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_free_space_ctl *ctl = root->free_ino_ctl;
	struct btrfs_key key;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	u64 last = (u64)-1;
	int slot;
	int ret;

	if (!btrfs_test_opt(fs_info, INODE_MAP_CACHE))
		return 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	/* Since the commit root is read-only, we can safely skip locking. */
	path->skip_locking = 1;
	path->search_commit_root = 1;
	path->reada = READA_FORWARD;

	key.objectid = BTRFS_FIRST_FREE_OBJECTID;
	key.offset = 0;
	key.type = BTRFS_INODE_ITEM_KEY;
again:
	/* need to make sure the commit_root doesn't disappear */
	down_read(&fs_info->commit_root_sem);

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;

	while (1) {
		if (btrfs_fs_closing(fs_info))
			goto out;

		leaf = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0)
				goto out;
			else if (ret > 0)
				break;

			if (need_resched() ||
			    btrfs_transaction_in_commit(fs_info)) {
				leaf = path->nodes[0];

				if (WARN_ON(btrfs_header_nritems(leaf) == 0))
					break;

				/*
				 * Save the key so we can advances forward
				 * in the next search.
				 */
				btrfs_item_key_to_cpu(leaf, &key, 0);
				btrfs_release_path(path);
				root->ino_cache_progress = last;
				up_read(&fs_info->commit_root_sem);
				schedule_timeout(1);
				goto again;
			} else
				continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, slot);

		if (key.type != BTRFS_INODE_ITEM_KEY)
			goto next;

		if (key.objectid >= root->highest_objectid)
			break;

		if (last != (u64)-1 && last + 1 != key.objectid) {
			__btrfs_add_free_space(fs_info, ctl, last + 1,
					       key.objectid - last - 1);
			wake_up(&root->ino_cache_wait);
		}

		last = key.objectid;
next:
		path->slots[0]++;
	}

	if (last < root->highest_objectid - 1) {
		__btrfs_add_free_space(fs_info, ctl, last + 1,
				       root->highest_objectid - last - 1);
	}

	spin_lock(&root->ino_cache_lock);
	root->ino_cache_state = BTRFS_CACHE_FINISHED;
	spin_unlock(&root->ino_cache_lock);

	root->ino_cache_progress = (u64)-1;
	btrfs_unpin_free_ino(root);
out:
	wake_up(&root->ino_cache_wait);
	up_read(&fs_info->commit_root_sem);

	btrfs_free_path(path);

	return ret;
}
 */
void btrfs_unpin_free_ino(struct btrfs_root *root)
{
	struct btrfs_free_space_ctl *ctl = root->free_ino_ctl;
	struct rb_root *rbroot = &root->free_ino_pinned->free_space_offset;
	spinlock_t *rbroot_lock = &root->free_ino_pinned->tree_lock;
	struct btrfs_free_space *info;
	struct rb_node *n;
	u64 count;

	if (!btrfs_test_opt(root->fs_info, INODE_MAP_CACHE))
		return;

	while (1) {
		bool add_to_ctl = true;

		spin_lock(rbroot_lock);
		n = rb_first(rbroot);
		if (!n) {
			spin_unlock(rbroot_lock);
			break;
		}

		info = rb_entry(n, struct btrfs_free_space, offset_index);
		BUG_ON(info->bitmap); /* Logic error */

		if (info->offset > root->ino_cache_progress)
			add_to_ctl = false;
		else if (info->offset + info->bytes > root->ino_cache_progress)
			count = root->ino_cache_progress - info->offset + 1;
		else
			count = info->bytes;

		rb_erase(&info->offset_index, rbroot);
		spin_unlock(rbroot_lock);
		if (add_to_ctl)
			__btrfs_add_free_space(root->fs_info, ctl,
					       info->offset, count);
		kmem_cache_free(btrfs_free_space_cachep, info);
	}
}
