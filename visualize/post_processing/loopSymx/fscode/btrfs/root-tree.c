
int btrfs_find_orphan_roots(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *tree_root = fs_info->tree_root;
	struct extent_buffer *leaf;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct btrfs_key root_key;
	struct btrfs_root *root;
	int err = 0;
	int ret;
	bool can_recover = true;

	if (fs_info->sb->s_flags & MS_RDONLY)
		can_recover = false;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	key.objectid = BTRFS_ORPHAN_OBJECTID;
	key.type = BTRFS_ORPHAN_ITEM_KEY;
	key.offset = 0;

	root_key.type = BTRFS_ROOT_ITEM_KEY;
	root_key.offset = (u64)-1;

	while (1) {
		ret = btrfs_search_slot(NULL, tree_root, &key, path, 0, 0);
		if (ret < 0) {
			err = ret;
			break;
		}

		leaf = path->nodes[0];
		if (path->slots[0] >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(tree_root, path);
			if (ret < 0)
				err = ret;
			if (ret != 0)
				break;
			leaf = path->nodes[0];
		}

		btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
		btrfs_release_path(path);

		if (key.objectid != BTRFS_ORPHAN_OBJECTID ||
		    key.type != BTRFS_ORPHAN_ITEM_KEY)
			break;

		root_key.objectid = key.offset;
		key.offset++;

		/*
		 * The root might have been inserted already, as before we look
		 * for orphan roots, log replay might have happened, which
		 * triggers a transaction commit and qgroup accounting, which
		 * in turn reads and inserts fs roots while doing backref
		 * walking.
		 */
		root = btrfs_lookup_fs_root(fs_info, root_key.objectid);
		if (root) {
			WARN_ON(!test_bit(BTRFS_ROOT_ORPHAN_ITEM_INSERTED,
					  &root->state));
			if (btrfs_root_refs(&root->root_item) == 0)
				btrfs_add_dead_root(root);
			continue;
		}

		root = btrfs_read_fs_root(tree_root, &root_key);
		err = PTR_ERR_OR_ZERO(root);
		if (err && err != -ENOENT) {
			break;
		} else if (err == -ENOENT) {
			struct btrfs_trans_handle *trans;

			btrfs_release_path(path);

			trans = btrfs_join_transaction(tree_root);
			if (IS_ERR(trans)) {
				err = PTR_ERR(trans);
				btrfs_handle_fs_error(fs_info, err,
					    "Failed to start trans to delete orphan item");
				break;
			}
			err = btrfs_del_orphan_item(trans, tree_root,
						    root_key.objectid);
			btrfs_end_transaction(trans);
			if (err) {
				btrfs_handle_fs_error(fs_info, err,
					    "Failed to delete root orphan item");
				break;
			}
			continue;
		}

		err = btrfs_init_fs_root(root);
		if (err) {
			btrfs_free_fs_root(root);
			break;
		}

		set_bit(BTRFS_ROOT_ORPHAN_ITEM_INSERTED, &root->state);

		err = btrfs_insert_fs_root(fs_info, root);
		if (err) {
			BUG_ON(err == -EEXIST);
			btrfs_free_fs_root(root);
			break;
		}

		if (btrfs_root_refs(&root->root_item) == 0)
			btrfs_add_dead_root(root);
	}

	btrfs_free_path(path);
	return err;
}
