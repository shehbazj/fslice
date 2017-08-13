
void __init btrfs_init_lockdep(void)
{
	int i, j;

	/* initialize lockdep class names */
	for (i = 0; i < ARRAY_SIZE(btrfs_lockdep_keysets); i++) {
		struct btrfs_lockdep_keyset *ks = &btrfs_lockdep_keysets[i];

		for (j = 0; j < ARRAY_SIZE(ks->names); j++)
			snprintf(ks->names[j], sizeof(ks->names[j]),
				 "btrfs-%s-%02d", ks->name_stem, j);
	}
}
void btrfs_set_buffer_lockdep_class(u64 objectid, struct extent_buffer *eb,
				    int level)
{
	struct btrfs_lockdep_keyset *ks;

	BUG_ON(level >= ARRAY_SIZE(ks->keys));

	/* find the matching keyset, id 0 is the default entry */
	for (ks = btrfs_lockdep_keysets; ks->id; ks++)
		if (ks->id == objectid)
			break;

	lockdep_set_class_and_name(&eb->lock,
				   &ks->keys[level], ks->names[level]);
}
			   struct extent_buffer *buf,
			   int verify)
{
	u16 csum_size = btrfs_super_csum_size(fs_info->super_copy);
	char *result = NULL;
	unsigned long len;
	unsigned long cur_len;
	unsigned long offset = BTRFS_CSUM_SIZE;
	char *kaddr;
	unsigned long map_start;
	unsigned long map_len;
	int err;
	u32 crc = ~(u32)0;
	unsigned long inline_result;

	len = buf->len - offset;
	while (len > 0) {
		err = map_private_extent_buffer(buf, offset, 32,
					&kaddr, &map_start, &map_len);
		if (err)
			return err;
		cur_len = min(len, map_len - (offset - map_start));
		crc = btrfs_csum_data(kaddr + offset - map_start,
				      crc, cur_len);
		len -= cur_len;
		offset += cur_len;
	}
	if (csum_size > sizeof(inline_result)) {
		result = kzalloc(csum_size, GFP_NOFS);
		if (!result)
			return -ENOMEM;
	} else {
		result = (char *)&inline_result;
	}

	btrfs_csum_final(crc, result);

	if (verify) {
		if (memcmp_extent_buffer(buf, result, 0, csum_size)) {
			u32 val;
			u32 found = 0;
			memcpy(&found, result, csum_size);

			read_extent_buffer(buf, &val, 0, csum_size);
			btrfs_warn_rl(fs_info,
				"%s checksum verify failed on %llu wanted %X found %X level %d",
				fs_info->sb->s_id, buf->start,
				val, found, btrfs_header_level(buf));
			if (result != (char *)&inline_result)
				kfree(result);
			return -EUCLEAN;
		}
	} else {
		write_extent_buffer(buf, result, 0, csum_size);
	}
	if (result != (char *)&inline_result)
		kfree(result);
	return 0;
}
					  struct extent_buffer *eb,
					  u64 parent_transid)
{
	struct extent_io_tree *io_tree;
	int failed = 0;
	int ret;
	int num_copies = 0;
	int mirror_num = 0;
	int failed_mirror = 0;

	clear_bit(EXTENT_BUFFER_CORRUPT, &eb->bflags);
	io_tree = &BTRFS_I(fs_info->btree_inode)->io_tree;
	while (1) {
		ret = read_extent_buffer_pages(io_tree, eb, WAIT_COMPLETE,
					       btree_get_extent, mirror_num);
		if (!ret) {
			if (!verify_parent_transid(io_tree, eb,
						   parent_transid, 0))
				break;
			else
				ret = -EIO;
		}

		/*
		 * This buffer's crc is fine, but its contents are corrupted, so
		 * there is no reason to read the other copies, they won't be
		 * any less wrong.
		 */
		if (test_bit(EXTENT_BUFFER_CORRUPT, &eb->bflags))
			break;

		num_copies = btrfs_num_copies(fs_info,
					      eb->start, eb->len);
		if (num_copies == 1)
			break;

		if (!failed_mirror) {
			failed = 1;
			failed_mirror = eb->read_mirror;
		}

		mirror_num++;
		if (mirror_num == failed_mirror)
			mirror_num++;

		if (mirror_num > num_copies)
			break;
	}

	if (failed && !ret && failed_mirror)
		repair_eb_io_failure(fs_info, eb, failed_mirror);

	return ret;
}
static int check_tree_block_fsid(struct btrfs_fs_info *fs_info,
				 struct extent_buffer *eb)
{
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	u8 fsid[BTRFS_UUID_SIZE];
	int ret = 1;

	read_extent_buffer(eb, fsid, btrfs_header_fsid(), BTRFS_FSID_SIZE);
	while (fs_devices) {
		if (!memcmp(fsid, fs_devices->fsid, BTRFS_FSID_SIZE)) {
			ret = 0;
			break;
		}
		fs_devices = fs_devices->seed;
	}
	return ret;
}
static noinline int check_leaf(struct btrfs_root *root,
			       struct extent_buffer *leaf)
{
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_key key;
	struct btrfs_key leaf_key;
	u32 nritems = btrfs_header_nritems(leaf);
	int slot;

	/*
	 * Extent buffers from a relocation tree have a owner field that
	 * corresponds to the subvolume tree they are based on. So just from an
	 * extent buffer alone we can not find out what is the id of the
	 * corresponding subvolume tree, so we can not figure out if the extent
	 * buffer corresponds to the root of the relocation tree or not. So skip
	 * this check for relocation trees.
	 */
	if (nritems == 0 && !btrfs_header_flag(leaf, BTRFS_HEADER_FLAG_RELOC)) {
		struct btrfs_root *check_root;

		key.objectid = btrfs_header_owner(leaf);
		key.type = BTRFS_ROOT_ITEM_KEY;
		key.offset = (u64)-1;

		check_root = btrfs_get_fs_root(fs_info, &key, false);
		/*
		 * The only reason we also check NULL here is that during
		 * open_ctree() some roots has not yet been set up.
		 */
		if (!IS_ERR_OR_NULL(check_root)) {
			struct extent_buffer *eb;

			eb = btrfs_root_node(check_root);
			/* if leaf is the root, then it's fine */
			if (leaf != eb) {
				CORRUPT("non-root leaf's nritems is 0",
					leaf, check_root, 0);
				free_extent_buffer(eb);
				return -EIO;
			}
			free_extent_buffer(eb);
		}
		return 0;
	}

	if (nritems == 0)
		return 0;

	/* Check the 0 item */
	if (btrfs_item_offset_nr(leaf, 0) + btrfs_item_size_nr(leaf, 0) !=
	    BTRFS_LEAF_DATA_SIZE(fs_info)) {
		CORRUPT("invalid item offset size pair", leaf, root, 0);
		return -EIO;
	}

	/*
	 * Check to make sure each items keys are in the correct order and their
	 * offsets make sense.  We only have to loop through nritems-1 because
	 * we check the current slot against the next slot, which verifies the
	 * next slot's offset+size makes sense and that the current's slot
	 * offset is correct.
	 */
	for (slot = 0; slot < nritems - 1; slot++) {
		btrfs_item_key_to_cpu(leaf, &leaf_key, slot);
		btrfs_item_key_to_cpu(leaf, &key, slot + 1);

		/* Make sure the keys are in the right order */
		if (btrfs_comp_cpu_keys(&leaf_key, &key) >= 0) {
			CORRUPT("bad key order", leaf, root, slot);
			return -EIO;
		}

		/*
		 * Make sure the offset and ends are right, remember that the
		 * item data starts at the end of the leaf and grows towards the
		 * front.
		 */
		if (btrfs_item_offset_nr(leaf, slot) !=
			btrfs_item_end_nr(leaf, slot + 1)) {
			CORRUPT("slot offset bad", leaf, root, slot);
			return -EIO;
		}

		/*
		 * Check to make sure that we don't point outside of the leaf,
		 * just in case all the items are consistent to each other, but
		 * all point outside of the leaf.
		 */
		if (btrfs_item_end_nr(leaf, slot) >
		    BTRFS_LEAF_DATA_SIZE(fs_info)) {
			CORRUPT("slot end outside of leaf", leaf, root, slot);
			return -EIO;
		}
	}

	return 0;
}

static int check_node(struct btrfs_root *root, struct extent_buffer *node)
{
	unsigned long nr = btrfs_header_nritems(node);
	struct btrfs_key key, next_key;
	int slot;
	u64 bytenr;
	int ret = 0;

	if (nr == 0 || nr > BTRFS_NODEPTRS_PER_BLOCK(root->fs_info)) {
		btrfs_crit(root->fs_info,
			   "corrupt node: block %llu root %llu nritems %lu",
			   node->start, root->objectid, nr);
		return -EIO;
	}

	for (slot = 0; slot < nr - 1; slot++) {
		bytenr = btrfs_node_blockptr(node, slot);
		btrfs_node_key_to_cpu(node, &key, slot);
		btrfs_node_key_to_cpu(node, &next_key, slot + 1);

		if (!bytenr) {
			CORRUPT("invalid item slot", node, root, slot);
			ret = -EIO;
			goto out;
		}

		if (btrfs_comp_cpu_keys(&key, &next_key) >= 0) {
			CORRUPT("bad key order", node, root, slot);
			ret = -EIO;
			goto out;
		}
	}
out:
	return ret;
}
			extent_submit_bio_hook_t *submit_bio_start,
			extent_submit_bio_hook_t *submit_bio_done)
{
	struct async_submit_bio *async;

	async = kmalloc(sizeof(*async), GFP_NOFS);
	if (!async)
		return -ENOMEM;

	async->inode = inode;
	async->bio = bio;
	async->mirror_num = mirror_num;
	async->submit_bio_start = submit_bio_start;
	async->submit_bio_done = submit_bio_done;

	btrfs_init_work(&async->work, btrfs_worker_helper, run_one_async_start,
			run_one_async_done, run_one_async_free);

	async->bio_flags = bio_flags;
	async->bio_offset = bio_offset;

	async->error = 0;

	atomic_inc(&fs_info->nr_async_submits);

	if (op_is_sync(bio->bi_opf))
		btrfs_set_work_high_priority(&async->work);

	btrfs_queue_work(fs_info->workers, &async->work);

	while (atomic_read(&fs_info->async_submit_draining) &&
	      atomic_read(&fs_info->nr_async_submits)) {
		wait_event(fs_info->async_submit_wait,
			   (atomic_read(&fs_info->nr_async_submits) == 0));
	}

	return 0;
}

static int cleaner_kthread(void *arg)
{
	struct btrfs_root *root = arg;
	struct btrfs_fs_info *fs_info = root->fs_info;
	int again;
	struct btrfs_trans_handle *trans;

	do {
		again = 0;

		/* Make the cleaner go to sleep early. */
		if (btrfs_need_cleaner_sleep(fs_info))
			goto sleep;

		/*
		 * Do not do anything if we might cause open_ctree() to block
		 * before we have finished mounting the filesystem.
		 */
		if (!test_bit(BTRFS_FS_OPEN, &fs_info->flags))
			goto sleep;

		if (!mutex_trylock(&fs_info->cleaner_mutex))
			goto sleep;

		/*
		 * Avoid the problem that we change the status of the fs
		 * during the above check and trylock.
		 */
		if (btrfs_need_cleaner_sleep(fs_info)) {
			mutex_unlock(&fs_info->cleaner_mutex);
			goto sleep;
		}

		mutex_lock(&fs_info->cleaner_delayed_iput_mutex);
		btrfs_run_delayed_iputs(fs_info);
		mutex_unlock(&fs_info->cleaner_delayed_iput_mutex);

		again = btrfs_clean_one_deleted_snapshot(root);
		mutex_unlock(&fs_info->cleaner_mutex);

		/*
		 * The defragger has dealt with the R/O remount and umount,
		 * needn't do anything special here.
		 */
		btrfs_run_defrag_inodes(fs_info);

		/*
		 * Acquires fs_info->delete_unused_bgs_mutex to avoid racing
		 * with relocation (btrfs_relocate_chunk) and relocation
		 * acquires fs_info->cleaner_mutex (btrfs_relocate_block_group)
		 * after acquiring fs_info->delete_unused_bgs_mutex. So we
		 * can't hold, nor need to, fs_info->cleaner_mutex when deleting
		 * unused block groups.
		 */
		btrfs_delete_unused_bgs(fs_info);
sleep:
		if (!again) {
			set_current_state(TASK_INTERRUPTIBLE);
			if (!kthread_should_stop())
				schedule();
			__set_current_state(TASK_RUNNING);
		}
	} while (!kthread_should_stop());

	/*
	 * Transaction kthread is stopped before us and wakes us up.
	 * However we might have started a new transaction and COWed some
	 * tree blocks when deleting unused block groups for example. So
	 * make sure we commit the transaction we started to have a clean
	 * shutdown when evicting the btree inode - if it has dirty pages
	 * when we do the final iput() on it, eviction will trigger a
	 * writeback for it which will fail with null pointer dereferences
	 * since work queues and other resources were already released and
	 * destroyed by the time the iput/eviction/writeback is made.
	 */
	trans = btrfs_attach_transaction(root);
	if (IS_ERR(trans)) {
		if (PTR_ERR(trans) != -ENOENT)
			btrfs_err(fs_info,
				  "cleaner transaction attach returned %ld",
				  PTR_ERR(trans));
	} else {
		int ret;

		ret = btrfs_commit_transaction(trans);
		if (ret)
			btrfs_err(fs_info,
				  "cleaner open transaction commit returned %d",
				  ret);
	}

	return 0;
}

static int transaction_kthread(void *arg)
{
	struct btrfs_root *root = arg;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_trans_handle *trans;
	struct btrfs_transaction *cur;
	u64 transid;
	unsigned long now;
	unsigned long delay;
	bool cannot_commit;

	do {
		cannot_commit = false;
		delay = HZ * fs_info->commit_interval;
		mutex_lock(&fs_info->transaction_kthread_mutex);

		spin_lock(&fs_info->trans_lock);
		cur = fs_info->running_transaction;
		if (!cur) {
			spin_unlock(&fs_info->trans_lock);
			goto sleep;
		}

		now = get_seconds();
		if (cur->state < TRANS_STATE_BLOCKED &&
		    (now < cur->start_time ||
		     now - cur->start_time < fs_info->commit_interval)) {
			spin_unlock(&fs_info->trans_lock);
			delay = HZ * 5;
			goto sleep;
		}
		transid = cur->transid;
		spin_unlock(&fs_info->trans_lock);

		/* If the file system is aborted, this will always fail. */
		trans = btrfs_attach_transaction(root);
		if (IS_ERR(trans)) {
			if (PTR_ERR(trans) != -ENOENT)
				cannot_commit = true;
			goto sleep;
		}
		if (transid == trans->transid) {
			btrfs_commit_transaction(trans);
		} else {
			btrfs_end_transaction(trans);
		}
sleep:
		wake_up_process(fs_info->cleaner_kthread);
		mutex_unlock(&fs_info->transaction_kthread_mutex);

		if (unlikely(test_bit(BTRFS_FS_STATE_ERROR,
				      &fs_info->fs_state)))
			btrfs_cleanup_transaction(fs_info);
		set_current_state(TASK_INTERRUPTIBLE);
		if (!kthread_should_stop() &&
				(!btrfs_transaction_blocked(fs_info) ||
				 cannot_commit))
			schedule_timeout(delay);
		__set_current_state(TASK_RUNNING);
	} while (!kthread_should_stop());
	return 0;
}
 */
static int find_newest_super_backup(struct btrfs_fs_info *info, u64 newest_gen)
{
	u64 cur;
	int newest_index = -1;
	struct btrfs_root_backup *root_backup;
	int i;

	for (i = 0; i < BTRFS_NUM_BACKUP_ROOTS; i++) {
		root_backup = info->super_copy->super_roots + i;
		cur = btrfs_backup_tree_root_gen(root_backup);
		if (cur == newest_gen)
			newest_index = i;
	}

	/* check to see if we actually wrapped around */
	if (newest_index == BTRFS_NUM_BACKUP_ROOTS - 1) {
		root_backup = info->super_copy->super_roots;
		cur = btrfs_backup_tree_root_gen(root_backup);
		if (cur == newest_gen)
			newest_index = 0;
	}
	return newest_index;
}

void btrfs_free_fs_roots(struct btrfs_fs_info *fs_info)
{
	int ret;
	struct btrfs_root *gang[8];
	int i;

	while (!list_empty(&fs_info->dead_roots)) {
		gang[0] = list_entry(fs_info->dead_roots.next,
				     struct btrfs_root, root_list);
		list_del(&gang[0]->root_list);

		if (test_bit(BTRFS_ROOT_IN_RADIX, &gang[0]->state)) {
			btrfs_drop_and_free_fs_root(fs_info, gang[0]);
		} else {
			free_extent_buffer(gang[0]->node);
			free_extent_buffer(gang[0]->commit_root);
			btrfs_put_fs_root(gang[0]);
		}
	}

	while (1) {
		ret = radix_tree_gang_lookup(&fs_info->fs_roots_radix,
					     (void **)gang, 0,
					     ARRAY_SIZE(gang));
		if (!ret)
			break;
		for (i = 0; i < ret; i++)
			btrfs_drop_and_free_fs_root(fs_info, gang[i]);
	}

	if (test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state)) {
		btrfs_free_log_root_tree(NULL, fs_info);
		btrfs_destroy_pinned_extent(fs_info, fs_info->pinned_extents);
	}
}

struct buffer_head *btrfs_read_dev_super(struct block_device *bdev)
{
	struct buffer_head *bh;
	struct buffer_head *latest = NULL;
	struct btrfs_super_block *super;
	int i;
	u64 transid = 0;
	int ret = -EINVAL;

	/* we would like to check all the supers, but that would make
	 * a btrfs mount succeed after a mkfs from a different FS.
	 * So, we need to add a special mount option to scan for
	 * later supers, using BTRFS_SUPER_MIRROR_MAX instead
	 */
	for (i = 0; i < 1; i++) {
		ret = btrfs_read_dev_one_super(bdev, i, &bh);
		if (ret)
			continue;

		super = (struct btrfs_super_block *)bh->b_data;

		if (!latest || btrfs_super_generation(super) > transid) {
			brelse(latest);
			latest = bh;
			transid = btrfs_super_generation(super);
		} else {
			brelse(bh);
		}
	}

	if (!latest)
		return ERR_PTR(ret);

	return latest;
}
			    struct btrfs_super_block *sb,
			    int wait, int max_mirrors)
{
	struct buffer_head *bh;
	int i;
	int ret;
	int errors = 0;
	u32 crc;
	u64 bytenr;

	if (max_mirrors == 0)
		max_mirrors = BTRFS_SUPER_MIRROR_MAX;

	for (i = 0; i < max_mirrors; i++) {
		bytenr = btrfs_sb_offset(i);
		if (bytenr + BTRFS_SUPER_INFO_SIZE >=
		    device->commit_total_bytes)
			break;

		if (wait) {
			bh = __find_get_block(device->bdev, bytenr / 4096,
					      BTRFS_SUPER_INFO_SIZE);
			if (!bh) {
				errors++;
				continue;
			}
			wait_on_buffer(bh);
			if (!buffer_uptodate(bh))
				errors++;

			/* drop our reference */
			brelse(bh);

			/* drop the reference from the wait == 0 run */
			brelse(bh);
			continue;
		} else {
			btrfs_set_super_bytenr(sb, bytenr);

			crc = ~(u32)0;
			crc = btrfs_csum_data((const char *)sb +
					      BTRFS_CSUM_SIZE, crc,
					      BTRFS_SUPER_INFO_SIZE -
					      BTRFS_CSUM_SIZE);
			btrfs_csum_final(crc, sb->csum);

			/*
			 * one reference for us, and we leave it for the
			 * caller
			 */
			bh = __getblk(device->bdev, bytenr / 4096,
				      BTRFS_SUPER_INFO_SIZE);
			if (!bh) {
				btrfs_err(device->fs_info,
				    "couldn't get super buffer head for bytenr %llu",
				    bytenr);
				errors++;
				continue;
			}

			memcpy(bh->b_data, sb, BTRFS_SUPER_INFO_SIZE);

			/* one reference for submit_bh */
			get_bh(bh);

			set_buffer_uptodate(bh);
			lock_buffer(bh);
			bh->b_end_io = btrfs_end_buffer_write_sync;
			bh->b_private = device;
		}

		/*
		 * we fua the first super.  The others we allow
		 * to go down lazy.
		 */
		if (i == 0) {
			ret = btrfsic_submit_bh(REQ_OP_WRITE,
						REQ_SYNC | REQ_FUA, bh);
		} else {
			ret = btrfsic_submit_bh(REQ_OP_WRITE, REQ_SYNC, bh);
		}
		if (ret)
			errors++;
	}
	return errors < i ? 0 : -1;
}

int btrfs_get_num_tolerated_disk_barrier_failures(u64 flags)
{
	int raid_type;
	int min_tolerated = INT_MAX;

	if ((flags & BTRFS_BLOCK_GROUP_PROFILE_MASK) == 0 ||
	    (flags & BTRFS_AVAIL_ALLOC_BIT_SINGLE))
		min_tolerated = min(min_tolerated,
				    btrfs_raid_array[BTRFS_RAID_SINGLE].
				    tolerated_failures);

	for (raid_type = 0; raid_type < BTRFS_NR_RAID_TYPES; raid_type++) {
		if (raid_type == BTRFS_RAID_SINGLE)
			continue;
		if (!(flags & btrfs_raid_group[raid_type]))
			continue;
		min_tolerated = min(min_tolerated,
				    btrfs_raid_array[raid_type].
				    tolerated_failures);
	}

	if (min_tolerated == INT_MAX) {
		pr_warn("BTRFS: unknown raid flag: %llu", flags);
		min_tolerated = 0;
	}

	return min_tolerated;
}
int btrfs_calc_num_tolerated_disk_barrier_failures(
	struct btrfs_fs_info *fs_info)
{
	struct btrfs_ioctl_space_info space;
	struct btrfs_space_info *sinfo;
	u64 types[] = {BTRFS_BLOCK_GROUP_DATA,
		       BTRFS_BLOCK_GROUP_SYSTEM,
		       BTRFS_BLOCK_GROUP_METADATA,
		       BTRFS_BLOCK_GROUP_DATA | BTRFS_BLOCK_GROUP_METADATA};
	int i;
	int c;
	int num_tolerated_disk_barrier_failures =
		(int)fs_info->fs_devices->num_devices;

	for (i = 0; i < ARRAY_SIZE(types); i++) {
		struct btrfs_space_info *tmp;

		sinfo = NULL;
		rcu_read_lock();
		list_for_each_entry_rcu(tmp, &fs_info->space_info, list) {
			if (tmp->flags == types[i]) {
				sinfo = tmp;
				break;
			}
		}
		rcu_read_unlock();

		if (!sinfo)
			continue;

		down_read(&sinfo->groups_sem);
		for (c = 0; c < BTRFS_NR_RAID_TYPES; c++) {
			u64 flags;

			if (list_empty(&sinfo->block_groups[c]))
				continue;

			btrfs_get_block_group_info(&sinfo->block_groups[c],
						   &space);
			if (space.total_bytes == 0 || space.used_bytes == 0)
				continue;
			flags = space.flags;

			num_tolerated_disk_barrier_failures = min(
				num_tolerated_disk_barrier_failures,
				btrfs_get_num_tolerated_disk_barrier_failures(
					flags));
		}
		up_read(&sinfo->groups_sem);
	}

	return num_tolerated_disk_barrier_failures;
}

int btrfs_cleanup_fs_roots(struct btrfs_fs_info *fs_info)
{
	u64 root_objectid = 0;
	struct btrfs_root *gang[8];
	int i = 0;
	int err = 0;
	unsigned int ret = 0;
	int index;

	while (1) {
		index = srcu_read_lock(&fs_info->subvol_srcu);
		ret = radix_tree_gang_lookup(&fs_info->fs_roots_radix,
					     (void **)gang, root_objectid,
					     ARRAY_SIZE(gang));
		if (!ret) {
			srcu_read_unlock(&fs_info->subvol_srcu, index);
			break;
		}
		root_objectid = gang[ret - 1]->root_key.objectid + 1;

		for (i = 0; i < ret; i++) {
			/* Avoid to grab roots in dead_roots */
			if (btrfs_root_refs(&gang[i]->root_item) == 0) {
				gang[i] = NULL;
				continue;
			}
			/* grab all the search result for later use */
			gang[i] = btrfs_grab_fs_root(gang[i]);
		}
		srcu_read_unlock(&fs_info->subvol_srcu, index);

		for (i = 0; i < ret; i++) {
			if (!gang[i])
				continue;
			root_objectid = gang[i]->root_key.objectid;
			err = btrfs_orphan_cleanup(gang[i]);
			if (err)
				break;
			btrfs_put_fs_root(gang[i]);
		}
		root_objectid++;
	}

	/* release the uncleaned roots due to error */
	for (; i < ret; i++) {
		if (gang[i])
			btrfs_put_fs_root(gang[i]);
	}
	return err;
}

void close_ctree(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root = fs_info->tree_root;
	int ret;

	set_bit(BTRFS_FS_CLOSING_START, &fs_info->flags);

	/* wait for the qgroup rescan worker to stop */
	btrfs_qgroup_wait_for_completion(fs_info, false);

	/* wait for the uuid_scan task to finish */
	down(&fs_info->uuid_tree_rescan_sem);
	/* avoid complains from lockdep et al., set sem back to initial state */
	up(&fs_info->uuid_tree_rescan_sem);

	/* pause restriper - we want to resume on mount */
	btrfs_pause_balance(fs_info);

	btrfs_dev_replace_suspend_for_unmount(fs_info);

	btrfs_scrub_cancel(fs_info);

	/* wait for any defraggers to finish */
	wait_event(fs_info->transaction_wait,
		   (atomic_read(&fs_info->defrag_running) == 0));

	/* clear out the rbtree of defraggable inodes */
	btrfs_cleanup_defrag_inodes(fs_info);

	cancel_work_sync(&fs_info->async_reclaim_work);

	if (!(fs_info->sb->s_flags & MS_RDONLY)) {
		/*
		 * If the cleaner thread is stopped and there are
		 * block groups queued for removal, the deletion will be
		 * skipped when we quit the cleaner thread.
		 */
		btrfs_delete_unused_bgs(fs_info);

		ret = btrfs_commit_super(fs_info);
		if (ret)
			btrfs_err(fs_info, "commit super ret %d", ret);
	}

	if (test_bit(BTRFS_FS_STATE_ERROR, &fs_info->fs_state))
		btrfs_error_commit_super(fs_info);

	kthread_stop(fs_info->transaction_kthread);
	kthread_stop(fs_info->cleaner_kthread);

	set_bit(BTRFS_FS_CLOSING_DONE, &fs_info->flags);

	btrfs_free_qgroup_config(fs_info);

	if (percpu_counter_sum(&fs_info->delalloc_bytes)) {
		btrfs_info(fs_info, "at unmount delalloc count %lld",
		       percpu_counter_sum(&fs_info->delalloc_bytes));
	}

	btrfs_sysfs_remove_mounted(fs_info);
	btrfs_sysfs_remove_fsid(fs_info->fs_devices);

	btrfs_free_fs_roots(fs_info);

	btrfs_put_block_group_cache(fs_info);

	/*
	 * we must make sure there is not any read request to
	 * submit after we stopping all workers.
	 */
	invalidate_inode_pages2(fs_info->btree_inode->i_mapping);
	btrfs_stop_all_workers(fs_info);

	btrfs_free_block_groups(fs_info);

	clear_bit(BTRFS_FS_OPEN, &fs_info->flags);
	free_root_pointers(fs_info, 1);

	iput(fs_info->btree_inode);

#ifdef CONFIG_BTRFS_FS_CHECK_INTEGRITY
	if (btrfs_test_opt(fs_info, CHECK_INTEGRITY))
		btrfsic_unmount(fs_info->fs_devices);
#endif

	btrfs_close_devices(fs_info->fs_devices);
	btrfs_mapping_tree_free(&fs_info->mapping_tree);

	percpu_counter_destroy(&fs_info->dirty_metadata_bytes);
	percpu_counter_destroy(&fs_info->delalloc_bytes);
	percpu_counter_destroy(&fs_info->bio_counter);
	cleanup_srcu_struct(&fs_info->subvol_srcu);

	btrfs_free_stripe_hash_table(fs_info);

	__btrfs_free_block_rsv(root->orphan_block_rsv);
	root->orphan_block_rsv = NULL;

	mutex_lock(&fs_info->chunk_mutex);
	while (!list_empty(&fs_info->pinned_chunks)) {
		struct extent_map *em;

		em = list_first_entry(&fs_info->pinned_chunks,
				      struct extent_map, list);
		list_del_init(&em->list);
		free_extent_map(em);
	}
	mutex_unlock(&fs_info->chunk_mutex);
}

static void btrfs_destroy_all_ordered_extents(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root;
	struct list_head splice;

	INIT_LIST_HEAD(&splice);

	spin_lock(&fs_info->ordered_root_lock);
	list_splice_init(&fs_info->ordered_roots, &splice);
	while (!list_empty(&splice)) {
		root = list_first_entry(&splice, struct btrfs_root,
					ordered_root);
		list_move_tail(&root->ordered_root,
			       &fs_info->ordered_roots);

		spin_unlock(&fs_info->ordered_root_lock);
		btrfs_destroy_ordered_extents(root);

		cond_resched();
		spin_lock(&fs_info->ordered_root_lock);
	}
	spin_unlock(&fs_info->ordered_root_lock);
}
static int btrfs_destroy_delayed_refs(struct btrfs_transaction *trans,
				      struct btrfs_fs_info *fs_info)
{
	struct rb_node *node;
	struct btrfs_delayed_ref_root *delayed_refs;
	struct btrfs_delayed_ref_node *ref;
	int ret = 0;

	delayed_refs = &trans->delayed_refs;

	spin_lock(&delayed_refs->lock);
	if (atomic_read(&delayed_refs->num_entries) == 0) {
		spin_unlock(&delayed_refs->lock);
		btrfs_info(fs_info, "delayed_refs has NO entry");
		return ret;
	}

	while ((node = rb_first(&delayed_refs->href_root)) != NULL) {
		struct btrfs_delayed_ref_head *head;
		struct btrfs_delayed_ref_node *tmp;
		bool pin_bytes = false;

		head = rb_entry(node, struct btrfs_delayed_ref_head,
				href_node);
		if (!mutex_trylock(&head->mutex)) {
			refcount_inc(&head->node.refs);
			spin_unlock(&delayed_refs->lock);

			mutex_lock(&head->mutex);
			mutex_unlock(&head->mutex);
			btrfs_put_delayed_ref(&head->node);
			spin_lock(&delayed_refs->lock);
			continue;
		}
		spin_lock(&head->lock);
		list_for_each_entry_safe_reverse(ref, tmp, &head->ref_list,
						 list) {
			ref->in_tree = 0;
			list_del(&ref->list);
			if (!list_empty(&ref->add_list))
				list_del(&ref->add_list);
			atomic_dec(&delayed_refs->num_entries);
			btrfs_put_delayed_ref(ref);
		}
		if (head->must_insert_reserved)
			pin_bytes = true;
		btrfs_free_delayed_extent_op(head->extent_op);
		delayed_refs->num_heads--;
		if (head->processing == 0)
			delayed_refs->num_heads_ready--;
		atomic_dec(&delayed_refs->num_entries);
		head->node.in_tree = 0;
		rb_erase(&head->href_node, &delayed_refs->href_root);
		spin_unlock(&head->lock);
		spin_unlock(&delayed_refs->lock);
		mutex_unlock(&head->mutex);

		if (pin_bytes)
			btrfs_pin_extent(fs_info, head->node.bytenr,
					 head->node.num_bytes, 1);
		btrfs_put_delayed_ref(&head->node);
		cond_resched();
		spin_lock(&delayed_refs->lock);
	}

	spin_unlock(&delayed_refs->lock);

	return ret;
}

static void btrfs_destroy_delalloc_inodes(struct btrfs_root *root)
{
	struct btrfs_inode *btrfs_inode;
	struct list_head splice;

	INIT_LIST_HEAD(&splice);

	spin_lock(&root->delalloc_lock);
	list_splice_init(&root->delalloc_inodes, &splice);

	while (!list_empty(&splice)) {
		btrfs_inode = list_first_entry(&splice, struct btrfs_inode,
					       delalloc_inodes);

		list_del_init(&btrfs_inode->delalloc_inodes);
		clear_bit(BTRFS_INODE_IN_DELALLOC_LIST,
			  &btrfs_inode->runtime_flags);
		spin_unlock(&root->delalloc_lock);

		btrfs_invalidate_inodes(btrfs_inode->root);

		spin_lock(&root->delalloc_lock);
	}

	spin_unlock(&root->delalloc_lock);
}

static void btrfs_destroy_all_delalloc_inodes(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root;
	struct list_head splice;

	INIT_LIST_HEAD(&splice);

	spin_lock(&fs_info->delalloc_root_lock);
	list_splice_init(&fs_info->delalloc_roots, &splice);
	while (!list_empty(&splice)) {
		root = list_first_entry(&splice, struct btrfs_root,
					 delalloc_root);
		list_del_init(&root->delalloc_root);
		root = btrfs_grab_fs_root(root);
		BUG_ON(!root);
		spin_unlock(&fs_info->delalloc_root_lock);

		btrfs_destroy_delalloc_inodes(root);
		btrfs_put_fs_root(root);

		spin_lock(&fs_info->delalloc_root_lock);
	}
	spin_unlock(&fs_info->delalloc_root_lock);
}
					struct extent_io_tree *dirty_pages,
					int mark)
{
	int ret;
	struct extent_buffer *eb;
	u64 start = 0;
	u64 end;

	while (1) {
		ret = find_first_extent_bit(dirty_pages, start, &start, &end,
					    mark, NULL);
		if (ret)
			break;

		clear_extent_bits(dirty_pages, start, end, mark);
		while (start <= end) {
			eb = find_extent_buffer(fs_info, start);
			start += fs_info->nodesize;
			if (!eb)
				continue;
			wait_on_extent_buffer_writeback(eb);

			if (test_and_clear_bit(EXTENT_BUFFER_DIRTY,
					       &eb->bflags))
				clear_extent_buffer_dirty(eb);
			free_extent_buffer_stale(eb);
		}
	}

	return ret;
}
static int btrfs_destroy_pinned_extent(struct btrfs_fs_info *fs_info,
				       struct extent_io_tree *pinned_extents)
{
	struct extent_io_tree *unpin;
	u64 start;
	u64 end;
	int ret;
	bool loop = true;

	unpin = pinned_extents;
again:
	while (1) {
		ret = find_first_extent_bit(unpin, 0, &start, &end,
					    EXTENT_DIRTY, NULL);
		if (ret)
			break;

		clear_extent_dirty(unpin, start, end);
		btrfs_error_unpin_extent_range(fs_info, start, end);
		cond_resched();
	}

	if (loop) {
		if (unpin == &fs_info->freed_extents[0])
			unpin = &fs_info->freed_extents[1];
		else
			unpin = &fs_info->freed_extents[0];
		loop = false;
		goto again;
	}

	return 0;
}
void btrfs_cleanup_dirty_bgs(struct btrfs_transaction *cur_trans,
			     struct btrfs_fs_info *fs_info)
{
	struct btrfs_block_group_cache *cache;

	spin_lock(&cur_trans->dirty_bgs_lock);
	while (!list_empty(&cur_trans->dirty_bgs)) {
		cache = list_first_entry(&cur_trans->dirty_bgs,
					 struct btrfs_block_group_cache,
					 dirty_list);
		if (!cache) {
			btrfs_err(fs_info, "orphan block group dirty_bgs list");
			spin_unlock(&cur_trans->dirty_bgs_lock);
			return;
		}

		if (!list_empty(&cache->io_list)) {
			spin_unlock(&cur_trans->dirty_bgs_lock);
			list_del_init(&cache->io_list);
			btrfs_cleanup_bg_io(cache);
			spin_lock(&cur_trans->dirty_bgs_lock);
		}

		list_del_init(&cache->dirty_list);
		spin_lock(&cache->lock);
		cache->disk_cache_state = BTRFS_DC_ERROR;
		spin_unlock(&cache->lock);

		spin_unlock(&cur_trans->dirty_bgs_lock);
		btrfs_put_block_group(cache);
		spin_lock(&cur_trans->dirty_bgs_lock);
	}
	spin_unlock(&cur_trans->dirty_bgs_lock);

	while (!list_empty(&cur_trans->io_bgs)) {
		cache = list_first_entry(&cur_trans->io_bgs,
					 struct btrfs_block_group_cache,
					 io_list);
		if (!cache) {
			btrfs_err(fs_info, "orphan block group on io_bgs list");
			return;
		}

		list_del_init(&cache->io_list);
		spin_lock(&cache->lock);
		cache->disk_cache_state = BTRFS_DC_ERROR;
		spin_unlock(&cache->lock);
		btrfs_cleanup_bg_io(cache);
	}
}

static int btrfs_cleanup_transaction(struct btrfs_fs_info *fs_info)
{
	struct btrfs_transaction *t;

	mutex_lock(&fs_info->transaction_kthread_mutex);

	spin_lock(&fs_info->trans_lock);
	while (!list_empty(&fs_info->trans_list)) {
		t = list_first_entry(&fs_info->trans_list,
				     struct btrfs_transaction, list);
		if (t->state >= TRANS_STATE_COMMIT_START) {
			refcount_inc(&t->use_count);
			spin_unlock(&fs_info->trans_lock);
			btrfs_wait_for_commit(fs_info, t->transid);
			btrfs_put_transaction(t);
			spin_lock(&fs_info->trans_lock);
			continue;
		}
		if (t == fs_info->running_transaction) {
			t->state = TRANS_STATE_COMMIT_DOING;
			spin_unlock(&fs_info->trans_lock);
			/*
			 * We wait for 0 num_writers since we don't hold a trans
			 * handle open currently for this transaction.
			 */
			wait_event(t->writer_wait,
				   atomic_read(&t->num_writers) == 0);
		} else {
			spin_unlock(&fs_info->trans_lock);
		}
		btrfs_cleanup_one_transaction(t, fs_info);

		spin_lock(&fs_info->trans_lock);
		if (t == fs_info->running_transaction)
			fs_info->running_transaction = NULL;
		list_del_init(&t->list);
		spin_unlock(&fs_info->trans_lock);

		btrfs_put_transaction(t);
		trace_btrfs_transaction_commit(fs_info->tree_root);
		spin_lock(&fs_info->trans_lock);
	}
	spin_unlock(&fs_info->trans_lock);
	btrfs_destroy_all_ordered_extents(fs_info);
	btrfs_destroy_delayed_inodes(fs_info);
	btrfs_assert_delayed_root_empty(fs_info);
	btrfs_destroy_pinned_extent(fs_info, fs_info->pinned_extents);
	btrfs_destroy_all_delalloc_inodes(fs_info);
	mutex_unlock(&fs_info->transaction_kthread_mutex);

	return 0;
}
