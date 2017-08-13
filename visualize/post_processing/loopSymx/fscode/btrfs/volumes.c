
static void free_fs_devices(struct btrfs_fs_devices *fs_devices)
{
	struct btrfs_device *device;
	WARN_ON(fs_devices->opened);
	while (!list_empty(&fs_devices->devices)) {
		device = list_entry(fs_devices->devices.next,
				    struct btrfs_device, dev_list);
		list_del(&device->dev_list);
		rcu_string_free(device->name);
		kfree(device);
	}
	kfree(fs_devices);
}

void btrfs_cleanup_fs_uuids(void)
{
	struct btrfs_fs_devices *fs_devices;

	while (!list_empty(&fs_uuids)) {
		fs_devices = list_entry(fs_uuids.next,
					struct btrfs_fs_devices, list);
		list_del(&fs_devices->list);
		free_fs_devices(fs_devices);
	}
}
 */
static noinline void run_scheduled_bios(struct btrfs_device *device)
{
	struct btrfs_fs_info *fs_info = device->fs_info;
	struct bio *pending;
	struct backing_dev_info *bdi;
	struct btrfs_pending_bios *pending_bios;
	struct bio *tail;
	struct bio *cur;
	int again = 0;
	unsigned long num_run;
	unsigned long batch_run = 0;
	unsigned long limit;
	unsigned long last_waited = 0;
	int force_reg = 0;
	int sync_pending = 0;
	struct blk_plug plug;

	/*
	 * this function runs all the bios we've collected for
	 * a particular device.  We don't want to wander off to
	 * another device without first sending all of these down.
	 * So, setup a plug here and finish it off before we return
	 */
	blk_start_plug(&plug);

	bdi = device->bdev->bd_bdi;
	limit = btrfs_async_submit_limit(fs_info);
	limit = limit * 2 / 3;

loop:
	spin_lock(&device->io_lock);

loop_lock:
	num_run = 0;

	/* take all the bios off the list at once and process them
	 * later on (without the lock held).  But, remember the
	 * tail and other pointers so the bios can be properly reinserted
	 * into the list if we hit congestion
	 */
	if (!force_reg && device->pending_sync_bios.head) {
		pending_bios = &device->pending_sync_bios;
		force_reg = 1;
	} else {
		pending_bios = &device->pending_bios;
		force_reg = 0;
	}

	pending = pending_bios->head;
	tail = pending_bios->tail;
	WARN_ON(pending && !tail);

	/*
	 * if pending was null this time around, no bios need processing
	 * at all and we can stop.  Otherwise it'll loop back up again
	 * and do an additional check so no bios are missed.
	 *
	 * device->running_pending is used to synchronize with the
	 * schedule_bio code.
	 */
	if (device->pending_sync_bios.head == NULL &&
	    device->pending_bios.head == NULL) {
		again = 0;
		device->running_pending = 0;
	} else {
		again = 1;
		device->running_pending = 1;
	}

	pending_bios->head = NULL;
	pending_bios->tail = NULL;

	spin_unlock(&device->io_lock);

	while (pending) {

		rmb();
		/* we want to work on both lists, but do more bios on the
		 * sync list than the regular list
		 */
		if ((num_run > 32 &&
		    pending_bios != &device->pending_sync_bios &&
		    device->pending_sync_bios.head) ||
		   (num_run > 64 && pending_bios == &device->pending_sync_bios &&
		    device->pending_bios.head)) {
			spin_lock(&device->io_lock);
			requeue_list(pending_bios, pending, tail);
			goto loop_lock;
		}

		cur = pending;
		pending = pending->bi_next;
		cur->bi_next = NULL;

		/*
		 * atomic_dec_return implies a barrier for waitqueue_active
		 */
		if (atomic_dec_return(&fs_info->nr_async_bios) < limit &&
		    waitqueue_active(&fs_info->async_submit_wait))
			wake_up(&fs_info->async_submit_wait);

		BUG_ON(atomic_read(&cur->__bi_cnt) == 0);

		/*
		 * if we're doing the sync list, record that our
		 * plug has some sync requests on it
		 *
		 * If we're doing the regular list and there are
		 * sync requests sitting around, unplug before
		 * we add more
		 */
		if (pending_bios == &device->pending_sync_bios) {
			sync_pending = 1;
		} else if (sync_pending) {
			blk_finish_plug(&plug);
			blk_start_plug(&plug);
			sync_pending = 0;
		}

		btrfsic_submit_bio(cur);
		num_run++;
		batch_run++;

		cond_resched();

		/*
		 * we made progress, there is more work to do and the bdi
		 * is now congested.  Back off and let other work structs
		 * run instead
		 */
		if (pending && bdi_write_congested(bdi) && batch_run > 8 &&
		    fs_info->fs_devices->open_devices > 1) {
			struct io_context *ioc;

			ioc = current->io_context;

			/*
			 * the main goal here is that we don't want to
			 * block if we're going to be able to submit
			 * more requests without blocking.
			 *
			 * This code does two great things, it pokes into
			 * the elevator code from a filesystem _and_
			 * it makes assumptions about how batching works.
			 */
			if (ioc && ioc->nr_batch_requests > 0 &&
			    time_before(jiffies, ioc->last_waited + HZ/50UL) &&
			    (last_waited == 0 ||
			     ioc->last_waited == last_waited)) {
				/*
				 * we want to go through our batch of
				 * requests and stop.  So, we copy out
				 * the ioc->last_waited time and test
				 * against it before looping
				 */
				last_waited = ioc->last_waited;
				cond_resched();
				continue;
			}
			spin_lock(&device->io_lock);
			requeue_list(pending_bios, pending, tail);
			device->running_pending = 1;

			spin_unlock(&device->io_lock);
			btrfs_queue_work(fs_info->submit_workers,
					 &device->work);
			goto done;
		}
		/* unplug every 64 requests just for good measure */
		if (batch_run % 64 == 0) {
			blk_finish_plug(&plug);
			blk_start_plug(&plug);
			sync_pending = 0;
		}
	}

	cond_resched();
	if (again)
		goto loop;

	spin_lock(&device->io_lock);
	if (device->pending_bios.head || device->pending_sync_bios.head)
		goto loop_lock;
	spin_unlock(&device->io_lock);

done:
	blk_finish_plug(&plug);
}

static int __btrfs_close_devices(struct btrfs_fs_devices *fs_devices)
{
	struct btrfs_device *device, *tmp;
	struct list_head pending_put;

	INIT_LIST_HEAD(&pending_put);

	if (--fs_devices->opened > 0)
		return 0;

	mutex_lock(&fs_devices->device_list_mutex);
	list_for_each_entry_safe(device, tmp, &fs_devices->devices, dev_list) {
		btrfs_prepare_close_one_device(device);
		list_add(&device->dev_list, &pending_put);
	}
	mutex_unlock(&fs_devices->device_list_mutex);

	/*
	 * btrfs_show_devname() is using the device_list_mutex,
	 * sometimes call to blkdev_put() leads vfs calling
	 * into this func. So do put outside of device_list_mutex,
	 * as of now.
	 */
	while (!list_empty(&pending_put)) {
		device = list_first_entry(&pending_put,
				struct btrfs_device, dev_list);
		list_del(&device->dev_list);
		btrfs_close_bdev(device);
		call_rcu(&device->rcu, free_device);
	}

	WARN_ON(fs_devices->open_devices);
	WARN_ON(fs_devices->rw_devices);
	fs_devices->opened = 0;
	fs_devices->seeding = 0;

	return 0;
}

int btrfs_close_devices(struct btrfs_fs_devices *fs_devices)
{
	struct btrfs_fs_devices *seed_devices = NULL;
	int ret;

	mutex_lock(&uuid_mutex);
	ret = __btrfs_close_devices(fs_devices);
	if (!fs_devices->opened) {
		seed_devices = fs_devices->seed;
		fs_devices->seed = NULL;
	}
	mutex_unlock(&uuid_mutex);

	while (seed_devices) {
		fs_devices = seed_devices;
		seed_devices = fs_devices->seed;
		__btrfs_close_devices(fs_devices);
		free_fs_devices(fs_devices);
	}
	/*
	 * Wait for rcu kworkers under __btrfs_close_devices
	 * to finish all blkdev_puts so device is really
	 * free when umount is done.
	 */
	rcu_barrier();
	return ret;
}
int btrfs_account_dev_extents_size(struct btrfs_device *device, u64 start,
				   u64 end, u64 *length)
{
	struct btrfs_key key;
	struct btrfs_root *root = device->fs_info->dev_root;
	struct btrfs_dev_extent *dev_extent;
	struct btrfs_path *path;
	u64 extent_end;
	int ret;
	int slot;
	struct extent_buffer *l;

	*length = 0;

	if (start >= device->total_bytes || device->is_tgtdev_for_dev_replace)
		return 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	path->reada = READA_FORWARD;

	key.objectid = device->devid;
	key.offset = start;
	key.type = BTRFS_DEV_EXTENT_KEY;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret > 0) {
		ret = btrfs_previous_item(root, path, key.objectid, key.type);
		if (ret < 0)
			goto out;
	}

	while (1) {
		l = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(l)) {
			ret = btrfs_next_leaf(root, path);
			if (ret == 0)
				continue;
			if (ret < 0)
				goto out;

			break;
		}
		btrfs_item_key_to_cpu(l, &key, slot);

		if (key.objectid < device->devid)
			goto next;

		if (key.objectid > device->devid)
			break;

		if (key.type != BTRFS_DEV_EXTENT_KEY)
			goto next;

		dev_extent = btrfs_item_ptr(l, slot, struct btrfs_dev_extent);
		extent_end = key.offset + btrfs_dev_extent_length(l,
								  dev_extent);
		if (key.offset <= start && extent_end > end) {
			*length = end - start + 1;
			break;
		} else if (key.offset <= start && extent_end > start)
			*length += extent_end - start;
		else if (key.offset > start && extent_end <= end)
			*length += extent_end - key.offset;
		else if (key.offset > start && key.offset <= end) {
			*length += end - key.offset + 1;
			break;
		} else if (key.offset > end)
			break;

next:
		path->slots[0]++;
	}
	ret = 0;
out:
	btrfs_free_path(path);
	return ret;
}
				   struct btrfs_device *device,
				   u64 *start, u64 len)
{
	struct btrfs_fs_info *fs_info = device->fs_info;
	struct extent_map *em;
	struct list_head *search_list = &fs_info->pinned_chunks;
	int ret = 0;
	u64 physical_start = *start;

	if (transaction)
		search_list = &transaction->pending_chunks;
again:
	list_for_each_entry(em, search_list, list) {
		struct map_lookup *map;
		int i;

		map = em->map_lookup;
		for (i = 0; i < map->num_stripes; i++) {
			u64 end;

			if (map->stripes[i].dev != device)
				continue;
			if (map->stripes[i].physical >= physical_start + len ||
			    map->stripes[i].physical + em->orig_block_len <=
			    physical_start)
				continue;
			/*
			 * Make sure that while processing the pinned list we do
			 * not override our *start with a lower value, because
			 * we can have pinned chunks that fall within this
			 * device hole and that have lower physical addresses
			 * than the pending chunks we processed before. If we
			 * do not take this special care we can end up getting
			 * 2 pending chunks that start at the same physical
			 * device offsets because the end offset of a pinned
			 * chunk can be equal to the start offset of some
			 * pending chunk.
			 */
			end = map->stripes[i].physical + em->orig_block_len;
			if (end > *start) {
				*start = end;
				ret = 1;
			}
		}
	}
	if (search_list != &fs_info->pinned_chunks) {
		search_list = &fs_info->pinned_chunks;
		goto again;
	}

	return ret;
}
			       struct btrfs_device *device, u64 num_bytes,
			       u64 search_start, u64 *start, u64 *len)
{
	struct btrfs_fs_info *fs_info = device->fs_info;
	struct btrfs_root *root = fs_info->dev_root;
	struct btrfs_key key;
	struct btrfs_dev_extent *dev_extent;
	struct btrfs_path *path;
	u64 hole_size;
	u64 max_hole_start;
	u64 max_hole_size;
	u64 extent_end;
	u64 search_end = device->total_bytes;
	int ret;
	int slot;
	struct extent_buffer *l;
	u64 min_search_start;

	/*
	 * We don't want to overwrite the superblock on the drive nor any area
	 * used by the boot loader (grub for example), so we make sure to start
	 * at an offset of at least 1MB.
	 */
	min_search_start = max(fs_info->alloc_start, 1024ull * 1024);
	search_start = max(search_start, min_search_start);

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	max_hole_start = search_start;
	max_hole_size = 0;

again:
	if (search_start >= search_end || device->is_tgtdev_for_dev_replace) {
		ret = -ENOSPC;
		goto out;
	}

	path->reada = READA_FORWARD;
	path->search_commit_root = 1;
	path->skip_locking = 1;

	key.objectid = device->devid;
	key.offset = search_start;
	key.type = BTRFS_DEV_EXTENT_KEY;

	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret > 0) {
		ret = btrfs_previous_item(root, path, key.objectid, key.type);
		if (ret < 0)
			goto out;
	}

	while (1) {
		l = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(l)) {
			ret = btrfs_next_leaf(root, path);
			if (ret == 0)
				continue;
			if (ret < 0)
				goto out;

			break;
		}
		btrfs_item_key_to_cpu(l, &key, slot);

		if (key.objectid < device->devid)
			goto next;

		if (key.objectid > device->devid)
			break;

		if (key.type != BTRFS_DEV_EXTENT_KEY)
			goto next;

		if (key.offset > search_start) {
			hole_size = key.offset - search_start;

			/*
			 * Have to check before we set max_hole_start, otherwise
			 * we could end up sending back this offset anyway.
			 */
			if (contains_pending_extent(transaction, device,
						    &search_start,
						    hole_size)) {
				if (key.offset >= search_start) {
					hole_size = key.offset - search_start;
				} else {
					WARN_ON_ONCE(1);
					hole_size = 0;
				}
			}

			if (hole_size > max_hole_size) {
				max_hole_start = search_start;
				max_hole_size = hole_size;
			}

			/*
			 * If this free space is greater than which we need,
			 * it must be the max free space that we have found
			 * until now, so max_hole_start must point to the start
			 * of this free space and the length of this free space
			 * is stored in max_hole_size. Thus, we return
			 * max_hole_start and max_hole_size and go back to the
			 * caller.
			 */
			if (hole_size >= num_bytes) {
				ret = 0;
				goto out;
			}
		}

		dev_extent = btrfs_item_ptr(l, slot, struct btrfs_dev_extent);
		extent_end = key.offset + btrfs_dev_extent_length(l,
								  dev_extent);
		if (extent_end > search_start)
			search_start = extent_end;
next:
		path->slots[0]++;
		cond_resched();
	}

	/*
	 * At this point, search_start should be the end of
	 * allocated dev extents, and when shrinking the device,
	 * search_end may be smaller than search_start.
	 */
	if (search_end > search_start) {
		hole_size = search_end - search_start;

		if (contains_pending_extent(transaction, device, &search_start,
					    hole_size)) {
			btrfs_release_path(path);
			goto again;
		}

		if (hole_size > max_hole_size) {
			max_hole_start = search_start;
			max_hole_size = hole_size;
		}
	}

	/* See above. */
	if (max_hole_size < num_bytes)
		ret = -ENOSPC;
	else
		ret = 0;

out:
	btrfs_free_path(path);
	*start = max_hole_start;
	if (len)
		*len = max_hole_size;
	return ret;
}
static int btrfs_check_raid_min_devices(struct btrfs_fs_info *fs_info,
		u64 num_devices)
{
	u64 all_avail;
	unsigned seq;
	int i;

	do {
		seq = read_seqbegin(&fs_info->profiles_lock);

		all_avail = fs_info->avail_data_alloc_bits |
			    fs_info->avail_system_alloc_bits |
			    fs_info->avail_metadata_alloc_bits;
	} while (read_seqretry(&fs_info->profiles_lock, seq));

	for (i = 0; i < BTRFS_NR_RAID_TYPES; i++) {
		if (!(all_avail & btrfs_raid_group[i]))
			continue;

		if (num_devices < btrfs_raid_array[i].devs_min) {
			int ret = btrfs_raid_mindev_error[i];

			if (ret)
				return ret;
		}
	}

	return 0;
}
int btrfs_rm_device(struct btrfs_fs_info *fs_info, const char *device_path,
		u64 devid)
{
	struct btrfs_device *device;
	struct btrfs_fs_devices *cur_devices;
	u64 num_devices;
	int ret = 0;
	bool clear_super = false;

	mutex_lock(&uuid_mutex);

	num_devices = fs_info->fs_devices->num_devices;
	btrfs_dev_replace_lock(&fs_info->dev_replace, 0);
	if (btrfs_dev_replace_is_ongoing(&fs_info->dev_replace)) {
		WARN_ON(num_devices < 1);
		num_devices--;
	}
	btrfs_dev_replace_unlock(&fs_info->dev_replace, 0);

	ret = btrfs_check_raid_min_devices(fs_info, num_devices - 1);
	if (ret)
		goto out;

	ret = btrfs_find_device_by_devspec(fs_info, devid, device_path,
					   &device);
	if (ret)
		goto out;

	if (device->is_tgtdev_for_dev_replace) {
		ret = BTRFS_ERROR_DEV_TGT_REPLACE;
		goto out;
	}

	if (device->writeable && fs_info->fs_devices->rw_devices == 1) {
		ret = BTRFS_ERROR_DEV_ONLY_WRITABLE;
		goto out;
	}

	if (device->writeable) {
		mutex_lock(&fs_info->chunk_mutex);
		list_del_init(&device->dev_alloc_list);
		device->fs_devices->rw_devices--;
		mutex_unlock(&fs_info->chunk_mutex);
		clear_super = true;
	}

	mutex_unlock(&uuid_mutex);
	ret = btrfs_shrink_device(device, 0);
	mutex_lock(&uuid_mutex);
	if (ret)
		goto error_undo;

	/*
	 * TODO: the superblock still includes this device in its num_devices
	 * counter although write_all_supers() is not locked out. This
	 * could give a filesystem state which requires a degraded mount.
	 */
	ret = btrfs_rm_dev_item(fs_info, device);
	if (ret)
		goto error_undo;

	device->in_fs_metadata = 0;
	btrfs_scrub_cancel_dev(fs_info, device);

	/*
	 * the device list mutex makes sure that we don't change
	 * the device list while someone else is writing out all
	 * the device supers. Whoever is writing all supers, should
	 * lock the device list mutex before getting the number of
	 * devices in the super block (super_copy). Conversely,
	 * whoever updates the number of devices in the super block
	 * (super_copy) should hold the device list mutex.
	 */

	cur_devices = device->fs_devices;
	mutex_lock(&fs_info->fs_devices->device_list_mutex);
	list_del_rcu(&device->dev_list);

	device->fs_devices->num_devices--;
	device->fs_devices->total_devices--;

	if (device->missing)
		device->fs_devices->missing_devices--;

	btrfs_assign_next_active_device(fs_info, device, NULL);

	if (device->bdev) {
		device->fs_devices->open_devices--;
		/* remove sysfs entry */
		btrfs_sysfs_rm_device_link(fs_info->fs_devices, device);
	}

	num_devices = btrfs_super_num_devices(fs_info->super_copy) - 1;
	btrfs_set_super_num_devices(fs_info->super_copy, num_devices);
	mutex_unlock(&fs_info->fs_devices->device_list_mutex);

	/*
	 * at this point, the device is zero sized and detached from
	 * the devices list.  All that's left is to zero out the old
	 * supers and free the device.
	 */
	if (device->writeable)
		btrfs_scratch_superblocks(device->bdev, device->name->str);

	btrfs_close_bdev(device);
	call_rcu(&device->rcu, free_device);

	if (cur_devices->open_devices == 0) {
		struct btrfs_fs_devices *fs_devices;
		fs_devices = fs_info->fs_devices;
		while (fs_devices) {
			if (fs_devices->seed == cur_devices) {
				fs_devices->seed = cur_devices->seed;
				break;
			}
			fs_devices = fs_devices->seed;
		}
		cur_devices->seed = NULL;
		__btrfs_close_devices(cur_devices);
		free_fs_devices(cur_devices);
	}

	fs_info->num_tolerated_disk_barrier_failures =
		btrfs_calc_num_tolerated_disk_barrier_failures(fs_info);

out:
	mutex_unlock(&uuid_mutex);
	return ret;

error_undo:
	if (device->writeable) {
		mutex_lock(&fs_info->chunk_mutex);
		list_add(&device->dev_alloc_list,
			 &fs_info->fs_devices->alloc_list);
		device->fs_devices->rw_devices++;
		mutex_unlock(&fs_info->chunk_mutex);
	}
	goto out;
}
void btrfs_rm_dev_replace_free_srcdev(struct btrfs_fs_info *fs_info,
				      struct btrfs_device *srcdev)
{
	struct btrfs_fs_devices *fs_devices = srcdev->fs_devices;

	if (srcdev->writeable) {
		/* zero out the old super if it is writable */
		btrfs_scratch_superblocks(srcdev->bdev, srcdev->name->str);
	}

	btrfs_close_bdev(srcdev);

	call_rcu(&srcdev->rcu, free_device);

	/*
	 * unless fs_devices is seed fs, num_devices shouldn't go
	 * zero
	 */
	BUG_ON(!fs_devices->num_devices && !fs_devices->seeding);

	/* if this is no devs we rather delete the fs_devices */
	if (!fs_devices->num_devices) {
		struct btrfs_fs_devices *tmp_fs_devices;

		tmp_fs_devices = fs_info->fs_devices;
		while (tmp_fs_devices) {
			if (tmp_fs_devices->seed == fs_devices) {
				tmp_fs_devices->seed = fs_devices->seed;
				break;
			}
			tmp_fs_devices = tmp_fs_devices->seed;
		}
		fs_devices->seed = NULL;
		__btrfs_close_devices(fs_devices);
		free_fs_devices(fs_devices);
	}
}
static int btrfs_finish_sprout(struct btrfs_trans_handle *trans,
			       struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root = fs_info->chunk_root;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_dev_item *dev_item;
	struct btrfs_device *device;
	struct btrfs_key key;
	u8 fs_uuid[BTRFS_UUID_SIZE];
	u8 dev_uuid[BTRFS_UUID_SIZE];
	u64 devid;
	int ret;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	key.objectid = BTRFS_DEV_ITEMS_OBJECTID;
	key.offset = 0;
	key.type = BTRFS_DEV_ITEM_KEY;

	while (1) {
		ret = btrfs_search_slot(trans, root, &key, path, 0, 1);
		if (ret < 0)
			goto error;

		leaf = path->nodes[0];
next_slot:
		if (path->slots[0] >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret > 0)
				break;
			if (ret < 0)
				goto error;
			leaf = path->nodes[0];
			btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
			btrfs_release_path(path);
			continue;
		}

		btrfs_item_key_to_cpu(leaf, &key, path->slots[0]);
		if (key.objectid != BTRFS_DEV_ITEMS_OBJECTID ||
		    key.type != BTRFS_DEV_ITEM_KEY)
			break;

		dev_item = btrfs_item_ptr(leaf, path->slots[0],
					  struct btrfs_dev_item);
		devid = btrfs_device_id(leaf, dev_item);
		read_extent_buffer(leaf, dev_uuid, btrfs_device_uuid(dev_item),
				   BTRFS_UUID_SIZE);
		read_extent_buffer(leaf, fs_uuid, btrfs_device_fsid(dev_item),
				   BTRFS_UUID_SIZE);
		device = btrfs_find_device(fs_info, devid, dev_uuid, fs_uuid);
		BUG_ON(!device); /* Logic error */

		if (device->fs_devices->seeding) {
			btrfs_set_device_generation(leaf, dev_item,
						    device->generation);
			btrfs_mark_buffer_dirty(leaf);
		}

		path->slots[0]++;
		goto next_slot;
	}
	ret = 0;
error:
	btrfs_free_path(path);
	return ret;
}
static int btrfs_del_sys_chunk(struct btrfs_fs_info *fs_info,
			       u64 chunk_objectid, u64 chunk_offset)
{
	struct btrfs_super_block *super_copy = fs_info->super_copy;
	struct btrfs_disk_key *disk_key;
	struct btrfs_chunk *chunk;
	u8 *ptr;
	int ret = 0;
	u32 num_stripes;
	u32 array_size;
	u32 len = 0;
	u32 cur;
	struct btrfs_key key;

	mutex_lock(&fs_info->chunk_mutex);
	array_size = btrfs_super_sys_array_size(super_copy);

	ptr = super_copy->sys_chunk_array;
	cur = 0;

	while (cur < array_size) {
		disk_key = (struct btrfs_disk_key *)ptr;
		btrfs_disk_key_to_cpu(&key, disk_key);

		len = sizeof(*disk_key);

		if (key.type == BTRFS_CHUNK_ITEM_KEY) {
			chunk = (struct btrfs_chunk *)(ptr + len);
			num_stripes = btrfs_stack_chunk_num_stripes(chunk);
			len += btrfs_chunk_item_size(num_stripes);
		} else {
			ret = -EIO;
			break;
		}
		if (key.objectid == chunk_objectid &&
		    key.offset == chunk_offset) {
			memmove(ptr, ptr + len, array_size - (cur + len));
			array_size -= len;
			btrfs_set_super_sys_array_size(super_copy, array_size);
		} else {
			ptr += len;
			cur += len;
		}
	}
	mutex_unlock(&fs_info->chunk_mutex);
	return ret;
}
int btrfs_remove_chunk(struct btrfs_trans_handle *trans,
		       struct btrfs_fs_info *fs_info, u64 chunk_offset)
{
	struct extent_map *em;
	struct map_lookup *map;
	u64 dev_extent_len = 0;
	u64 chunk_objectid = BTRFS_FIRST_CHUNK_TREE_OBJECTID;
	int i, ret = 0;
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;

	em = get_chunk_map(fs_info, chunk_offset, 1);
	if (IS_ERR(em)) {
		/*
		 * This is a logic error, but we don't want to just rely on the
		 * user having built with ASSERT enabled, so if ASSERT doesn't
		 * do anything we still error out.
		 */
		ASSERT(0);
		return PTR_ERR(em);
	}
	map = em->map_lookup;
	mutex_lock(&fs_info->chunk_mutex);
	check_system_chunk(trans, fs_info, map->type);
	mutex_unlock(&fs_info->chunk_mutex);

	/*
	 * Take the device list mutex to prevent races with the final phase of
	 * a device replace operation that replaces the device object associated
	 * with map stripes (dev-replace.c:btrfs_dev_replace_finishing()).
	 */
	mutex_lock(&fs_devices->device_list_mutex);
	for (i = 0; i < map->num_stripes; i++) {
		struct btrfs_device *device = map->stripes[i].dev;
		ret = btrfs_free_dev_extent(trans, device,
					    map->stripes[i].physical,
					    &dev_extent_len);
		if (ret) {
			mutex_unlock(&fs_devices->device_list_mutex);
			btrfs_abort_transaction(trans, ret);
			goto out;
		}

		if (device->bytes_used > 0) {
			mutex_lock(&fs_info->chunk_mutex);
			btrfs_device_set_bytes_used(device,
					device->bytes_used - dev_extent_len);
			spin_lock(&fs_info->free_chunk_lock);
			fs_info->free_chunk_space += dev_extent_len;
			spin_unlock(&fs_info->free_chunk_lock);
			btrfs_clear_space_info_full(fs_info);
			mutex_unlock(&fs_info->chunk_mutex);
		}

		if (map->stripes[i].dev) {
			ret = btrfs_update_device(trans, map->stripes[i].dev);
			if (ret) {
				mutex_unlock(&fs_devices->device_list_mutex);
				btrfs_abort_transaction(trans, ret);
				goto out;
			}
		}
	}
	mutex_unlock(&fs_devices->device_list_mutex);

	ret = btrfs_free_chunk(trans, fs_info, chunk_objectid, chunk_offset);
	if (ret) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

	trace_btrfs_chunk_free(fs_info, map, chunk_offset, em->len);

	if (map->type & BTRFS_BLOCK_GROUP_SYSTEM) {
		ret = btrfs_del_sys_chunk(fs_info, chunk_objectid,
					  chunk_offset);
		if (ret) {
			btrfs_abort_transaction(trans, ret);
			goto out;
		}
	}

	ret = btrfs_remove_block_group(trans, fs_info, chunk_offset, em);
	if (ret) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

out:
	/* once for us */
	free_extent_map(em);
	return ret;
}

static int btrfs_relocate_sys_chunks(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *chunk_root = fs_info->chunk_root;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_chunk *chunk;
	struct btrfs_key key;
	struct btrfs_key found_key;
	u64 chunk_type;
	bool retried = false;
	int failed = 0;
	int ret;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

again:
	key.objectid = BTRFS_FIRST_CHUNK_TREE_OBJECTID;
	key.offset = (u64)-1;
	key.type = BTRFS_CHUNK_ITEM_KEY;

	while (1) {
		mutex_lock(&fs_info->delete_unused_bgs_mutex);
		ret = btrfs_search_slot(NULL, chunk_root, &key, path, 0, 0);
		if (ret < 0) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			goto error;
		}
		BUG_ON(ret == 0); /* Corruption */

		ret = btrfs_previous_item(chunk_root, path, key.objectid,
					  key.type);
		if (ret)
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
		if (ret < 0)
			goto error;
		if (ret > 0)
			break;

		leaf = path->nodes[0];
		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);

		chunk = btrfs_item_ptr(leaf, path->slots[0],
				       struct btrfs_chunk);
		chunk_type = btrfs_chunk_type(leaf, chunk);
		btrfs_release_path(path);

		if (chunk_type & BTRFS_BLOCK_GROUP_SYSTEM) {
			ret = btrfs_relocate_chunk(fs_info, found_key.offset);
			if (ret == -ENOSPC)
				failed++;
			else
				BUG_ON(ret);
		}
		mutex_unlock(&fs_info->delete_unused_bgs_mutex);

		if (found_key.offset == 0)
			break;
		key.offset = found_key.offset - 1;
	}
	ret = 0;
	if (failed && !retried) {
		failed = 0;
		retried = true;
		goto again;
	} else if (WARN_ON(failed && retried)) {
		ret = -ENOSPC;
	}
error:
	btrfs_free_path(path);
	return ret;
}
			      struct btrfs_chunk *chunk,
			      struct btrfs_balance_args *bargs)
{
	struct btrfs_stripe *stripe;
	int num_stripes = btrfs_chunk_num_stripes(leaf, chunk);
	int i;

	for (i = 0; i < num_stripes; i++) {
		stripe = btrfs_stripe_nr(chunk, i);
		if (btrfs_stripe_devid(leaf, stripe) == bargs->devid)
			return 0;
	}

	return 1;
}
			       u64 chunk_offset,
			       struct btrfs_balance_args *bargs)
{
	struct btrfs_stripe *stripe;
	int num_stripes = btrfs_chunk_num_stripes(leaf, chunk);
	u64 stripe_offset;
	u64 stripe_length;
	int factor;
	int i;

	if (!(bargs->flags & BTRFS_BALANCE_ARGS_DEVID))
		return 0;

	if (btrfs_chunk_type(leaf, chunk) & (BTRFS_BLOCK_GROUP_DUP |
	     BTRFS_BLOCK_GROUP_RAID1 | BTRFS_BLOCK_GROUP_RAID10)) {
		factor = num_stripes / 2;
	} else if (btrfs_chunk_type(leaf, chunk) & BTRFS_BLOCK_GROUP_RAID5) {
		factor = num_stripes - 1;
	} else if (btrfs_chunk_type(leaf, chunk) & BTRFS_BLOCK_GROUP_RAID6) {
		factor = num_stripes - 2;
	} else {
		factor = num_stripes;
	}

	for (i = 0; i < num_stripes; i++) {
		stripe = btrfs_stripe_nr(chunk, i);
		if (btrfs_stripe_devid(leaf, stripe) != bargs->devid)
			continue;

		stripe_offset = btrfs_stripe_offset(leaf, stripe);
		stripe_length = btrfs_chunk_length(leaf, chunk);
		stripe_length = div_u64(stripe_length, factor);

		if (stripe_offset < bargs->pend &&
		    stripe_offset + stripe_length > bargs->pstart)
			return 0;
	}

	return 1;
}

static int __btrfs_balance(struct btrfs_fs_info *fs_info)
{
	struct btrfs_balance_control *bctl = fs_info->balance_ctl;
	struct btrfs_root *chunk_root = fs_info->chunk_root;
	struct btrfs_root *dev_root = fs_info->dev_root;
	struct list_head *devices;
	struct btrfs_device *device;
	u64 old_size;
	u64 size_to_free;
	u64 chunk_type;
	struct btrfs_chunk *chunk;
	struct btrfs_path *path = NULL;
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_trans_handle *trans;
	struct extent_buffer *leaf;
	int slot;
	int ret;
	int enospc_errors = 0;
	bool counting = true;
	/* The single value limit and min/max limits use the same bytes in the */
	u64 limit_data = bctl->data.limit;
	u64 limit_meta = bctl->meta.limit;
	u64 limit_sys = bctl->sys.limit;
	u32 count_data = 0;
	u32 count_meta = 0;
	u32 count_sys = 0;
	int chunk_reserved = 0;
	u64 bytes_used = 0;

	/* step one make some room on all the devices */
	devices = &fs_info->fs_devices->devices;
	list_for_each_entry(device, devices, dev_list) {
		old_size = btrfs_device_get_total_bytes(device);
		size_to_free = div_factor(old_size, 1);
		size_to_free = min_t(u64, size_to_free, SZ_1M);
		if (!device->writeable ||
		    btrfs_device_get_total_bytes(device) -
		    btrfs_device_get_bytes_used(device) > size_to_free ||
		    device->is_tgtdev_for_dev_replace)
			continue;

		ret = btrfs_shrink_device(device, old_size - size_to_free);
		if (ret == -ENOSPC)
			break;
		if (ret) {
			/* btrfs_shrink_device never returns ret > 0 */
			WARN_ON(ret > 0);
			goto error;
		}

		trans = btrfs_start_transaction(dev_root, 0);
		if (IS_ERR(trans)) {
			ret = PTR_ERR(trans);
			btrfs_info_in_rcu(fs_info,
		 "resize: unable to start transaction after shrinking device %s (error %d), old size %llu, new size %llu",
					  rcu_str_deref(device->name), ret,
					  old_size, old_size - size_to_free);
			goto error;
		}

		ret = btrfs_grow_device(trans, device, old_size);
		if (ret) {
			btrfs_end_transaction(trans);
			/* btrfs_grow_device never returns ret > 0 */
			WARN_ON(ret > 0);
			btrfs_info_in_rcu(fs_info,
		 "resize: unable to grow device after shrinking device %s (error %d), old size %llu, new size %llu",
					  rcu_str_deref(device->name), ret,
					  old_size, old_size - size_to_free);
			goto error;
		}

		btrfs_end_transaction(trans);
	}

	/* step two, relocate all the chunks */
	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto error;
	}

	/* zero out stat counters */
	spin_lock(&fs_info->balance_lock);
	memset(&bctl->stat, 0, sizeof(bctl->stat));
	spin_unlock(&fs_info->balance_lock);
again:
	if (!counting) {
		/*
		 * The single value limit and min/max limits use the same bytes
		 * in the
		 */
		bctl->data.limit = limit_data;
		bctl->meta.limit = limit_meta;
		bctl->sys.limit = limit_sys;
	}
	key.objectid = BTRFS_FIRST_CHUNK_TREE_OBJECTID;
	key.offset = (u64)-1;
	key.type = BTRFS_CHUNK_ITEM_KEY;

	while (1) {
		if ((!counting && atomic_read(&fs_info->balance_pause_req)) ||
		    atomic_read(&fs_info->balance_cancel_req)) {
			ret = -ECANCELED;
			goto error;
		}

		mutex_lock(&fs_info->delete_unused_bgs_mutex);
		ret = btrfs_search_slot(NULL, chunk_root, &key, path, 0, 0);
		if (ret < 0) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			goto error;
		}

		/*
		 * this shouldn't happen, it means the last relocate
		 * failed
		 */
		if (ret == 0)
			BUG(); /* FIXME break ? */

		ret = btrfs_previous_item(chunk_root, path, 0,
					  BTRFS_CHUNK_ITEM_KEY);
		if (ret) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			ret = 0;
			break;
		}

		leaf = path->nodes[0];
		slot = path->slots[0];
		btrfs_item_key_to_cpu(leaf, &found_key, slot);

		if (found_key.objectid != key.objectid) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			break;
		}

		chunk = btrfs_item_ptr(leaf, slot, struct btrfs_chunk);
		chunk_type = btrfs_chunk_type(leaf, chunk);

		if (!counting) {
			spin_lock(&fs_info->balance_lock);
			bctl->stat.considered++;
			spin_unlock(&fs_info->balance_lock);
		}

		ret = should_balance_chunk(fs_info, leaf, chunk,
					   found_key.offset);

		btrfs_release_path(path);
		if (!ret) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			goto loop;
		}

		if (counting) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			spin_lock(&fs_info->balance_lock);
			bctl->stat.expected++;
			spin_unlock(&fs_info->balance_lock);

			if (chunk_type & BTRFS_BLOCK_GROUP_DATA)
				count_data++;
			else if (chunk_type & BTRFS_BLOCK_GROUP_SYSTEM)
				count_sys++;
			else if (chunk_type & BTRFS_BLOCK_GROUP_METADATA)
				count_meta++;

			goto loop;
		}

		/*
		 * Apply limit_min filter, no need to check if the LIMITS
		 * filter is used, limit_min is 0 by default
		 */
		if (((chunk_type & BTRFS_BLOCK_GROUP_DATA) &&
					count_data < bctl->data.limit_min)
				|| ((chunk_type & BTRFS_BLOCK_GROUP_METADATA) &&
					count_meta < bctl->meta.limit_min)
				|| ((chunk_type & BTRFS_BLOCK_GROUP_SYSTEM) &&
					count_sys < bctl->sys.limit_min)) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			goto loop;
		}

		ASSERT(fs_info->data_sinfo);
		spin_lock(&fs_info->data_sinfo->lock);
		bytes_used = fs_info->data_sinfo->bytes_used;
		spin_unlock(&fs_info->data_sinfo->lock);

		if ((chunk_type & BTRFS_BLOCK_GROUP_DATA) &&
		    !chunk_reserved && !bytes_used) {
			trans = btrfs_start_transaction(chunk_root, 0);
			if (IS_ERR(trans)) {
				mutex_unlock(&fs_info->delete_unused_bgs_mutex);
				ret = PTR_ERR(trans);
				goto error;
			}

			ret = btrfs_force_chunk_alloc(trans, fs_info,
						      BTRFS_BLOCK_GROUP_DATA);
			btrfs_end_transaction(trans);
			if (ret < 0) {
				mutex_unlock(&fs_info->delete_unused_bgs_mutex);
				goto error;
			}
			chunk_reserved = 1;
		}

		ret = btrfs_relocate_chunk(fs_info, found_key.offset);
		mutex_unlock(&fs_info->delete_unused_bgs_mutex);
		if (ret && ret != -ENOSPC)
			goto error;
		if (ret == -ENOSPC) {
			enospc_errors++;
		} else {
			spin_lock(&fs_info->balance_lock);
			bctl->stat.completed++;
			spin_unlock(&fs_info->balance_lock);
		}
loop:
		if (found_key.offset == 0)
			break;
		key.offset = found_key.offset - 1;
	}

	if (counting) {
		btrfs_release_path(path);
		counting = false;
		goto again;
	}
error:
	btrfs_free_path(path);
	if (enospc_errors) {
		btrfs_info(fs_info, "%d enospc errors during balance",
			   enospc_errors);
		if (!ret)
			ret = -ENOSPC;
	}

	return ret;
}
int btrfs_balance(struct btrfs_balance_control *bctl,
		  struct btrfs_ioctl_balance_args *bargs)
{
	struct btrfs_fs_info *fs_info = bctl->fs_info;
	u64 meta_target, data_target;
	u64 allowed;
	int mixed = 0;
	int ret;
	u64 num_devices;
	unsigned seq;

	if (btrfs_fs_closing(fs_info) ||
	    atomic_read(&fs_info->balance_pause_req) ||
	    atomic_read(&fs_info->balance_cancel_req)) {
		ret = -EINVAL;
		goto out;
	}

	allowed = btrfs_super_incompat_flags(fs_info->super_copy);
	if (allowed & BTRFS_FEATURE_INCOMPAT_MIXED_GROUPS)
		mixed = 1;

	/*
	 * In case of mixed groups both data and meta should be picked,
	 * and identical options should be given for both of them.
	 */
	allowed = BTRFS_BALANCE_DATA | BTRFS_BALANCE_METADATA;
	if (mixed && (bctl->flags & allowed)) {
		if (!(bctl->flags & BTRFS_BALANCE_DATA) ||
		    !(bctl->flags & BTRFS_BALANCE_METADATA) ||
		    memcmp(&bctl->data, &bctl->meta, sizeof(bctl->data))) {
			btrfs_err(fs_info,
				  "with mixed groups data and metadata balance options must be the same");
			ret = -EINVAL;
			goto out;
		}
	}

	num_devices = fs_info->fs_devices->num_devices;
	btrfs_dev_replace_lock(&fs_info->dev_replace, 0);
	if (btrfs_dev_replace_is_ongoing(&fs_info->dev_replace)) {
		BUG_ON(num_devices < 1);
		num_devices--;
	}
	btrfs_dev_replace_unlock(&fs_info->dev_replace, 0);
	allowed = BTRFS_AVAIL_ALLOC_BIT_SINGLE | BTRFS_BLOCK_GROUP_DUP;
	if (num_devices > 1)
		allowed |= (BTRFS_BLOCK_GROUP_RAID0 | BTRFS_BLOCK_GROUP_RAID1);
	if (num_devices > 2)
		allowed |= BTRFS_BLOCK_GROUP_RAID5;
	if (num_devices > 3)
		allowed |= (BTRFS_BLOCK_GROUP_RAID10 |
			    BTRFS_BLOCK_GROUP_RAID6);
	if (validate_convert_profile(&bctl->data, allowed)) {
		btrfs_err(fs_info,
			  "unable to start balance with target data profile %llu",
			  bctl->data.target);
		ret = -EINVAL;
		goto out;
	}
	if (validate_convert_profile(&bctl->meta, allowed)) {
		btrfs_err(fs_info,
			  "unable to start balance with target metadata profile %llu",
			  bctl->meta.target);
		ret = -EINVAL;
		goto out;
	}
	if (validate_convert_profile(&bctl->sys, allowed)) {
		btrfs_err(fs_info,
			  "unable to start balance with target system profile %llu",
			  bctl->sys.target);
		ret = -EINVAL;
		goto out;
	}

	/* allow to reduce meta or sys integrity only if force set */
	allowed = BTRFS_BLOCK_GROUP_DUP | BTRFS_BLOCK_GROUP_RAID1 |
			BTRFS_BLOCK_GROUP_RAID10 |
			BTRFS_BLOCK_GROUP_RAID5 |
			BTRFS_BLOCK_GROUP_RAID6;
	do {
		seq = read_seqbegin(&fs_info->profiles_lock);

		if (((bctl->sys.flags & BTRFS_BALANCE_ARGS_CONVERT) &&
		     (fs_info->avail_system_alloc_bits & allowed) &&
		     !(bctl->sys.target & allowed)) ||
		    ((bctl->meta.flags & BTRFS_BALANCE_ARGS_CONVERT) &&
		     (fs_info->avail_metadata_alloc_bits & allowed) &&
		     !(bctl->meta.target & allowed))) {
			if (bctl->flags & BTRFS_BALANCE_FORCE) {
				btrfs_info(fs_info,
					   "force reducing metadata integrity");
			} else {
				btrfs_err(fs_info,
					  "balance will reduce metadata integrity, use force if you want this");
				ret = -EINVAL;
				goto out;
			}
		}
	} while (read_seqretry(&fs_info->profiles_lock, seq));

	/* if we're not converting, the target field is uninitialized */
	meta_target = (bctl->meta.flags & BTRFS_BALANCE_ARGS_CONVERT) ?
		bctl->meta.target : fs_info->avail_metadata_alloc_bits;
	data_target = (bctl->data.flags & BTRFS_BALANCE_ARGS_CONVERT) ?
		bctl->data.target : fs_info->avail_data_alloc_bits;
	if (btrfs_get_num_tolerated_disk_barrier_failures(meta_target) <
		btrfs_get_num_tolerated_disk_barrier_failures(data_target)) {
		btrfs_warn(fs_info,
			   "metadata profile 0x%llx has lower redundancy than data profile 0x%llx",
			   meta_target, data_target);
	}

	if (bctl->sys.flags & BTRFS_BALANCE_ARGS_CONVERT) {
		fs_info->num_tolerated_disk_barrier_failures = min(
			btrfs_calc_num_tolerated_disk_barrier_failures(fs_info),
			btrfs_get_num_tolerated_disk_barrier_failures(
				bctl->sys.target));
	}

	ret = insert_balance_item(fs_info, bctl);
	if (ret && ret != -EEXIST)
		goto out;

	if (!(bctl->flags & BTRFS_BALANCE_RESUME)) {
		BUG_ON(ret == -EEXIST);
		set_balance_control(bctl);
	} else {
		BUG_ON(ret != -EEXIST);
		spin_lock(&fs_info->balance_lock);
		update_balance_args(bctl);
		spin_unlock(&fs_info->balance_lock);
	}

	atomic_inc(&fs_info->balance_running);
	mutex_unlock(&fs_info->balance_mutex);

	ret = __btrfs_balance(fs_info);

	mutex_lock(&fs_info->balance_mutex);
	atomic_dec(&fs_info->balance_running);

	if (bctl->sys.flags & BTRFS_BALANCE_ARGS_CONVERT) {
		fs_info->num_tolerated_disk_barrier_failures =
			btrfs_calc_num_tolerated_disk_barrier_failures(fs_info);
	}

	if (bargs) {
		memset(bargs, 0, sizeof(*bargs));
		update_ioctl_balance_args(fs_info, 0, bargs);
	}

	if ((ret && ret != -ECANCELED && ret != -ENOSPC) ||
	    balance_need_close(fs_info)) {
		__cancel_balance(fs_info);
	}

	wake_up(&fs_info->balance_wait_q);

	return ret;
out:
	if (bctl->flags & BTRFS_BALANCE_RESUME)
		__cancel_balance(fs_info);
	else {
		kfree(bctl);
		clear_bit(BTRFS_FS_EXCL_OP, &fs_info->flags);
	}
	return ret;
}

static int btrfs_uuid_scan_kthread(void *data)
{
	struct btrfs_fs_info *fs_info = data;
	struct btrfs_root *root = fs_info->tree_root;
	struct btrfs_key key;
	struct btrfs_key max_key;
	struct btrfs_path *path = NULL;
	int ret = 0;
	struct extent_buffer *eb;
	int slot;
	struct btrfs_root_item root_item;
	u32 item_size;
	struct btrfs_trans_handle *trans = NULL;

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	key.objectid = 0;
	key.type = BTRFS_ROOT_ITEM_KEY;
	key.offset = 0;

	max_key.objectid = (u64)-1;
	max_key.type = BTRFS_ROOT_ITEM_KEY;
	max_key.offset = (u64)-1;

	while (1) {
		ret = btrfs_search_forward(root, &key, path, 0);
		if (ret) {
			if (ret > 0)
				ret = 0;
			break;
		}

		if (key.type != BTRFS_ROOT_ITEM_KEY ||
		    (key.objectid < BTRFS_FIRST_FREE_OBJECTID &&
		     key.objectid != BTRFS_FS_TREE_OBJECTID) ||
		    key.objectid > BTRFS_LAST_FREE_OBJECTID)
			goto skip;

		eb = path->nodes[0];
		slot = path->slots[0];
		item_size = btrfs_item_size_nr(eb, slot);
		if (item_size < sizeof(root_item))
			goto skip;

		read_extent_buffer(eb, &root_item,
				   btrfs_item_ptr_offset(eb, slot),
				   (int)sizeof(root_item));
		if (btrfs_root_refs(&root_item) == 0)
			goto skip;

		if (!btrfs_is_empty_uuid(root_item.uuid) ||
		    !btrfs_is_empty_uuid(root_item.received_uuid)) {
			if (trans)
				goto update_tree;

			btrfs_release_path(path);
			/*
			 * 1 - subvol uuid item
			 * 1 - received_subvol uuid item
			 */
			trans = btrfs_start_transaction(fs_info->uuid_root, 2);
			if (IS_ERR(trans)) {
				ret = PTR_ERR(trans);
				break;
			}
			continue;
		} else {
			goto skip;
		}
update_tree:
		if (!btrfs_is_empty_uuid(root_item.uuid)) {
			ret = btrfs_uuid_tree_add(trans, fs_info,
						  root_item.uuid,
						  BTRFS_UUID_KEY_SUBVOL,
						  key.objectid);
			if (ret < 0) {
				btrfs_warn(fs_info, "uuid_tree_add failed %d",
					ret);
				break;
			}
		}

		if (!btrfs_is_empty_uuid(root_item.received_uuid)) {
			ret = btrfs_uuid_tree_add(trans, fs_info,
						  root_item.received_uuid,
						 BTRFS_UUID_KEY_RECEIVED_SUBVOL,
						  key.objectid);
			if (ret < 0) {
				btrfs_warn(fs_info, "uuid_tree_add failed %d",
					ret);
				break;
			}
		}

skip:
		if (trans) {
			ret = btrfs_end_transaction(trans);
			trans = NULL;
			if (ret)
				break;
		}

		btrfs_release_path(path);
		if (key.offset < (u64)-1) {
			key.offset++;
		} else if (key.type < BTRFS_ROOT_ITEM_KEY) {
			key.offset = 0;
			key.type = BTRFS_ROOT_ITEM_KEY;
		} else if (key.objectid < (u64)-1) {
			key.offset = 0;
			key.type = BTRFS_ROOT_ITEM_KEY;
			key.objectid++;
		} else {
			break;
		}
		cond_resched();
	}

out:
	btrfs_free_path(path);
	if (trans && !IS_ERR(trans))
		btrfs_end_transaction(trans);
	if (ret)
		btrfs_warn(fs_info, "btrfs_uuid_scan_kthread failed %d", ret);
	else
		set_bit(BTRFS_FS_UPDATE_UUID_TREE_GEN, &fs_info->flags);
	up(&fs_info->uuid_tree_rescan_sem);
	return 0;
}
 */
int btrfs_shrink_device(struct btrfs_device *device, u64 new_size)
{
	struct btrfs_fs_info *fs_info = device->fs_info;
	struct btrfs_root *root = fs_info->dev_root;
	struct btrfs_trans_handle *trans;
	struct btrfs_dev_extent *dev_extent = NULL;
	struct btrfs_path *path;
	u64 length;
	u64 chunk_offset;
	int ret;
	int slot;
	int failed = 0;
	bool retried = false;
	bool checked_pending_chunks = false;
	struct extent_buffer *l;
	struct btrfs_key key;
	struct btrfs_super_block *super_copy = fs_info->super_copy;
	u64 old_total = btrfs_super_total_bytes(super_copy);
	u64 old_size = btrfs_device_get_total_bytes(device);
	u64 diff = old_size - new_size;

	if (device->is_tgtdev_for_dev_replace)
		return -EINVAL;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	path->reada = READA_FORWARD;

	mutex_lock(&fs_info->chunk_mutex);

	btrfs_device_set_total_bytes(device, new_size);
	if (device->writeable) {
		device->fs_devices->total_rw_bytes -= diff;
		spin_lock(&fs_info->free_chunk_lock);
		fs_info->free_chunk_space -= diff;
		spin_unlock(&fs_info->free_chunk_lock);
	}
	mutex_unlock(&fs_info->chunk_mutex);

again:
	key.objectid = device->devid;
	key.offset = (u64)-1;
	key.type = BTRFS_DEV_EXTENT_KEY;

	do {
		mutex_lock(&fs_info->delete_unused_bgs_mutex);
		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			goto done;
		}

		ret = btrfs_previous_item(root, path, 0, key.type);
		if (ret)
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
		if (ret < 0)
			goto done;
		if (ret) {
			ret = 0;
			btrfs_release_path(path);
			break;
		}

		l = path->nodes[0];
		slot = path->slots[0];
		btrfs_item_key_to_cpu(l, &key, path->slots[0]);

		if (key.objectid != device->devid) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			btrfs_release_path(path);
			break;
		}

		dev_extent = btrfs_item_ptr(l, slot, struct btrfs_dev_extent);
		length = btrfs_dev_extent_length(l, dev_extent);

		if (key.offset + length <= new_size) {
			mutex_unlock(&fs_info->delete_unused_bgs_mutex);
			btrfs_release_path(path);
			break;
		}

		chunk_offset = btrfs_dev_extent_chunk_offset(l, dev_extent);
		btrfs_release_path(path);

		ret = btrfs_relocate_chunk(fs_info, chunk_offset);
		mutex_unlock(&fs_info->delete_unused_bgs_mutex);
		if (ret && ret != -ENOSPC)
			goto done;
		if (ret == -ENOSPC)
			failed++;
	} while (key.offset-- > 0);

	if (failed && !retried) {
		failed = 0;
		retried = true;
		goto again;
	} else if (failed && retried) {
		ret = -ENOSPC;
		goto done;
	}

	/* Shrinking succeeded, else we would be at "done". */
	trans = btrfs_start_transaction(root, 0);
	if (IS_ERR(trans)) {
		ret = PTR_ERR(trans);
		goto done;
	}

	mutex_lock(&fs_info->chunk_mutex);

	/*
	 * We checked in the above loop all device extents that were already in
	 * the device tree. However before we have updated the device's
	 * total_bytes to the new size, we might have had chunk allocations that
	 * have not complete yet (new block groups attached to transaction
	 * handles), and therefore their device extents were not yet in the
	 * device tree and we missed them in the loop above. So if we have any
	 * pending chunk using a device extent that overlaps the device range
	 * that we can not use anymore, commit the current transaction and
	 * repeat the search on the device tree - this way we guarantee we will
	 * not have chunks using device extents that end beyond 'new_size'.
	 */
	if (!checked_pending_chunks) {
		u64 start = new_size;
		u64 len = old_size - new_size;

		if (contains_pending_extent(trans->transaction, device,
					    &start, len)) {
			mutex_unlock(&fs_info->chunk_mutex);
			checked_pending_chunks = true;
			failed = 0;
			retried = false;
			ret = btrfs_commit_transaction(trans);
			if (ret)
				goto done;
			goto again;
		}
	}

	btrfs_device_set_disk_total_bytes(device, new_size);
	if (list_empty(&device->resized_list))
		list_add_tail(&device->resized_list,
			      &fs_info->fs_devices->resized_devices);

	WARN_ON(diff > old_total);
	btrfs_set_super_total_bytes(super_copy, old_total - diff);
	mutex_unlock(&fs_info->chunk_mutex);

	/* Now btrfs_update_device() will change the on-disk size. */
	ret = btrfs_update_device(trans, device);
	btrfs_end_transaction(trans);
done:
	btrfs_free_path(path);
	if (ret) {
		mutex_lock(&fs_info->chunk_mutex);
		btrfs_device_set_total_bytes(device, old_size);
		if (device->writeable)
			device->fs_devices->total_rw_bytes += diff;
		spin_lock(&fs_info->free_chunk_lock);
		fs_info->free_chunk_space += diff;
		spin_unlock(&fs_info->free_chunk_lock);
		mutex_unlock(&fs_info->chunk_mutex);
	}
	return ret;
}
static int __btrfs_alloc_chunk(struct btrfs_trans_handle *trans,
			       u64 start, u64 type)
{
	struct btrfs_fs_info *info = trans->fs_info;
	struct btrfs_fs_devices *fs_devices = info->fs_devices;
	struct list_head *cur;
	struct map_lookup *map = NULL;
	struct extent_map_tree *em_tree;
	struct extent_map *em;
	struct btrfs_device_info *devices_info = NULL;
	u64 total_avail;
	int num_stripes;	/* total number of stripes to allocate */
	int data_stripes;	/* number of stripes that count for
				   block group size */
	int sub_stripes;	/* sub_stripes info for map */
	int dev_stripes;	/* stripes per dev */
	int devs_max;		/* max devs to use */
	int devs_min;		/* min devs needed */
	int devs_increment;	/* ndevs has to be a multiple of this */
	int ncopies;		/* how many copies to data has */
	int ret;
	u64 max_stripe_size;
	u64 max_chunk_size;
	u64 stripe_size;
	u64 num_bytes;
	u64 raid_stripe_len = BTRFS_STRIPE_LEN;
	int ndevs;
	int i;
	int j;
	int index;

	BUG_ON(!alloc_profile_is_valid(type, 0));

	if (list_empty(&fs_devices->alloc_list))
		return -ENOSPC;

	index = __get_raid_index(type);

	sub_stripes = btrfs_raid_array[index].sub_stripes;
	dev_stripes = btrfs_raid_array[index].dev_stripes;
	devs_max = btrfs_raid_array[index].devs_max;
	devs_min = btrfs_raid_array[index].devs_min;
	devs_increment = btrfs_raid_array[index].devs_increment;
	ncopies = btrfs_raid_array[index].ncopies;

	if (type & BTRFS_BLOCK_GROUP_DATA) {
		max_stripe_size = SZ_1G;
		max_chunk_size = 10 * max_stripe_size;
		if (!devs_max)
			devs_max = BTRFS_MAX_DEVS(info->chunk_root);
	} else if (type & BTRFS_BLOCK_GROUP_METADATA) {
		/* for larger filesystems, use larger metadata chunks */
		if (fs_devices->total_rw_bytes > 50ULL * SZ_1G)
			max_stripe_size = SZ_1G;
		else
			max_stripe_size = SZ_256M;
		max_chunk_size = max_stripe_size;
		if (!devs_max)
			devs_max = BTRFS_MAX_DEVS(info->chunk_root);
	} else if (type & BTRFS_BLOCK_GROUP_SYSTEM) {
		max_stripe_size = SZ_32M;
		max_chunk_size = 2 * max_stripe_size;
		if (!devs_max)
			devs_max = BTRFS_MAX_DEVS_SYS_CHUNK;
	} else {
		btrfs_err(info, "invalid chunk type 0x%llx requested",
		       type);
		BUG_ON(1);
	}

	/* we don't want a chunk larger than 10% of writeable space */
	max_chunk_size = min(div_factor(fs_devices->total_rw_bytes, 1),
			     max_chunk_size);

	devices_info = kcalloc(fs_devices->rw_devices, sizeof(*devices_info),
			       GFP_NOFS);
	if (!devices_info)
		return -ENOMEM;

	cur = fs_devices->alloc_list.next;

	/*
	 * in the first pass through the devices list, we gather information
	 * about the available holes on each device.
	 */
	ndevs = 0;
	while (cur != &fs_devices->alloc_list) {
		struct btrfs_device *device;
		u64 max_avail;
		u64 dev_offset;

		device = list_entry(cur, struct btrfs_device, dev_alloc_list);

		cur = cur->next;

		if (!device->writeable) {
			WARN(1, KERN_ERR
			       "BTRFS: read-only device in alloc_list\n");
			continue;
		}

		if (!device->in_fs_metadata ||
		    device->is_tgtdev_for_dev_replace)
			continue;

		if (device->total_bytes > device->bytes_used)
			total_avail = device->total_bytes - device->bytes_used;
		else
			total_avail = 0;

		/* If there is no space on this device, skip it. */
		if (total_avail == 0)
			continue;

		ret = find_free_dev_extent(trans, device,
					   max_stripe_size * dev_stripes,
					   &dev_offset, &max_avail);
		if (ret && ret != -ENOSPC)
			goto error;

		if (ret == 0)
			max_avail = max_stripe_size * dev_stripes;

		if (max_avail < BTRFS_STRIPE_LEN * dev_stripes)
			continue;

		if (ndevs == fs_devices->rw_devices) {
			WARN(1, "%s: found more than %llu devices\n",
			     __func__, fs_devices->rw_devices);
			break;
		}
		devices_info[ndevs].dev_offset = dev_offset;
		devices_info[ndevs].max_avail = max_avail;
		devices_info[ndevs].total_avail = total_avail;
		devices_info[ndevs].dev = device;
		++ndevs;
	}

	/*
	 * now sort the devices by hole size / available space
	 */
	sort(devices_info, ndevs, sizeof(struct btrfs_device_info),
	     btrfs_cmp_device_info, NULL);

	/* round down to number of usable stripes */
	ndevs -= ndevs % devs_increment;

	if (ndevs < devs_increment * sub_stripes || ndevs < devs_min) {
		ret = -ENOSPC;
		goto error;
	}

	if (devs_max && ndevs > devs_max)
		ndevs = devs_max;
	/*
	 * the primary goal is to maximize the number of stripes, so use as many
	 * devices as possible, even if the stripes are not maximum sized.
	 */
	stripe_size = devices_info[ndevs-1].max_avail;
	num_stripes = ndevs * dev_stripes;

	/*
	 * this will have to be fixed for RAID1 and RAID10 over
	 * more drives
	 */
	data_stripes = num_stripes / ncopies;

	if (type & BTRFS_BLOCK_GROUP_RAID5) {
		raid_stripe_len = find_raid56_stripe_len(ndevs - 1,
							 info->stripesize);
		data_stripes = num_stripes - 1;
	}
	if (type & BTRFS_BLOCK_GROUP_RAID6) {
		raid_stripe_len = find_raid56_stripe_len(ndevs - 2,
							 info->stripesize);
		data_stripes = num_stripes - 2;
	}

	/*
	 * Use the number of data stripes to figure out how big this chunk
	 * is really going to be in terms of logical address space,
	 * and compare that answer with the max chunk size
	 */
	if (stripe_size * data_stripes > max_chunk_size) {
		u64 mask = (1ULL << 24) - 1;

		stripe_size = div_u64(max_chunk_size, data_stripes);

		/* bump the answer up to a 16MB boundary */
		stripe_size = (stripe_size + mask) & ~mask;

		/* but don't go higher than the limits we found
		 * while searching for free extents
		 */
		if (stripe_size > devices_info[ndevs-1].max_avail)
			stripe_size = devices_info[ndevs-1].max_avail;
	}

	stripe_size = div_u64(stripe_size, dev_stripes);

	/* align to BTRFS_STRIPE_LEN */
	stripe_size = div64_u64(stripe_size, raid_stripe_len);
	stripe_size *= raid_stripe_len;

	map = kmalloc(map_lookup_size(num_stripes), GFP_NOFS);
	if (!map) {
		ret = -ENOMEM;
		goto error;
	}
	map->num_stripes = num_stripes;

	for (i = 0; i < ndevs; ++i) {
		for (j = 0; j < dev_stripes; ++j) {
			int s = i * dev_stripes + j;
			map->stripes[s].dev = devices_info[i].dev;
			map->stripes[s].physical = devices_info[i].dev_offset +
						   j * stripe_size;
		}
	}
	map->sector_size = info->sectorsize;
	map->stripe_len = raid_stripe_len;
	map->io_align = raid_stripe_len;
	map->io_width = raid_stripe_len;
	map->type = type;
	map->sub_stripes = sub_stripes;

	num_bytes = stripe_size * data_stripes;

	trace_btrfs_chunk_alloc(info, map, start, num_bytes);

	em = alloc_extent_map();
	if (!em) {
		kfree(map);
		ret = -ENOMEM;
		goto error;
	}
	set_bit(EXTENT_FLAG_FS_MAPPING, &em->flags);
	em->map_lookup = map;
	em->start = start;
	em->len = num_bytes;
	em->block_start = 0;
	em->block_len = em->len;
	em->orig_block_len = stripe_size;

	em_tree = &info->mapping_tree.map_tree;
	write_lock(&em_tree->lock);
	ret = add_extent_mapping(em_tree, em, 0);
	if (!ret) {
		list_add_tail(&em->list, &trans->transaction->pending_chunks);
		refcount_inc(&em->refs);
	}
	write_unlock(&em_tree->lock);
	if (ret) {
		free_extent_map(em);
		goto error;
	}

	ret = btrfs_make_block_group(trans, info, 0, type,
				     BTRFS_FIRST_CHUNK_TREE_OBJECTID,
				     start, num_bytes);
	if (ret)
		goto error_del_extent;

	for (i = 0; i < map->num_stripes; i++) {
		num_bytes = map->stripes[i].dev->bytes_used + stripe_size;
		btrfs_device_set_bytes_used(map->stripes[i].dev, num_bytes);
	}

	spin_lock(&info->free_chunk_lock);
	info->free_chunk_space -= (stripe_size * map->num_stripes);
	spin_unlock(&info->free_chunk_lock);

	free_extent_map(em);
	check_raid56_incompat_flag(info, type);

	kfree(devices_info);
	return 0;

error_del_extent:
	write_lock(&em_tree->lock);
	remove_extent_mapping(em_tree, em);
	write_unlock(&em_tree->lock);

	/* One for our allocation */
	free_extent_map(em);
	/* One for the tree reference */
	free_extent_map(em);
	/* One for the pending_chunks list reference */
	free_extent_map(em);
error:
	kfree(devices_info);
	return ret;
}
				struct btrfs_fs_info *fs_info,
				u64 chunk_offset, u64 chunk_size)
{
	struct btrfs_root *extent_root = fs_info->extent_root;
	struct btrfs_root *chunk_root = fs_info->chunk_root;
	struct btrfs_key key;
	struct btrfs_device *device;
	struct btrfs_chunk *chunk;
	struct btrfs_stripe *stripe;
	struct extent_map *em;
	struct map_lookup *map;
	size_t item_size;
	u64 dev_offset;
	u64 stripe_size;
	int i = 0;
	int ret = 0;

	em = get_chunk_map(fs_info, chunk_offset, chunk_size);
	if (IS_ERR(em))
		return PTR_ERR(em);

	map = em->map_lookup;
	item_size = btrfs_chunk_item_size(map->num_stripes);
	stripe_size = em->orig_block_len;

	chunk = kzalloc(item_size, GFP_NOFS);
	if (!chunk) {
		ret = -ENOMEM;
		goto out;
	}

	/*
	 * Take the device list mutex to prevent races with the final phase of
	 * a device replace operation that replaces the device object associated
	 * with the map's stripes, because the device object's id can change
	 * at any time during that final phase of the device replace operation
	 * (dev-replace.c:btrfs_dev_replace_finishing()).
	 */
	mutex_lock(&fs_info->fs_devices->device_list_mutex);
	for (i = 0; i < map->num_stripes; i++) {
		device = map->stripes[i].dev;
		dev_offset = map->stripes[i].physical;

		ret = btrfs_update_device(trans, device);
		if (ret)
			break;
		ret = btrfs_alloc_dev_extent(trans, device,
					     chunk_root->root_key.objectid,
					     BTRFS_FIRST_CHUNK_TREE_OBJECTID,
					     chunk_offset, dev_offset,
					     stripe_size);
		if (ret)
			break;
	}
	if (ret) {
		mutex_unlock(&fs_info->fs_devices->device_list_mutex);
		goto out;
	}

	stripe = &chunk->stripe;
	for (i = 0; i < map->num_stripes; i++) {
		device = map->stripes[i].dev;
		dev_offset = map->stripes[i].physical;

		btrfs_set_stack_stripe_devid(stripe, device->devid);
		btrfs_set_stack_stripe_offset(stripe, dev_offset);
		memcpy(stripe->dev_uuid, device->uuid, BTRFS_UUID_SIZE);
		stripe++;
	}
	mutex_unlock(&fs_info->fs_devices->device_list_mutex);

	btrfs_set_stack_chunk_length(chunk, chunk_size);
	btrfs_set_stack_chunk_owner(chunk, extent_root->root_key.objectid);
	btrfs_set_stack_chunk_stripe_len(chunk, map->stripe_len);
	btrfs_set_stack_chunk_type(chunk, map->type);
	btrfs_set_stack_chunk_num_stripes(chunk, map->num_stripes);
	btrfs_set_stack_chunk_io_align(chunk, map->stripe_len);
	btrfs_set_stack_chunk_io_width(chunk, map->stripe_len);
	btrfs_set_stack_chunk_sector_size(chunk, fs_info->sectorsize);
	btrfs_set_stack_chunk_sub_stripes(chunk, map->sub_stripes);

	key.objectid = BTRFS_FIRST_CHUNK_TREE_OBJECTID;
	key.type = BTRFS_CHUNK_ITEM_KEY;
	key.offset = chunk_offset;

	ret = btrfs_insert_item(trans, chunk_root, &key, chunk, item_size);
	if (ret == 0 && map->type & BTRFS_BLOCK_GROUP_SYSTEM) {
		/*
		 * TODO: Cleanup of inserted chunk root in case of
		 * failure.
		 */
		ret = btrfs_add_system_chunk(fs_info, &key, chunk, item_size);
	}

out:
	kfree(chunk);
	free_extent_map(em);
	return ret;
}

int btrfs_chunk_readonly(struct btrfs_fs_info *fs_info, u64 chunk_offset)
{
	struct extent_map *em;
	struct map_lookup *map;
	int readonly = 0;
	int miss_ndevs = 0;
	int i;

	em = get_chunk_map(fs_info, chunk_offset, 1);
	if (IS_ERR(em))
		return 1;

	map = em->map_lookup;
	for (i = 0; i < map->num_stripes; i++) {
		if (map->stripes[i].dev->missing) {
			miss_ndevs++;
			continue;
		}

		if (!map->stripes[i].dev->writeable) {
			readonly = 1;
			goto end;
		}
	}

	/*
	 * If the number of missing devices is larger than max errors,
	 * we can not write the data into that chunk successfully, so
	 * set it readonly.
	 */
	if (miss_ndevs > btrfs_chunk_max_errors(map))
		readonly = 1;
end:
	free_extent_map(em);
	return readonly;
}

void btrfs_mapping_tree_free(struct btrfs_mapping_tree *tree)
{
	struct extent_map *em;

	while (1) {
		write_lock(&tree->map_tree.lock);
		em = lookup_extent_mapping(&tree->map_tree, 0, (u64)-1);
		if (em)
			remove_extent_mapping(&tree->map_tree, em);
		write_unlock(&tree->map_tree.lock);
		if (!em)
			break;
		/* once for us */
		free_extent_map(em);
		/* once for the tree */
		free_extent_map(em);
	}
}
			    struct map_lookup *map, int first, int num,
			    int optimal, int dev_replace_is_ongoing)
{
	int i;
	int tolerance;
	struct btrfs_device *srcdev;

	if (dev_replace_is_ongoing &&
	    fs_info->dev_replace.cont_reading_from_srcdev_mode ==
	     BTRFS_DEV_REPLACE_ITEM_CONT_READING_FROM_SRCDEV_MODE_AVOID)
		srcdev = fs_info->dev_replace.srcdev;
	else
		srcdev = NULL;

	/*
	 * try to avoid the drive that is the source drive for a
	 * dev-replace procedure, only choose it if no other non-missing
	 * mirror is available
	 */
	for (tolerance = 0; tolerance < 2; tolerance++) {
		if (map->stripes[optimal].dev->bdev &&
		    (tolerance || map->stripes[optimal].dev != srcdev))
			return optimal;
		for (i = first; i < first + num; i++) {
			if (map->stripes[i].dev->bdev &&
			    (tolerance || map->stripes[i].dev != srcdev))
				return i;
		}
	}

	/* we couldn't find one that doesn't fail.  Just return something
	 * and the io error handling code will clean up eventually
	 */
	return optimal;
}
/* Bubble-sort the stripe set to put the parity/syndrome stripes last */
static void sort_parity_stripes(struct btrfs_bio *bbio, int num_stripes)
{
	struct btrfs_bio_stripe s;
	int i;
	u64 l;
	int again = 1;

	while (again) {
		again = 0;
		for (i = 0; i < num_stripes - 1; i++) {
			if (parity_smaller(bbio->raid_map[i],
					   bbio->raid_map[i+1])) {
				s = bbio->stripes[i];
				l = bbio->raid_map[i];
				bbio->stripes[i] = bbio->stripes[i+1];
				bbio->raid_map[i] = bbio->raid_map[i+1];
				bbio->stripes[i+1] = s;
				bbio->raid_map[i+1] = l;

				again = 1;
			}
		}
	}
}
					 u64 logical, u64 length,
					 struct btrfs_bio **bbio_ret)
{
	struct extent_map *em;
	struct map_lookup *map;
	struct btrfs_bio *bbio;
	u64 offset;
	u64 stripe_nr;
	u64 stripe_nr_end;
	u64 stripe_end_offset;
	u64 stripe_cnt;
	u64 stripe_len;
	u64 stripe_offset;
	u64 num_stripes;
	u32 stripe_index;
	u32 factor = 0;
	u32 sub_stripes = 0;
	u64 stripes_per_dev = 0;
	u32 remaining_stripes = 0;
	u32 last_stripe = 0;
	int ret = 0;
	int i;

	/* discard always return a bbio */
	ASSERT(bbio_ret);

	em = get_chunk_map(fs_info, logical, length);
	if (IS_ERR(em))
		return PTR_ERR(em);

	map = em->map_lookup;
	/* we don't discard raid56 yet */
	if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		ret = -EOPNOTSUPP;
		goto out;
	}

	offset = logical - em->start;
	length = min_t(u64, em->len - offset, length);

	stripe_len = map->stripe_len;
	/*
	 * stripe_nr counts the total number of stripes we have to stride
	 * to get to this block
	 */
	stripe_nr = div64_u64(offset, stripe_len);

	/* stripe_offset is the offset of this block in its stripe */
	stripe_offset = offset - stripe_nr * stripe_len;

	stripe_nr_end = round_up(offset + length, map->stripe_len);
	stripe_nr_end = div64_u64(stripe_nr_end, map->stripe_len);
	stripe_cnt = stripe_nr_end - stripe_nr;
	stripe_end_offset = stripe_nr_end * map->stripe_len -
			    (offset + length);
	/*
	 * after this, stripe_nr is the number of stripes on this
	 * device we have to walk to find the data, and stripe_index is
	 * the number of our device in the stripe array
	 */
	num_stripes = 1;
	stripe_index = 0;
	if (map->type & (BTRFS_BLOCK_GROUP_RAID0 |
			 BTRFS_BLOCK_GROUP_RAID10)) {
		if (map->type & BTRFS_BLOCK_GROUP_RAID0)
			sub_stripes = 1;
		else
			sub_stripes = map->sub_stripes;

		factor = map->num_stripes / sub_stripes;
		num_stripes = min_t(u64, map->num_stripes,
				    sub_stripes * stripe_cnt);
		stripe_nr = div_u64_rem(stripe_nr, factor, &stripe_index);
		stripe_index *= sub_stripes;
		stripes_per_dev = div_u64_rem(stripe_cnt, factor,
					      &remaining_stripes);
		div_u64_rem(stripe_nr_end - 1, factor, &last_stripe);
		last_stripe *= sub_stripes;
	} else if (map->type & (BTRFS_BLOCK_GROUP_RAID1 |
				BTRFS_BLOCK_GROUP_DUP)) {
		num_stripes = map->num_stripes;
	} else {
		stripe_nr = div_u64_rem(stripe_nr, map->num_stripes,
					&stripe_index);
	}

	bbio = alloc_btrfs_bio(num_stripes, 0);
	if (!bbio) {
		ret = -ENOMEM;
		goto out;
	}

	for (i = 0; i < num_stripes; i++) {
		bbio->stripes[i].physical =
			map->stripes[stripe_index].physical +
			stripe_offset + stripe_nr * map->stripe_len;
		bbio->stripes[i].dev = map->stripes[stripe_index].dev;

		if (map->type & (BTRFS_BLOCK_GROUP_RAID0 |
				 BTRFS_BLOCK_GROUP_RAID10)) {
			bbio->stripes[i].length = stripes_per_dev *
				map->stripe_len;

			if (i / sub_stripes < remaining_stripes)
				bbio->stripes[i].length +=
					map->stripe_len;

			/*
			 * Special for the first stripe and
			 * the last stripe:
			 *
			 * |-------|...|-------|
			 *     |----------|
			 *    off     end_off
			 */
			if (i < sub_stripes)
				bbio->stripes[i].length -=
					stripe_offset;

			if (stripe_index >= last_stripe &&
			    stripe_index <= (last_stripe +
					     sub_stripes - 1))
				bbio->stripes[i].length -=
					stripe_end_offset;

			if (i == sub_stripes - 1)
				stripe_offset = 0;
		} else {
			bbio->stripes[i].length = length;
		}

		stripe_index++;
		if (stripe_index == map->num_stripes) {
			stripe_index = 0;
			stripe_nr++;
		}
	}

	*bbio_ret = bbio;
	bbio->map_type = map->type;
	bbio->num_stripes = num_stripes;
out:
	free_extent_map(em);
	return ret;
}
					 u64 srcdev_devid, int *mirror_num,
					 u64 *physical)
{
	struct btrfs_bio *bbio = NULL;
	int num_stripes;
	int index_srcdev = 0;
	int found = 0;
	u64 physical_of_found = 0;
	int i;
	int ret = 0;

	ret = __btrfs_map_block(fs_info, BTRFS_MAP_GET_READ_MIRRORS,
				logical, &length, &bbio, 0, 0);
	if (ret) {
		ASSERT(bbio == NULL);
		return ret;
	}

	num_stripes = bbio->num_stripes;
	if (*mirror_num > num_stripes) {
		/*
		 * BTRFS_MAP_GET_READ_MIRRORS does not contain this mirror,
		 * that means that the requested area is not left of the left
		 * cursor
		 */
		btrfs_put_bbio(bbio);
		return -EIO;
	}

	/*
	 * process the rest of the function using the mirror_num of the source
	 * drive. Therefore look it up first.  At the end, patch the device
	 * pointer to the one of the target drive.
	 */
	for (i = 0; i < num_stripes; i++) {
		if (bbio->stripes[i].dev->devid != srcdev_devid)
			continue;

		/*
		 * In case of DUP, in order to keep it simple, only add the
		 * mirror with the lowest physical address
		 */
		if (found &&
		    physical_of_found <= bbio->stripes[i].physical)
			continue;

		index_srcdev = i;
		found = 1;
		physical_of_found = bbio->stripes[i].physical;
	}

	btrfs_put_bbio(bbio);

	ASSERT(found);
	if (!found)
		return -EIO;

	*mirror_num = index_srcdev + 1;
	*physical = physical_of_found;
	return ret;
}
				      struct btrfs_dev_replace *dev_replace,
				      int *num_stripes_ret, int *max_errors_ret)
{
	struct btrfs_bio *bbio = *bbio_ret;
	u64 srcdev_devid = dev_replace->srcdev->devid;
	int tgtdev_indexes = 0;
	int num_stripes = *num_stripes_ret;
	int max_errors = *max_errors_ret;
	int i;

	if (op == BTRFS_MAP_WRITE) {
		int index_where_to_add;

		/*
		 * duplicate the write operations while the dev replace
		 * procedure is running. Since the copying of the old disk to
		 * the new disk takes place at run time while the filesystem is
		 * mounted writable, the regular write operations to the old
		 * disk have to be duplicated to go to the new disk as well.
		 *
		 * Note that device->missing is handled by the caller, and that
		 * the write to the old disk is already set up in the stripes
		 * array.
		 */
		index_where_to_add = num_stripes;
		for (i = 0; i < num_stripes; i++) {
			if (bbio->stripes[i].dev->devid == srcdev_devid) {
				/* write to new disk, too */
				struct btrfs_bio_stripe *new =
					bbio->stripes + index_where_to_add;
				struct btrfs_bio_stripe *old =
					bbio->stripes + i;

				new->physical = old->physical;
				new->length = old->length;
				new->dev = dev_replace->tgtdev;
				bbio->tgtdev_map[i] = index_where_to_add;
				index_where_to_add++;
				max_errors++;
				tgtdev_indexes++;
			}
		}
		num_stripes = index_where_to_add;
	} else if (op == BTRFS_MAP_GET_READ_MIRRORS) {
		int index_srcdev = 0;
		int found = 0;
		u64 physical_of_found = 0;

		/*
		 * During the dev-replace procedure, the target drive can also
		 * be used to read data in case it is needed to repair a corrupt
		 * block elsewhere. This is possible if the requested area is
		 * left of the left cursor. In this area, the target drive is a
		 * full copy of the source drive.
		 */
		for (i = 0; i < num_stripes; i++) {
			if (bbio->stripes[i].dev->devid == srcdev_devid) {
				/*
				 * In case of DUP, in order to keep it simple,
				 * only add the mirror with the lowest physical
				 * address
				 */
				if (found &&
				    physical_of_found <=
				     bbio->stripes[i].physical)
					continue;
				index_srcdev = i;
				found = 1;
				physical_of_found = bbio->stripes[i].physical;
			}
		}
		if (found) {
			struct btrfs_bio_stripe *tgtdev_stripe =
				bbio->stripes + num_stripes;

			tgtdev_stripe->physical = physical_of_found;
			tgtdev_stripe->length =
				bbio->stripes[index_srcdev].length;
			tgtdev_stripe->dev = dev_replace->tgtdev;
			bbio->tgtdev_map[index_srcdev] = num_stripes;

			tgtdev_indexes++;
			num_stripes++;
		}
	}

	*num_stripes_ret = num_stripes;
	*max_errors_ret = max_errors;
	bbio->num_tgtdevs = tgtdev_indexes;
	*bbio_ret = bbio;
}
			     struct btrfs_bio **bbio_ret,
			     int mirror_num, int need_raid_map)
{
	struct extent_map *em;
	struct map_lookup *map;
	u64 offset;
	u64 stripe_offset;
	u64 stripe_nr;
	u64 stripe_len;
	u32 stripe_index;
	int i;
	int ret = 0;
	int num_stripes;
	int max_errors = 0;
	int tgtdev_indexes = 0;
	struct btrfs_bio *bbio = NULL;
	struct btrfs_dev_replace *dev_replace = &fs_info->dev_replace;
	int dev_replace_is_ongoing = 0;
	int num_alloc_stripes;
	int patch_the_first_stripe_for_dev_replace = 0;
	u64 physical_to_patch_in_first_stripe = 0;
	u64 raid56_full_stripe_start = (u64)-1;

	if (op == BTRFS_MAP_DISCARD)
		return __btrfs_map_block_for_discard(fs_info, logical,
						     *length, bbio_ret);

	em = get_chunk_map(fs_info, logical, *length);
	if (IS_ERR(em))
		return PTR_ERR(em);

	map = em->map_lookup;
	offset = logical - em->start;

	stripe_len = map->stripe_len;
	stripe_nr = offset;
	/*
	 * stripe_nr counts the total number of stripes we have to stride
	 * to get to this block
	 */
	stripe_nr = div64_u64(stripe_nr, stripe_len);

	stripe_offset = stripe_nr * stripe_len;
	if (offset < stripe_offset) {
		btrfs_crit(fs_info,
			   "stripe math has gone wrong, stripe_offset=%llu, offset=%llu, start=%llu, logical=%llu, stripe_len=%llu",
			   stripe_offset, offset, em->start, logical,
			   stripe_len);
		free_extent_map(em);
		return -EINVAL;
	}

	/* stripe_offset is the offset of this block in its stripe*/
	stripe_offset = offset - stripe_offset;

	/* if we're here for raid56, we need to know the stripe aligned start */
	if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		unsigned long full_stripe_len = stripe_len * nr_data_stripes(map);
		raid56_full_stripe_start = offset;

		/* allow a write of a full stripe, but make sure we don't
		 * allow straddling of stripes
		 */
		raid56_full_stripe_start = div64_u64(raid56_full_stripe_start,
				full_stripe_len);
		raid56_full_stripe_start *= full_stripe_len;
	}

	if (map->type & BTRFS_BLOCK_GROUP_PROFILE_MASK) {
		u64 max_len;
		/* For writes to RAID[56], allow a full stripeset across all disks.
		   For other RAID types and for RAID[56] reads, just allow a single
		   stripe (on a single disk). */
		if ((map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) &&
		    (op == BTRFS_MAP_WRITE)) {
			max_len = stripe_len * nr_data_stripes(map) -
				(offset - raid56_full_stripe_start);
		} else {
			/* we limit the length of each bio to what fits in a stripe */
			max_len = stripe_len - stripe_offset;
		}
		*length = min_t(u64, em->len - offset, max_len);
	} else {
		*length = em->len - offset;
	}

	/* This is for when we're called from btrfs_merge_bio_hook() and all
	   it cares about is the length */
	if (!bbio_ret)
		goto out;

	btrfs_dev_replace_lock(dev_replace, 0);
	dev_replace_is_ongoing = btrfs_dev_replace_is_ongoing(dev_replace);
	if (!dev_replace_is_ongoing)
		btrfs_dev_replace_unlock(dev_replace, 0);
	else
		btrfs_dev_replace_set_lock_blocking(dev_replace);

	if (dev_replace_is_ongoing && mirror_num == map->num_stripes + 1 &&
	    !need_full_stripe(op) && dev_replace->tgtdev != NULL) {
		ret = get_extra_mirror_from_replace(fs_info, logical, *length,
						    dev_replace->srcdev->devid,
						    &mirror_num,
					    &physical_to_patch_in_first_stripe);
		if (ret)
			goto out;
		else
			patch_the_first_stripe_for_dev_replace = 1;
	} else if (mirror_num > map->num_stripes) {
		mirror_num = 0;
	}

	num_stripes = 1;
	stripe_index = 0;
	if (map->type & BTRFS_BLOCK_GROUP_RAID0) {
		stripe_nr = div_u64_rem(stripe_nr, map->num_stripes,
				&stripe_index);
		if (op != BTRFS_MAP_WRITE && op != BTRFS_MAP_GET_READ_MIRRORS)
			mirror_num = 1;
	} else if (map->type & BTRFS_BLOCK_GROUP_RAID1) {
		if (op == BTRFS_MAP_WRITE || op == BTRFS_MAP_GET_READ_MIRRORS)
			num_stripes = map->num_stripes;
		else if (mirror_num)
			stripe_index = mirror_num - 1;
		else {
			stripe_index = find_live_mirror(fs_info, map, 0,
					    map->num_stripes,
					    current->pid % map->num_stripes,
					    dev_replace_is_ongoing);
			mirror_num = stripe_index + 1;
		}

	} else if (map->type & BTRFS_BLOCK_GROUP_DUP) {
		if (op == BTRFS_MAP_WRITE || op == BTRFS_MAP_GET_READ_MIRRORS) {
			num_stripes = map->num_stripes;
		} else if (mirror_num) {
			stripe_index = mirror_num - 1;
		} else {
			mirror_num = 1;
		}

	} else if (map->type & BTRFS_BLOCK_GROUP_RAID10) {
		u32 factor = map->num_stripes / map->sub_stripes;

		stripe_nr = div_u64_rem(stripe_nr, factor, &stripe_index);
		stripe_index *= map->sub_stripes;

		if (op == BTRFS_MAP_WRITE || op == BTRFS_MAP_GET_READ_MIRRORS)
			num_stripes = map->sub_stripes;
		else if (mirror_num)
			stripe_index += mirror_num - 1;
		else {
			int old_stripe_index = stripe_index;
			stripe_index = find_live_mirror(fs_info, map,
					      stripe_index,
					      map->sub_stripes, stripe_index +
					      current->pid % map->sub_stripes,
					      dev_replace_is_ongoing);
			mirror_num = stripe_index - old_stripe_index + 1;
		}

	} else if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		if (need_raid_map &&
		    (op == BTRFS_MAP_WRITE || op == BTRFS_MAP_GET_READ_MIRRORS ||
		     mirror_num > 1)) {
			/* push stripe_nr back to the start of the full stripe */
			stripe_nr = div64_u64(raid56_full_stripe_start,
					stripe_len * nr_data_stripes(map));

			/* RAID[56] write or recovery. Return all stripes */
			num_stripes = map->num_stripes;
			max_errors = nr_parity_stripes(map);

			*length = map->stripe_len;
			stripe_index = 0;
			stripe_offset = 0;
		} else {
			/*
			 * Mirror #0 or #1 means the original data block.
			 * Mirror #2 is RAID5 parity block.
			 * Mirror #3 is RAID6 Q block.
			 */
			stripe_nr = div_u64_rem(stripe_nr,
					nr_data_stripes(map), &stripe_index);
			if (mirror_num > 1)
				stripe_index = nr_data_stripes(map) +
						mirror_num - 2;

			/* We distribute the parity blocks across stripes */
			div_u64_rem(stripe_nr + stripe_index, map->num_stripes,
					&stripe_index);
			if ((op != BTRFS_MAP_WRITE &&
			     op != BTRFS_MAP_GET_READ_MIRRORS) &&
			    mirror_num <= 1)
				mirror_num = 1;
		}
	} else {
		/*
		 * after this, stripe_nr is the number of stripes on this
		 * device we have to walk to find the data, and stripe_index is
		 * the number of our device in the stripe array
		 */
		stripe_nr = div_u64_rem(stripe_nr, map->num_stripes,
				&stripe_index);
		mirror_num = stripe_index + 1;
	}
	if (stripe_index >= map->num_stripes) {
		btrfs_crit(fs_info,
			   "stripe index math went horribly wrong, got stripe_index=%u, num_stripes=%u",
			   stripe_index, map->num_stripes);
		ret = -EINVAL;
		goto out;
	}

	num_alloc_stripes = num_stripes;
	if (dev_replace_is_ongoing && dev_replace->tgtdev != NULL) {
		if (op == BTRFS_MAP_WRITE)
			num_alloc_stripes <<= 1;
		if (op == BTRFS_MAP_GET_READ_MIRRORS)
			num_alloc_stripes++;
		tgtdev_indexes = num_stripes;
	}

	bbio = alloc_btrfs_bio(num_alloc_stripes, tgtdev_indexes);
	if (!bbio) {
		ret = -ENOMEM;
		goto out;
	}
	if (dev_replace_is_ongoing && dev_replace->tgtdev != NULL)
		bbio->tgtdev_map = (int *)(bbio->stripes + num_alloc_stripes);

	/* build raid_map */
	if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK && need_raid_map &&
	    (need_full_stripe(op) || mirror_num > 1)) {
		u64 tmp;
		unsigned rot;

		bbio->raid_map = (u64 *)((void *)bbio->stripes +
				 sizeof(struct btrfs_bio_stripe) *
				 num_alloc_stripes +
				 sizeof(int) * tgtdev_indexes);

		/* Work out the disk rotation on this stripe-set */
		div_u64_rem(stripe_nr, num_stripes, &rot);

		/* Fill in the logical address of each stripe */
		tmp = stripe_nr * nr_data_stripes(map);
		for (i = 0; i < nr_data_stripes(map); i++)
			bbio->raid_map[(i+rot) % num_stripes] =
				em->start + (tmp + i) * map->stripe_len;

		bbio->raid_map[(i+rot) % map->num_stripes] = RAID5_P_STRIPE;
		if (map->type & BTRFS_BLOCK_GROUP_RAID6)
			bbio->raid_map[(i+rot+1) % num_stripes] =
				RAID6_Q_STRIPE;
	}


	for (i = 0; i < num_stripes; i++) {
		bbio->stripes[i].physical =
			map->stripes[stripe_index].physical +
			stripe_offset +
			stripe_nr * map->stripe_len;
		bbio->stripes[i].dev =
			map->stripes[stripe_index].dev;
		stripe_index++;
	}

	if (need_full_stripe(op))
		max_errors = btrfs_chunk_max_errors(map);

	if (bbio->raid_map)
		sort_parity_stripes(bbio, num_stripes);

	if (dev_replace_is_ongoing && dev_replace->tgtdev != NULL &&
	    need_full_stripe(op)) {
		handle_ops_on_dev_replace(op, &bbio, dev_replace, &num_stripes,
					  &max_errors);
	}

	*bbio_ret = bbio;
	bbio->map_type = map->type;
	bbio->num_stripes = num_stripes;
	bbio->max_errors = max_errors;
	bbio->mirror_num = mirror_num;

	/*
	 * this is the case that REQ_READ && dev_replace_is_ongoing &&
	 * mirror_num == num_stripes + 1 && dev_replace target drive is
	 * available as a mirror
	 */
	if (patch_the_first_stripe_for_dev_replace && num_stripes > 0) {
		WARN_ON(num_stripes > 1);
		bbio->stripes[0].dev = dev_replace->tgtdev;
		bbio->stripes[0].physical = physical_to_patch_in_first_stripe;
		bbio->mirror_num = map->num_stripes + 1;
	}
out:
	if (dev_replace_is_ongoing) {
		btrfs_dev_replace_clear_lock_blocking(dev_replace);
		btrfs_dev_replace_unlock(dev_replace, 0);
	}
	free_extent_map(em);
	return ret;
}
		     u64 chunk_start, u64 physical, u64 devid,
		     u64 **logical, int *naddrs, int *stripe_len)
{
	struct extent_map *em;
	struct map_lookup *map;
	u64 *buf;
	u64 bytenr;
	u64 length;
	u64 stripe_nr;
	u64 rmap_len;
	int i, j, nr = 0;

	em = get_chunk_map(fs_info, chunk_start, 1);
	if (IS_ERR(em))
		return -EIO;

	map = em->map_lookup;
	length = em->len;
	rmap_len = map->stripe_len;

	if (map->type & BTRFS_BLOCK_GROUP_RAID10)
		length = div_u64(length, map->num_stripes / map->sub_stripes);
	else if (map->type & BTRFS_BLOCK_GROUP_RAID0)
		length = div_u64(length, map->num_stripes);
	else if (map->type & BTRFS_BLOCK_GROUP_RAID56_MASK) {
		length = div_u64(length, nr_data_stripes(map));
		rmap_len = map->stripe_len * nr_data_stripes(map);
	}

	buf = kcalloc(map->num_stripes, sizeof(u64), GFP_NOFS);
	BUG_ON(!buf); /* -ENOMEM */

	for (i = 0; i < map->num_stripes; i++) {
		if (devid && map->stripes[i].dev->devid != devid)
			continue;
		if (map->stripes[i].physical > physical ||
		    map->stripes[i].physical + length <= physical)
			continue;

		stripe_nr = physical - map->stripes[i].physical;
		stripe_nr = div64_u64(stripe_nr, map->stripe_len);

		if (map->type & BTRFS_BLOCK_GROUP_RAID10) {
			stripe_nr = stripe_nr * map->num_stripes + i;
			stripe_nr = div_u64(stripe_nr, map->sub_stripes);
		} else if (map->type & BTRFS_BLOCK_GROUP_RAID0) {
			stripe_nr = stripe_nr * map->num_stripes + i;
		} /* else if RAID[56], multiply by nr_data_stripes().
		   * Alternatively, just use rmap_len below instead of
		   * map->stripe_len */

		bytenr = chunk_start + stripe_nr * rmap_len;
		WARN_ON(nr >= map->num_stripes);
		for (j = 0; j < nr; j++) {
			if (buf[j] == bytenr)
				break;
		}
		if (j == nr) {
			WARN_ON(nr >= map->num_stripes);
			buf[nr++] = bytenr;
		}
	}

	*logical = buf;
	*naddrs = nr;
	*stripe_len = rmap_len;

	free_extent_map(em);
	return 0;
}
int btrfs_map_bio(struct btrfs_fs_info *fs_info, struct bio *bio,
		  int mirror_num, int async_submit)
{
	struct btrfs_device *dev;
	struct bio *first_bio = bio;
	u64 logical = (u64)bio->bi_iter.bi_sector << 9;
	u64 length = 0;
	u64 map_length;
	int ret;
	int dev_nr;
	int total_devs;
	struct btrfs_bio *bbio = NULL;

	length = bio->bi_iter.bi_size;
	map_length = length;

	btrfs_bio_counter_inc_blocked(fs_info);
	ret = __btrfs_map_block(fs_info, bio_op(bio), logical,
				&map_length, &bbio, mirror_num, 1);
	if (ret) {
		btrfs_bio_counter_dec(fs_info);
		return ret;
	}

	total_devs = bbio->num_stripes;
	bbio->orig_bio = first_bio;
	bbio->private = first_bio->bi_private;
	bbio->end_io = first_bio->bi_end_io;
	bbio->fs_info = fs_info;
	atomic_set(&bbio->stripes_pending, bbio->num_stripes);

	if ((bbio->map_type & BTRFS_BLOCK_GROUP_RAID56_MASK) &&
	    ((bio_op(bio) == REQ_OP_WRITE) || (mirror_num > 1))) {
		/* In this case, map_length has been set to the length of
		   a single stripe; not the whole write */
		if (bio_op(bio) == REQ_OP_WRITE) {
			ret = raid56_parity_write(fs_info, bio, bbio,
						  map_length);
		} else {
			ret = raid56_parity_recover(fs_info, bio, bbio,
						    map_length, mirror_num, 1);
		}

		btrfs_bio_counter_dec(fs_info);
		return ret;
	}

	if (map_length < length) {
		btrfs_crit(fs_info,
			   "mapping failed logical %llu bio len %llu len %llu",
			   logical, length, map_length);
		BUG();
	}

	for (dev_nr = 0; dev_nr < total_devs; dev_nr++) {
		dev = bbio->stripes[dev_nr].dev;
		if (!dev || !dev->bdev ||
		    (bio_op(first_bio) == REQ_OP_WRITE && !dev->writeable)) {
			bbio_error(bbio, first_bio, logical);
			continue;
		}

		if (dev_nr < total_devs - 1) {
			bio = btrfs_bio_clone(first_bio, GFP_NOFS);
			BUG_ON(!bio); /* -ENOMEM */
		} else
			bio = first_bio;

		submit_stripe_bio(bbio, bio, bbio->stripes[dev_nr].physical,
				  dev_nr, async_submit);
	}
	btrfs_bio_counter_dec(fs_info);
	return 0;
}
struct btrfs_device *btrfs_find_device(struct btrfs_fs_info *fs_info, u64 devid,
				       u8 *uuid, u8 *fsid)
{
	struct btrfs_device *device;
	struct btrfs_fs_devices *cur_devices;

	cur_devices = fs_info->fs_devices;
	while (cur_devices) {
		if (!fsid ||
		    !memcmp(cur_devices->fsid, fsid, BTRFS_UUID_SIZE)) {
			device = __find_device(&cur_devices->devices,
					       devid, uuid);
			if (device)
				return device;
		}
		cur_devices = cur_devices->seed;
	}
	return NULL;
}
			  struct extent_buffer *leaf,
			  struct btrfs_chunk *chunk)
{
	struct btrfs_mapping_tree *map_tree = &fs_info->mapping_tree;
	struct map_lookup *map;
	struct extent_map *em;
	u64 logical;
	u64 length;
	u64 stripe_len;
	u64 devid;
	u8 uuid[BTRFS_UUID_SIZE];
	int num_stripes;
	int ret;
	int i;

	logical = key->offset;
	length = btrfs_chunk_length(leaf, chunk);
	stripe_len = btrfs_chunk_stripe_len(leaf, chunk);
	num_stripes = btrfs_chunk_num_stripes(leaf, chunk);

	ret = btrfs_check_chunk_valid(fs_info, leaf, chunk, logical);
	if (ret)
		return ret;

	read_lock(&map_tree->map_tree.lock);
	em = lookup_extent_mapping(&map_tree->map_tree, logical, 1);
	read_unlock(&map_tree->map_tree.lock);

	/* already mapped? */
	if (em && em->start <= logical && em->start + em->len > logical) {
		free_extent_map(em);
		return 0;
	} else if (em) {
		free_extent_map(em);
	}

	em = alloc_extent_map();
	if (!em)
		return -ENOMEM;
	map = kmalloc(map_lookup_size(num_stripes), GFP_NOFS);
	if (!map) {
		free_extent_map(em);
		return -ENOMEM;
	}

	set_bit(EXTENT_FLAG_FS_MAPPING, &em->flags);
	em->map_lookup = map;
	em->start = logical;
	em->len = length;
	em->orig_start = 0;
	em->block_start = 0;
	em->block_len = em->len;

	map->num_stripes = num_stripes;
	map->io_width = btrfs_chunk_io_width(leaf, chunk);
	map->io_align = btrfs_chunk_io_align(leaf, chunk);
	map->sector_size = btrfs_chunk_sector_size(leaf, chunk);
	map->stripe_len = btrfs_chunk_stripe_len(leaf, chunk);
	map->type = btrfs_chunk_type(leaf, chunk);
	map->sub_stripes = btrfs_chunk_sub_stripes(leaf, chunk);
	for (i = 0; i < num_stripes; i++) {
		map->stripes[i].physical =
			btrfs_stripe_offset_nr(leaf, chunk, i);
		devid = btrfs_stripe_devid_nr(leaf, chunk, i);
		read_extent_buffer(leaf, uuid, (unsigned long)
				   btrfs_stripe_dev_uuid_nr(chunk, i),
				   BTRFS_UUID_SIZE);
		map->stripes[i].dev = btrfs_find_device(fs_info, devid,
							uuid, NULL);
		if (!map->stripes[i].dev &&
		    !btrfs_test_opt(fs_info, DEGRADED)) {
			free_extent_map(em);
			return -EIO;
		}
		if (!map->stripes[i].dev) {
			map->stripes[i].dev =
				add_missing_dev(fs_info->fs_devices, devid,
						uuid);
			if (!map->stripes[i].dev) {
				free_extent_map(em);
				return -EIO;
			}
			btrfs_warn(fs_info, "devid %llu uuid %pU is missing",
				   devid, uuid);
		}
		map->stripes[i].dev->in_fs_metadata = 1;
	}

	write_lock(&map_tree->map_tree.lock);
	ret = add_extent_mapping(&map_tree->map_tree, em, 0);
	write_unlock(&map_tree->map_tree.lock);
	BUG_ON(ret); /* Tree corruption */
	free_extent_map(em);

	return 0;
}
static struct btrfs_fs_devices *open_seed_devices(struct btrfs_fs_info *fs_info,
						  u8 *fsid)
{
	struct btrfs_fs_devices *fs_devices;
	int ret;

	BUG_ON(!mutex_is_locked(&uuid_mutex));

	fs_devices = fs_info->fs_devices->seed;
	while (fs_devices) {
		if (!memcmp(fs_devices->fsid, fsid, BTRFS_UUID_SIZE))
			return fs_devices;

		fs_devices = fs_devices->seed;
	}

	fs_devices = find_fsid(fsid);
	if (!fs_devices) {
		if (!btrfs_test_opt(fs_info, DEGRADED))
			return ERR_PTR(-ENOENT);

		fs_devices = alloc_fs_devices(fsid);
		if (IS_ERR(fs_devices))
			return fs_devices;

		fs_devices->seeding = 1;
		fs_devices->opened = 1;
		return fs_devices;
	}

	fs_devices = clone_fs_devices(fs_devices);
	if (IS_ERR(fs_devices))
		return fs_devices;

	ret = __btrfs_open_devices(fs_devices, FMODE_READ,
				   fs_info->bdev_holder);
	if (ret) {
		free_fs_devices(fs_devices);
		fs_devices = ERR_PTR(ret);
		goto out;
	}

	if (!fs_devices->seeding) {
		__btrfs_close_devices(fs_devices);
		free_fs_devices(fs_devices);
		fs_devices = ERR_PTR(-EINVAL);
		goto out;
	}

	fs_devices->seed = fs_info->fs_devices->seed;
	fs_info->fs_devices->seed = fs_devices;
out:
	return fs_devices;
}

int btrfs_read_sys_array(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root = fs_info->tree_root;
	struct btrfs_super_block *super_copy = fs_info->super_copy;
	struct extent_buffer *sb;
	struct btrfs_disk_key *disk_key;
	struct btrfs_chunk *chunk;
	u8 *array_ptr;
	unsigned long sb_array_offset;
	int ret = 0;
	u32 num_stripes;
	u32 array_size;
	u32 len = 0;
	u32 cur_offset;
	u64 type;
	struct btrfs_key key;

	ASSERT(BTRFS_SUPER_INFO_SIZE <= fs_info->nodesize);
	/*
	 * This will create extent buffer of nodesize, superblock size is
	 * fixed to BTRFS_SUPER_INFO_SIZE. If nodesize > sb size, this will
	 * overallocate but we can keep it as-is, only the first page is used.
	 */
	sb = btrfs_find_create_tree_block(fs_info, BTRFS_SUPER_INFO_OFFSET);
	if (IS_ERR(sb))
		return PTR_ERR(sb);
	set_extent_buffer_uptodate(sb);
	btrfs_set_buffer_lockdep_class(root->root_key.objectid, sb, 0);
	/*
	 * The sb extent buffer is artificial and just used to read the system array.
	 * set_extent_buffer_uptodate() call does not properly mark all it's
	 * pages up-to-date when the page is larger: extent does not cover the
	 * whole page and consequently check_page_uptodate does not find all
	 * the page's extents up-to-date (the hole beyond sb),
	 * write_extent_buffer then triggers a WARN_ON.
	 *
	 * Regular short extents go through mark_extent_buffer_dirty/writeback cycle,
	 * but sb spans only this function. Add an explicit SetPageUptodate call
	 * to silence the warning eg. on PowerPC 64.
	 */
	if (PAGE_SIZE > BTRFS_SUPER_INFO_SIZE)
		SetPageUptodate(sb->pages[0]);

	write_extent_buffer(sb, super_copy, 0, BTRFS_SUPER_INFO_SIZE);
	array_size = btrfs_super_sys_array_size(super_copy);

	array_ptr = super_copy->sys_chunk_array;
	sb_array_offset = offsetof(struct btrfs_super_block, sys_chunk_array);
	cur_offset = 0;

	while (cur_offset < array_size) {
		disk_key = (struct btrfs_disk_key *)array_ptr;
		len = sizeof(*disk_key);
		if (cur_offset + len > array_size)
			goto out_short_read;

		btrfs_disk_key_to_cpu(&key, disk_key);

		array_ptr += len;
		sb_array_offset += len;
		cur_offset += len;

		if (key.type == BTRFS_CHUNK_ITEM_KEY) {
			chunk = (struct btrfs_chunk *)sb_array_offset;
			/*
			 * At least one btrfs_chunk with one stripe must be
			 * present, exact stripe count check comes afterwards
			 */
			len = btrfs_chunk_item_size(1);
			if (cur_offset + len > array_size)
				goto out_short_read;

			num_stripes = btrfs_chunk_num_stripes(sb, chunk);
			if (!num_stripes) {
				btrfs_err(fs_info,
					"invalid number of stripes %u in sys_array at offset %u",
					num_stripes, cur_offset);
				ret = -EIO;
				break;
			}

			type = btrfs_chunk_type(sb, chunk);
			if ((type & BTRFS_BLOCK_GROUP_SYSTEM) == 0) {
				btrfs_err(fs_info,
			    "invalid chunk type %llu in sys_array at offset %u",
					type, cur_offset);
				ret = -EIO;
				break;
			}

			len = btrfs_chunk_item_size(num_stripes);
			if (cur_offset + len > array_size)
				goto out_short_read;

			ret = read_one_chunk(fs_info, &key, sb, chunk);
			if (ret)
				break;
		} else {
			btrfs_err(fs_info,
			    "unexpected item type %u in sys_array at offset %u",
				  (u32)key.type, cur_offset);
			ret = -EIO;
			break;
		}
		array_ptr += len;
		sb_array_offset += len;
		cur_offset += len;
	}
	clear_extent_buffer_uptodate(sb);
	free_extent_buffer_stale(sb);
	return ret;

out_short_read:
	btrfs_err(fs_info, "sys_array too short to read %u bytes at offset %u",
			len, cur_offset);
	clear_extent_buffer_uptodate(sb);
	free_extent_buffer_stale(sb);
	return -EIO;
}

int btrfs_read_chunk_tree(struct btrfs_fs_info *fs_info)
{
	struct btrfs_root *root = fs_info->chunk_root;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_key key;
	struct btrfs_key found_key;
	int ret;
	int slot;
	u64 total_dev = 0;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	mutex_lock(&uuid_mutex);
	mutex_lock(&fs_info->chunk_mutex);

	/*
	 * Read all device items, and then all the chunk items. All
	 * device items are found before any chunk item (their object id
	 * is smaller than the lowest possible object id for a chunk
	 * item - BTRFS_FIRST_CHUNK_TREE_OBJECTID).
	 */
	key.objectid = BTRFS_DEV_ITEMS_OBJECTID;
	key.offset = 0;
	key.type = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto error;
	while (1) {
		leaf = path->nodes[0];
		slot = path->slots[0];
		if (slot >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret == 0)
				continue;
			if (ret < 0)
				goto error;
			break;
		}
		btrfs_item_key_to_cpu(leaf, &found_key, slot);
		if (found_key.type == BTRFS_DEV_ITEM_KEY) {
			struct btrfs_dev_item *dev_item;
			dev_item = btrfs_item_ptr(leaf, slot,
						  struct btrfs_dev_item);
			ret = read_one_dev(fs_info, leaf, dev_item);
			if (ret)
				goto error;
			total_dev++;
		} else if (found_key.type == BTRFS_CHUNK_ITEM_KEY) {
			struct btrfs_chunk *chunk;
			chunk = btrfs_item_ptr(leaf, slot, struct btrfs_chunk);
			ret = read_one_chunk(fs_info, &found_key, leaf, chunk);
			if (ret)
				goto error;
		}
		path->slots[0]++;
	}

	/*
	 * After loading chunk tree, we've got all device information,
	 * do another round of validation checks.
	 */
	if (total_dev != fs_info->fs_devices->total_devices) {
		btrfs_err(fs_info,
	   "super_num_devices %llu mismatch with num_devices %llu found here",
			  btrfs_super_num_devices(fs_info->super_copy),
			  total_dev);
		ret = -EINVAL;
		goto error;
	}
	if (btrfs_super_total_bytes(fs_info->super_copy) <
	    fs_info->fs_devices->total_rw_bytes) {
		btrfs_err(fs_info,
	"super_total_bytes %llu mismatch with fs_devices total_rw_bytes %llu",
			  btrfs_super_total_bytes(fs_info->super_copy),
			  fs_info->fs_devices->total_rw_bytes);
		ret = -EINVAL;
		goto error;
	}
	ret = 0;
error:
	mutex_unlock(&fs_info->chunk_mutex);
	mutex_unlock(&uuid_mutex);

	btrfs_free_path(path);
	return ret;
}

void btrfs_init_devices_late(struct btrfs_fs_info *fs_info)
{
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	struct btrfs_device *device;

	while (fs_devices) {
		mutex_lock(&fs_devices->device_list_mutex);
		list_for_each_entry(device, &fs_devices->devices, dev_list)
			device->fs_info = fs_info;
		mutex_unlock(&fs_devices->device_list_mutex);

		fs_devices = fs_devices->seed;
	}
}

static void __btrfs_reset_dev_stats(struct btrfs_device *dev)
{
	int i;

	for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++)
		btrfs_dev_stat_reset(dev, i);
}

int btrfs_init_dev_stats(struct btrfs_fs_info *fs_info)
{
	struct btrfs_key key;
	struct btrfs_key found_key;
	struct btrfs_root *dev_root = fs_info->dev_root;
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	struct extent_buffer *eb;
	int slot;
	int ret = 0;
	struct btrfs_device *device;
	struct btrfs_path *path = NULL;
	int i;

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto out;
	}

	mutex_lock(&fs_devices->device_list_mutex);
	list_for_each_entry(device, &fs_devices->devices, dev_list) {
		int item_size;
		struct btrfs_dev_stats_item *ptr;

		key.objectid = BTRFS_DEV_STATS_OBJECTID;
		key.type = BTRFS_PERSISTENT_ITEM_KEY;
		key.offset = device->devid;
		ret = btrfs_search_slot(NULL, dev_root, &key, path, 0, 0);
		if (ret) {
			__btrfs_reset_dev_stats(device);
			device->dev_stats_valid = 1;
			btrfs_release_path(path);
			continue;
		}
		slot = path->slots[0];
		eb = path->nodes[0];
		btrfs_item_key_to_cpu(eb, &found_key, slot);
		item_size = btrfs_item_size_nr(eb, slot);

		ptr = btrfs_item_ptr(eb, slot,
				     struct btrfs_dev_stats_item);

		for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++) {
			if (item_size >= (1 + i) * sizeof(__le64))
				btrfs_dev_stat_set(device, i,
					btrfs_dev_stats_value(eb, ptr, i));
			else
				btrfs_dev_stat_reset(device, i);
		}

		device->dev_stats_valid = 1;
		btrfs_dev_stat_print_on_load(device);
		btrfs_release_path(path);
	}
	mutex_unlock(&fs_devices->device_list_mutex);

out:
	btrfs_free_path(path);
	return ret < 0 ? ret : 0;
}
				struct btrfs_fs_info *fs_info,
				struct btrfs_device *device)
{
	struct btrfs_root *dev_root = fs_info->dev_root;
	struct btrfs_path *path;
	struct btrfs_key key;
	struct extent_buffer *eb;
	struct btrfs_dev_stats_item *ptr;
	int ret;
	int i;

	key.objectid = BTRFS_DEV_STATS_OBJECTID;
	key.type = BTRFS_PERSISTENT_ITEM_KEY;
	key.offset = device->devid;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;
	ret = btrfs_search_slot(trans, dev_root, &key, path, -1, 1);
	if (ret < 0) {
		btrfs_warn_in_rcu(fs_info,
			"error %d while searching for dev_stats item for device %s",
			      ret, rcu_str_deref(device->name));
		goto out;
	}

	if (ret == 0 &&
	    btrfs_item_size_nr(path->nodes[0], path->slots[0]) < sizeof(*ptr)) {
		/* need to delete old one and insert a new one */
		ret = btrfs_del_item(trans, dev_root, path);
		if (ret != 0) {
			btrfs_warn_in_rcu(fs_info,
				"delete too small dev_stats item for device %s failed %d",
				      rcu_str_deref(device->name), ret);
			goto out;
		}
		ret = 1;
	}

	if (ret == 1) {
		/* need to insert a new item */
		btrfs_release_path(path);
		ret = btrfs_insert_empty_item(trans, dev_root, path,
					      &key, sizeof(*ptr));
		if (ret < 0) {
			btrfs_warn_in_rcu(fs_info,
				"insert dev_stats item for device %s failed %d",
				rcu_str_deref(device->name), ret);
			goto out;
		}
	}

	eb = path->nodes[0];
	ptr = btrfs_item_ptr(eb, path->slots[0], struct btrfs_dev_stats_item);
	for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++)
		btrfs_set_dev_stats_value(eb, ptr, i,
					  btrfs_dev_stat_read(device, i));
	btrfs_mark_buffer_dirty(eb);

out:
	btrfs_free_path(path);
	return ret;
}

static void btrfs_dev_stat_print_on_load(struct btrfs_device *dev)
{
	int i;

	for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++)
		if (btrfs_dev_stat_read(dev, i) != 0)
			break;
	if (i == BTRFS_DEV_STAT_VALUES_MAX)
		return; /* all values == 0, suppress message */

	btrfs_info_in_rcu(dev->fs_info,
		"bdev %s errs: wr %u, rd %u, flush %u, corrupt %u, gen %u",
	       rcu_str_deref(dev->name),
	       btrfs_dev_stat_read(dev, BTRFS_DEV_STAT_WRITE_ERRS),
	       btrfs_dev_stat_read(dev, BTRFS_DEV_STAT_READ_ERRS),
	       btrfs_dev_stat_read(dev, BTRFS_DEV_STAT_FLUSH_ERRS),
	       btrfs_dev_stat_read(dev, BTRFS_DEV_STAT_CORRUPTION_ERRS),
	       btrfs_dev_stat_read(dev, BTRFS_DEV_STAT_GENERATION_ERRS));
}
int btrfs_get_dev_stats(struct btrfs_fs_info *fs_info,
			struct btrfs_ioctl_get_dev_stats *stats)
{
	struct btrfs_device *dev;
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	int i;

	mutex_lock(&fs_devices->device_list_mutex);
	dev = btrfs_find_device(fs_info, stats->devid, NULL, NULL);
	mutex_unlock(&fs_devices->device_list_mutex);

	if (!dev) {
		btrfs_warn(fs_info, "get dev_stats failed, device not found");
		return -ENODEV;
	} else if (!dev->dev_stats_valid) {
		btrfs_warn(fs_info, "get dev_stats failed, not yet valid");
		return -ENODEV;
	} else if (stats->flags & BTRFS_DEV_STATS_RESET) {
		for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++) {
			if (stats->nr_items > i)
				stats->values[i] =
					btrfs_dev_stat_read_and_reset(dev, i);
			else
				btrfs_dev_stat_reset(dev, i);
		}
	} else {
		for (i = 0; i < BTRFS_DEV_STAT_VALUES_MAX; i++)
			if (stats->nr_items > i)
				stats->values[i] = btrfs_dev_stat_read(dev, i);
	}
	if (stats->nr_items > BTRFS_DEV_STAT_VALUES_MAX)
		stats->nr_items = BTRFS_DEV_STAT_VALUES_MAX;
	return 0;
}

void btrfs_scratch_superblocks(struct block_device *bdev, const char *device_path)
{
	struct buffer_head *bh;
	struct btrfs_super_block *disk_super;
	int copy_num;

	if (!bdev)
		return;

	for (copy_num = 0; copy_num < BTRFS_SUPER_MIRROR_MAX;
		copy_num++) {

		if (btrfs_read_dev_one_super(bdev, copy_num, &bh))
			continue;

		disk_super = (struct btrfs_super_block *)bh->b_data;

		memset(&disk_super->magic, 0, sizeof(disk_super->magic));
		set_buffer_dirty(bh);
		sync_dirty_buffer(bh);
		brelse(bh);
	}

	/* Notify udev that device has changed */
	btrfs_kobject_uevent(bdev, KOBJ_CHANGE);

	/* Update ctime/mtime for device path for libblkid */
	update_dev_time(device_path);
}
void btrfs_update_commit_device_bytes_used(struct btrfs_fs_info *fs_info,
					struct btrfs_transaction *transaction)
{
	struct extent_map *em;
	struct map_lookup *map;
	struct btrfs_device *dev;
	int i;

	if (list_empty(&transaction->pending_chunks))
		return;

	/* In order to kick the device replace finish process */
	mutex_lock(&fs_info->chunk_mutex);
	list_for_each_entry(em, &transaction->pending_chunks, list) {
		map = em->map_lookup;

		for (i = 0; i < map->num_stripes; i++) {
			dev = map->stripes[i].dev;
			dev->commit_bytes_used = dev->bytes_used;
		}
	}
	mutex_unlock(&fs_info->chunk_mutex);
}

void btrfs_set_fs_info_ptr(struct btrfs_fs_info *fs_info)
{
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	while (fs_devices) {
		fs_devices->fs_info = fs_info;
		fs_devices = fs_devices->seed;
	}
}

void btrfs_reset_fs_info_ptr(struct btrfs_fs_info *fs_info)
{
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	while (fs_devices) {
		fs_devices->fs_info = NULL;
		fs_devices = fs_devices->seed;
	}
}
