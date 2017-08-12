int ext4_getfsmap_find_fixed_metadata(struct super_block *sb,
				      struct list_head *meta_list)
{
	struct ext4_group_desc *gdp;
	ext4_group_t agno;
	int error;

	INIT_LIST_HEAD(meta_list);

	/* Collect everything. */
	for (agno = 0; agno < EXT4_SB(sb)->s_groups_count; agno++) {
		gdp = ext4_get_group_desc(sb, agno, NULL);
		if (!gdp) {
			error = -EFSCORRUPTED;
			goto err;
		}

		/* Superblock & GDT */
		error = ext4_getfsmap_find_sb(sb, agno, meta_list);
		if (error)
			goto err;

		/* Block bitmap */
		error = ext4_getfsmap_fill(meta_list,
					   ext4_block_bitmap(sb, gdp), 1,
					   EXT4_FMR_OWN_BLKBM);
		if (error)
			goto err;

		/* Inode bitmap */
		error = ext4_getfsmap_fill(meta_list,
					   ext4_inode_bitmap(sb, gdp), 1,
					   EXT4_FMR_OWN_INOBM);
		if (error)
			goto err;

		/* Inodes */
		error = ext4_getfsmap_fill(meta_list,
					   ext4_inode_table(sb, gdp),
					   EXT4_SB(sb)->s_itb_per_group,
					   EXT4_FMR_OWN_INODES);
		if (error)
			goto err;
	}

	/* Sort the list */
	list_sort(NULL, meta_list, ext4_getfsmap_compare);

	/* Merge adjacent extents */
	ext4_getfsmap_merge_fixed_metadata(meta_list);

	return 0;
err:
	ext4_getfsmap_free_fixed_metadata(meta_list);
	return error;
}
				 struct ext4_fsmap *keys,
				 struct ext4_getfsmap_info *info)
{
	struct ext4_sb_info *sbi = EXT4_SB(sb);
	ext4_fsblk_t start_fsb;
	ext4_fsblk_t end_fsb;
	ext4_fsblk_t eofs;
	ext4_group_t start_ag;
	ext4_group_t end_ag;
	ext4_grpblk_t first_cluster;
	ext4_grpblk_t last_cluster;
	int error = 0;

	eofs = ext4_blocks_count(sbi->s_es);
	if (keys[0].fmr_physical >= eofs)
		return 0;
	if (keys[1].fmr_physical >= eofs)
		keys[1].fmr_physical = eofs - 1;
	start_fsb = keys[0].fmr_physical;
	end_fsb = keys[1].fmr_physical;

	/* Determine first and last group to examine based on start and end */
	ext4_get_group_no_and_offset(sb, start_fsb, &start_ag, &first_cluster);
	ext4_get_group_no_and_offset(sb, end_fsb, &end_ag, &last_cluster);

	/*
	 * Convert the fsmap low/high keys to bg based keys.  Initialize
	 * low to the fsmap low key and max out the high key to the end
	 * of the bg.
	 */
	info->gfi_low = keys[0];
	info->gfi_low.fmr_physical = EXT4_C2B(sbi, first_cluster);
	info->gfi_low.fmr_length = 0;

	memset(&info->gfi_high, 0xFF, sizeof(info->gfi_high));

	/* Assemble a list of all the fixed-location metadata. */
	error = ext4_getfsmap_find_fixed_metadata(sb, &info->gfi_meta_list);
	if (error)
		goto err;

	/* Query each bg */
	for (info->gfi_agno = start_ag;
	     info->gfi_agno <= end_ag;
	     info->gfi_agno++) {
		/*
		 * Set the bg high key from the fsmap high key if this
		 * is the last bg that we're querying.
		 */
		if (info->gfi_agno == end_ag) {
			info->gfi_high = keys[1];
			info->gfi_high.fmr_physical = EXT4_C2B(sbi,
					last_cluster);
			info->gfi_high.fmr_length = 0;
		}

		trace_ext4_fsmap_low_key(sb, info->gfi_dev, info->gfi_agno,
				info->gfi_low.fmr_physical,
				info->gfi_low.fmr_length,
				info->gfi_low.fmr_owner);

		trace_ext4_fsmap_high_key(sb, info->gfi_dev, info->gfi_agno,
				info->gfi_high.fmr_physical,
				info->gfi_high.fmr_length,
				info->gfi_high.fmr_owner);

		error = ext4_mballoc_query_range(sb, info->gfi_agno,
				EXT4_B2C(sbi, info->gfi_low.fmr_physical),
				EXT4_B2C(sbi, info->gfi_high.fmr_physical),
				ext4_getfsmap_datadev_helper, info);
		if (error)
			goto err;

		/*
		 * Set the bg low key to the start of the bg prior to
		 * moving on to the next bg.
		 */
		if (info->gfi_agno == start_ag)
			memset(&info->gfi_low, 0, sizeof(info->gfi_low));
	}

	/* Do we have a retained free extent? */
	if (info->gfi_lastfree.fmr_owner) {
		error = ext4_getfsmap_helper(sb, info, &info->gfi_lastfree);
		if (error)
			goto err;
	}

	/* Report any gaps at the end of the bg */
	info->gfi_last = true;
	error = ext4_getfsmap_datadev_helper(sb, end_ag, last_cluster, 0, info);
	if (error)
		goto err;

err:
	ext4_getfsmap_free_fixed_metadata(&info->gfi_meta_list);
	return error;
}
int ext4_getfsmap(struct super_block *sb, struct ext4_fsmap_head *head,
		  ext4_fsmap_format_t formatter, void *arg)
{
	struct ext4_fsmap dkeys[2];	/* per-dev keys */
	struct ext4_getfsmap_dev handlers[EXT4_GETFSMAP_DEVS];
	struct ext4_getfsmap_info info = {0};
	int i;
	int error = 0;

	if (head->fmh_iflags & ~FMH_IF_VALID)
		return -EINVAL;
	if (!ext4_getfsmap_is_valid_device(sb, &head->fmh_keys[0]) ||
	    !ext4_getfsmap_is_valid_device(sb, &head->fmh_keys[1]))
		return -EINVAL;

	head->fmh_entries = 0;

	/* Set up our device handlers. */
	memset(handlers, 0, sizeof(handlers));
	handlers[0].gfd_dev = new_encode_dev(sb->s_bdev->bd_dev);
	handlers[0].gfd_fn = ext4_getfsmap_datadev;
	if (EXT4_SB(sb)->journal_bdev) {
		handlers[1].gfd_dev = new_encode_dev(
				EXT4_SB(sb)->journal_bdev->bd_dev);
		handlers[1].gfd_fn = ext4_getfsmap_logdev;
	}

	sort(handlers, EXT4_GETFSMAP_DEVS, sizeof(struct ext4_getfsmap_dev),
			ext4_getfsmap_dev_compare, NULL);

	/*
	 * To continue where we left off, we allow userspace to use the
	 * last mapping from a previous call as the low key of the next.
	 * This is identified by a non-zero length in the low key. We
	 * have to increment the low key in this scenario to ensure we
	 * don't return the same mapping again, and instead return the
	 * very next mapping.
	 *
	 * Bump the physical offset as there can be no other mapping for
	 * the same physical block range.
	 */
	dkeys[0] = head->fmh_keys[0];
	dkeys[0].fmr_physical += dkeys[0].fmr_length;
	dkeys[0].fmr_owner = 0;
	dkeys[0].fmr_length = 0;
	memset(&dkeys[1], 0xFF, sizeof(struct ext4_fsmap));

	if (!ext4_getfsmap_check_keys(dkeys, &head->fmh_keys[1]))
		return -EINVAL;

	info.gfi_next_fsblk = head->fmh_keys[0].fmr_physical +
			  head->fmh_keys[0].fmr_length;
	info.gfi_formatter = formatter;
	info.gfi_format_arg = arg;
	info.gfi_head = head;

	/* For each device we support... */
	for (i = 0; i < EXT4_GETFSMAP_DEVS; i++) {
		/* Is this device within the range the user asked for? */
		if (!handlers[i].gfd_fn)
			continue;
		if (head->fmh_keys[0].fmr_device > handlers[i].gfd_dev)
			continue;
		if (head->fmh_keys[1].fmr_device < handlers[i].gfd_dev)
			break;

		/*
		 * If this device number matches the high key, we have
		 * to pass the high key to the handler to limit the
		 * query results.  If the device number exceeds the
		 * low key, zero out the low key so that we get
		 * everything from the beginning.
		 */
		if (handlers[i].gfd_dev == head->fmh_keys[1].fmr_device)
			dkeys[1] = head->fmh_keys[1];
		if (handlers[i].gfd_dev > head->fmh_keys[0].fmr_device)
			memset(&dkeys[0], 0, sizeof(struct ext4_fsmap));

		info.gfi_dev = handlers[i].gfd_dev;
		info.gfi_last = false;
		info.gfi_agno = -1;
		error = handlers[i].gfd_fn(sb, dkeys, &info);
		if (error)
			break;
		info.gfi_next_fsblk = 0;
	}

	head->fmh_oflags = FMH_OF_DEV_T;
	return error;
}
