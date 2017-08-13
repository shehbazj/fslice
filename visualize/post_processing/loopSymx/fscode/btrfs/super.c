
void btrfs_printk(const struct btrfs_fs_info *fs_info, const char *fmt, ...)
{
	struct super_block *sb = fs_info->sb;
	char lvl[PRINTK_MAX_SINGLE_HEADER_LEN + 1] = "\0";
	struct va_format vaf;
	va_list args;
	int kern_level;
	const char *type = logtypes[4];
	struct ratelimit_state *ratelimit = &printk_limits[4];

	va_start(args, fmt);

	while ((kern_level = printk_get_level(fmt)) != 0) {
		size_t size = printk_skip_level(fmt) - fmt;

		if (kern_level >= '0' && kern_level <= '7') {
			memcpy(lvl, fmt,  size);
			lvl[size] = '\0';
			type = logtypes[kern_level - '0'];
			ratelimit = &printk_limits[kern_level - '0'];
		}
		fmt += size;
	}

	vaf.fmt = fmt;
	vaf.va = &args;

	if (__ratelimit(ratelimit))
		printk("%sBTRFS %s (device %s): %pV\n", lvl, type, sb->s_id, &vaf);

	va_end(args);
}
int btrfs_parse_options(struct btrfs_fs_info *info, char *options,
			unsigned long new_flags)
{
	substring_t args[MAX_OPT_ARGS];
	char *p, *num, *orig = NULL;
	u64 cache_gen;
	int intarg;
	int ret = 0;
	char *compress_type;
	bool compress_force = false;
	enum btrfs_compression_type saved_compress_type;
	bool saved_compress_force;
	int no_compress = 0;

	cache_gen = btrfs_super_cache_generation(info->super_copy);
	if (btrfs_fs_compat_ro(info, FREE_SPACE_TREE))
		btrfs_set_opt(info->mount_opt, FREE_SPACE_TREE);
	else if (cache_gen)
		btrfs_set_opt(info->mount_opt, SPACE_CACHE);

	/*
	 * Even the options are empty, we still need to do extra check
	 * against new flags
	 */
	if (!options)
		goto check;

	/*
	 * strsep changes the string, duplicate it because parse_options
	 * gets called twice
	 */
	options = kstrdup(options, GFP_NOFS);
	if (!options)
		return -ENOMEM;

	orig = options;

	while ((p = strsep(&options, ",")) != NULL) {
		int token;
		if (!*p)
			continue;

		token = match_token(p, tokens, args);
		switch (token) {
		case Opt_degraded:
			btrfs_info(info, "allowing degraded mounts");
			btrfs_set_opt(info->mount_opt, DEGRADED);
			break;
		case Opt_subvol:
		case Opt_subvolid:
		case Opt_subvolrootid:
		case Opt_device:
			/*
			 * These are parsed by btrfs_parse_early_options
			 * and can be happily ignored here.
			 */
			break;
		case Opt_nodatasum:
			btrfs_set_and_info(info, NODATASUM,
					   "setting nodatasum");
			break;
		case Opt_datasum:
			if (btrfs_test_opt(info, NODATASUM)) {
				if (btrfs_test_opt(info, NODATACOW))
					btrfs_info(info,
						   "setting datasum, datacow enabled");
				else
					btrfs_info(info, "setting datasum");
			}
			btrfs_clear_opt(info->mount_opt, NODATACOW);
			btrfs_clear_opt(info->mount_opt, NODATASUM);
			break;
		case Opt_nodatacow:
			if (!btrfs_test_opt(info, NODATACOW)) {
				if (!btrfs_test_opt(info, COMPRESS) ||
				    !btrfs_test_opt(info, FORCE_COMPRESS)) {
					btrfs_info(info,
						   "setting nodatacow, compression disabled");
				} else {
					btrfs_info(info, "setting nodatacow");
				}
			}
			btrfs_clear_opt(info->mount_opt, COMPRESS);
			btrfs_clear_opt(info->mount_opt, FORCE_COMPRESS);
			btrfs_set_opt(info->mount_opt, NODATACOW);
			btrfs_set_opt(info->mount_opt, NODATASUM);
			break;
		case Opt_datacow:
			btrfs_clear_and_info(info, NODATACOW,
					     "setting datacow");
			break;
		case Opt_compress_force:
		case Opt_compress_force_type:
			compress_force = true;
			/* Fallthrough */
		case Opt_compress:
		case Opt_compress_type:
			saved_compress_type = btrfs_test_opt(info,
							     COMPRESS) ?
				info->compress_type : BTRFS_COMPRESS_NONE;
			saved_compress_force =
				btrfs_test_opt(info, FORCE_COMPRESS);
			if (token == Opt_compress ||
			    token == Opt_compress_force ||
			    strcmp(args[0].from, "zlib") == 0) {
				compress_type = "zlib";
				info->compress_type = BTRFS_COMPRESS_ZLIB;
				btrfs_set_opt(info->mount_opt, COMPRESS);
				btrfs_clear_opt(info->mount_opt, NODATACOW);
				btrfs_clear_opt(info->mount_opt, NODATASUM);
				no_compress = 0;
			} else if (strcmp(args[0].from, "lzo") == 0) {
				compress_type = "lzo";
				info->compress_type = BTRFS_COMPRESS_LZO;
				btrfs_set_opt(info->mount_opt, COMPRESS);
				btrfs_clear_opt(info->mount_opt, NODATACOW);
				btrfs_clear_opt(info->mount_opt, NODATASUM);
				btrfs_set_fs_incompat(info, COMPRESS_LZO);
				no_compress = 0;
			} else if (strncmp(args[0].from, "no", 2) == 0) {
				compress_type = "no";
				btrfs_clear_opt(info->mount_opt, COMPRESS);
				btrfs_clear_opt(info->mount_opt, FORCE_COMPRESS);
				compress_force = false;
				no_compress++;
			} else {
				ret = -EINVAL;
				goto out;
			}

			if (compress_force) {
				btrfs_set_opt(info->mount_opt, FORCE_COMPRESS);
			} else {
				/*
				 * If we remount from compress-force=xxx to
				 * compress=xxx, we need clear FORCE_COMPRESS
				 * flag, otherwise, there is no way for users
				 * to disable forcible compression separately.
				 */
				btrfs_clear_opt(info->mount_opt, FORCE_COMPRESS);
			}
			if ((btrfs_test_opt(info, COMPRESS) &&
			     (info->compress_type != saved_compress_type ||
			      compress_force != saved_compress_force)) ||
			    (!btrfs_test_opt(info, COMPRESS) &&
			     no_compress == 1)) {
				btrfs_info(info, "%s %s compression",
					   (compress_force) ? "force" : "use",
					   compress_type);
			}
			compress_force = false;
			break;
		case Opt_ssd:
			btrfs_set_and_info(info, SSD,
					   "use ssd allocation scheme");
			btrfs_clear_opt(info->mount_opt, NOSSD);
			break;
		case Opt_ssd_spread:
			btrfs_set_and_info(info, SSD_SPREAD,
					   "use spread ssd allocation scheme");
			btrfs_set_opt(info->mount_opt, SSD);
			btrfs_clear_opt(info->mount_opt, NOSSD);
			break;
		case Opt_nossd:
			btrfs_set_and_info(info, NOSSD,
					     "not using ssd allocation scheme");
			btrfs_clear_opt(info->mount_opt, SSD);
			btrfs_clear_opt(info->mount_opt, SSD_SPREAD);
			break;
		case Opt_barrier:
			btrfs_clear_and_info(info, NOBARRIER,
					     "turning on barriers");
			break;
		case Opt_nobarrier:
			btrfs_set_and_info(info, NOBARRIER,
					   "turning off barriers");
			break;
		case Opt_thread_pool:
			ret = match_int(&args[0], &intarg);
			if (ret) {
				goto out;
			} else if (intarg > 0) {
				info->thread_pool_size = intarg;
			} else {
				ret = -EINVAL;
				goto out;
			}
			break;
		case Opt_max_inline:
			num = match_strdup(&args[0]);
			if (num) {
				info->max_inline = memparse(num, NULL);
				kfree(num);

				if (info->max_inline) {
					info->max_inline = min_t(u64,
						info->max_inline,
						info->sectorsize);
				}
				btrfs_info(info, "max_inline at %llu",
					   info->max_inline);
			} else {
				ret = -ENOMEM;
				goto out;
			}
			break;
		case Opt_alloc_start:
			num = match_strdup(&args[0]);
			if (num) {
				mutex_lock(&info->chunk_mutex);
				info->alloc_start = memparse(num, NULL);
				mutex_unlock(&info->chunk_mutex);
				kfree(num);
				btrfs_info(info, "allocations start at %llu",
					   info->alloc_start);
			} else {
				ret = -ENOMEM;
				goto out;
			}
			break;
		case Opt_acl:
#ifdef CONFIG_BTRFS_FS_POSIX_ACL
			info->sb->s_flags |= MS_POSIXACL;
			break;
#else
			btrfs_err(info, "support for ACL not compiled in!");
			ret = -EINVAL;
			goto out;
#endif
		case Opt_noacl:
			info->sb->s_flags &= ~MS_POSIXACL;
			break;
		case Opt_notreelog:
			btrfs_set_and_info(info, NOTREELOG,
					   "disabling tree log");
			break;
		case Opt_treelog:
			btrfs_clear_and_info(info, NOTREELOG,
					     "enabling tree log");
			break;
		case Opt_norecovery:
		case Opt_nologreplay:
			btrfs_set_and_info(info, NOLOGREPLAY,
					   "disabling log replay at mount time");
			break;
		case Opt_flushoncommit:
			btrfs_set_and_info(info, FLUSHONCOMMIT,
					   "turning on flush-on-commit");
			break;
		case Opt_noflushoncommit:
			btrfs_clear_and_info(info, FLUSHONCOMMIT,
					     "turning off flush-on-commit");
			break;
		case Opt_ratio:
			ret = match_int(&args[0], &intarg);
			if (ret) {
				goto out;
			} else if (intarg >= 0) {
				info->metadata_ratio = intarg;
				btrfs_info(info, "metadata ratio %d",
					   info->metadata_ratio);
			} else {
				ret = -EINVAL;
				goto out;
			}
			break;
		case Opt_discard:
			btrfs_set_and_info(info, DISCARD,
					   "turning on discard");
			break;
		case Opt_nodiscard:
			btrfs_clear_and_info(info, DISCARD,
					     "turning off discard");
			break;
		case Opt_space_cache:
		case Opt_space_cache_version:
			if (token == Opt_space_cache ||
			    strcmp(args[0].from, "v1") == 0) {
				btrfs_clear_opt(info->mount_opt,
						FREE_SPACE_TREE);
				btrfs_set_and_info(info, SPACE_CACHE,
					   "enabling disk space caching");
			} else if (strcmp(args[0].from, "v2") == 0) {
				btrfs_clear_opt(info->mount_opt,
						SPACE_CACHE);
				btrfs_set_and_info(info, FREE_SPACE_TREE,
						   "enabling free space tree");
			} else {
				ret = -EINVAL;
				goto out;
			}
			break;
		case Opt_rescan_uuid_tree:
			btrfs_set_opt(info->mount_opt, RESCAN_UUID_TREE);
			break;
		case Opt_no_space_cache:
			if (btrfs_test_opt(info, SPACE_CACHE)) {
				btrfs_clear_and_info(info, SPACE_CACHE,
					     "disabling disk space caching");
			}
			if (btrfs_test_opt(info, FREE_SPACE_TREE)) {
				btrfs_clear_and_info(info, FREE_SPACE_TREE,
					     "disabling free space tree");
			}
			break;
		case Opt_inode_cache:
			btrfs_set_pending_and_info(info, INODE_MAP_CACHE,
					   "enabling inode map caching");
			break;
		case Opt_noinode_cache:
			btrfs_clear_pending_and_info(info, INODE_MAP_CACHE,
					     "disabling inode map caching");
			break;
		case Opt_clear_cache:
			btrfs_set_and_info(info, CLEAR_CACHE,
					   "force clearing of disk cache");
			break;
		case Opt_user_subvol_rm_allowed:
			btrfs_set_opt(info->mount_opt, USER_SUBVOL_RM_ALLOWED);
			break;
		case Opt_enospc_debug:
			btrfs_set_opt(info->mount_opt, ENOSPC_DEBUG);
			break;
		case Opt_noenospc_debug:
			btrfs_clear_opt(info->mount_opt, ENOSPC_DEBUG);
			break;
		case Opt_defrag:
			btrfs_set_and_info(info, AUTO_DEFRAG,
					   "enabling auto defrag");
			break;
		case Opt_nodefrag:
			btrfs_clear_and_info(info, AUTO_DEFRAG,
					     "disabling auto defrag");
			break;
		case Opt_recovery:
			btrfs_warn(info,
				   "'recovery' is deprecated, use 'usebackuproot' instead");
		case Opt_usebackuproot:
			btrfs_info(info,
				   "trying to use backup root at mount time");
			btrfs_set_opt(info->mount_opt, USEBACKUPROOT);
			break;
		case Opt_skip_balance:
			btrfs_set_opt(info->mount_opt, SKIP_BALANCE);
			break;
#ifdef CONFIG_BTRFS_FS_CHECK_INTEGRITY
		case Opt_check_integrity_including_extent_data:
			btrfs_info(info,
				   "enabling check integrity including extent data");
			btrfs_set_opt(info->mount_opt,
				      CHECK_INTEGRITY_INCLUDING_EXTENT_DATA);
			btrfs_set_opt(info->mount_opt, CHECK_INTEGRITY);
			break;
		case Opt_check_integrity:
			btrfs_info(info, "enabling check integrity");
			btrfs_set_opt(info->mount_opt, CHECK_INTEGRITY);
			break;
		case Opt_check_integrity_print_mask:
			ret = match_int(&args[0], &intarg);
			if (ret) {
				goto out;
			} else if (intarg >= 0) {
				info->check_integrity_print_mask = intarg;
				btrfs_info(info,
					   "check_integrity_print_mask 0x%x",
					   info->check_integrity_print_mask);
			} else {
				ret = -EINVAL;
				goto out;
			}
			break;
#else
		case Opt_check_integrity_including_extent_data:
		case Opt_check_integrity:
		case Opt_check_integrity_print_mask:
			btrfs_err(info,
				  "support for check_integrity* not compiled in!");
			ret = -EINVAL;
			goto out;
#endif
		case Opt_fatal_errors:
			if (strcmp(args[0].from, "panic") == 0)
				btrfs_set_opt(info->mount_opt,
					      PANIC_ON_FATAL_ERROR);
			else if (strcmp(args[0].from, "bug") == 0)
				btrfs_clear_opt(info->mount_opt,
					      PANIC_ON_FATAL_ERROR);
			else {
				ret = -EINVAL;
				goto out;
			}
			break;
		case Opt_commit_interval:
			intarg = 0;
			ret = match_int(&args[0], &intarg);
			if (ret < 0) {
				btrfs_err(info, "invalid commit interval");
				ret = -EINVAL;
				goto out;
			}
			if (intarg > 0) {
				if (intarg > 300) {
					btrfs_warn(info,
						"excessive commit interval %d",
						intarg);
				}
				info->commit_interval = intarg;
			} else {
				btrfs_info(info,
					   "using default commit interval %ds",
					   BTRFS_DEFAULT_COMMIT_INTERVAL);
				info->commit_interval = BTRFS_DEFAULT_COMMIT_INTERVAL;
			}
			break;
#ifdef CONFIG_BTRFS_DEBUG
		case Opt_fragment_all:
			btrfs_info(info, "fragmenting all space");
			btrfs_set_opt(info->mount_opt, FRAGMENT_DATA);
			btrfs_set_opt(info->mount_opt, FRAGMENT_METADATA);
			break;
		case Opt_fragment_metadata:
			btrfs_info(info, "fragmenting metadata");
			btrfs_set_opt(info->mount_opt,
				      FRAGMENT_METADATA);
			break;
		case Opt_fragment_data:
			btrfs_info(info, "fragmenting data");
			btrfs_set_opt(info->mount_opt, FRAGMENT_DATA);
			break;
#endif
		case Opt_err:
			btrfs_info(info, "unrecognized mount option '%s'", p);
			ret = -EINVAL;
			goto out;
		default:
			break;
		}
	}
check:
	/*
	 * Extra check for current option against current flag
	 */
	if (btrfs_test_opt(info, NOLOGREPLAY) && !(new_flags & MS_RDONLY)) {
		btrfs_err(info,
			  "nologreplay must be used with ro mount option");
		ret = -EINVAL;
	}
out:
	if (btrfs_fs_compat_ro(info, FREE_SPACE_TREE) &&
	    !btrfs_test_opt(info, FREE_SPACE_TREE) &&
	    !btrfs_test_opt(info, CLEAR_CACHE)) {
		btrfs_err(info, "cannot disable free space tree");
		ret = -EINVAL;

	}
	if (!ret && btrfs_test_opt(info, SPACE_CACHE))
		btrfs_info(info, "disk space caching is enabled");
	if (!ret && btrfs_test_opt(info, FREE_SPACE_TREE))
		btrfs_info(info, "using free space tree");
	kfree(orig);
	return ret;
}
		void *holder, char **subvol_name, u64 *subvol_objectid,
		struct btrfs_fs_devices **fs_devices)
{
	substring_t args[MAX_OPT_ARGS];
	char *device_name, *opts, *orig, *p;
	char *num = NULL;
	int error = 0;

	if (!options)
		return 0;

	/*
	 * strsep changes the string, duplicate it because parse_options
	 * gets called twice
	 */
	opts = kstrdup(options, GFP_KERNEL);
	if (!opts)
		return -ENOMEM;
	orig = opts;

	while ((p = strsep(&opts, ",")) != NULL) {
		int token;
		if (!*p)
			continue;

		token = match_token(p, tokens, args);
		switch (token) {
		case Opt_subvol:
			kfree(*subvol_name);
			*subvol_name = match_strdup(&args[0]);
			if (!*subvol_name) {
				error = -ENOMEM;
				goto out;
			}
			break;
		case Opt_subvolid:
			num = match_strdup(&args[0]);
			if (num) {
				*subvol_objectid = memparse(num, NULL);
				kfree(num);
				/* we want the original fs_tree */
				if (!*subvol_objectid)
					*subvol_objectid =
						BTRFS_FS_TREE_OBJECTID;
			} else {
				error = -EINVAL;
				goto out;
			}
			break;
		case Opt_subvolrootid:
			pr_warn("BTRFS: 'subvolrootid' mount option is deprecated and has no effect\n");
			break;
		case Opt_device:
			device_name = match_strdup(&args[0]);
			if (!device_name) {
				error = -ENOMEM;
				goto out;
			}
			error = btrfs_scan_one_device(device_name,
					flags, holder, fs_devices);
			kfree(device_name);
			if (error)
				goto out;
			break;
		default:
			break;
		}
	}

out:
	kfree(orig);
	return error;
}
static char *get_subvol_name_from_objectid(struct btrfs_fs_info *fs_info,
					   u64 subvol_objectid)
{
	struct btrfs_root *root = fs_info->tree_root;
	struct btrfs_root *fs_root;
	struct btrfs_root_ref *root_ref;
	struct btrfs_inode_ref *inode_ref;
	struct btrfs_key key;
	struct btrfs_path *path = NULL;
	char *name = NULL, *ptr;
	u64 dirid;
	int len;
	int ret;

	path = btrfs_alloc_path();
	if (!path) {
		ret = -ENOMEM;
		goto err;
	}
	path->leave_spinning = 1;

	name = kmalloc(PATH_MAX, GFP_NOFS);
	if (!name) {
		ret = -ENOMEM;
		goto err;
	}
	ptr = name + PATH_MAX - 1;
	ptr[0] = '\0';

	/*
	 * Walk up the subvolume trees in the tree of tree roots by root
	 * backrefs until we hit the top-level subvolume.
	 */
	while (subvol_objectid != BTRFS_FS_TREE_OBJECTID) {
		key.objectid = subvol_objectid;
		key.type = BTRFS_ROOT_BACKREF_KEY;
		key.offset = (u64)-1;

		ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
		if (ret < 0) {
			goto err;
		} else if (ret > 0) {
			ret = btrfs_previous_item(root, path, subvol_objectid,
						  BTRFS_ROOT_BACKREF_KEY);
			if (ret < 0) {
				goto err;
			} else if (ret > 0) {
				ret = -ENOENT;
				goto err;
			}
		}

		btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);
		subvol_objectid = key.offset;

		root_ref = btrfs_item_ptr(path->nodes[0], path->slots[0],
					  struct btrfs_root_ref);
		len = btrfs_root_ref_name_len(path->nodes[0], root_ref);
		ptr -= len + 1;
		if (ptr < name) {
			ret = -ENAMETOOLONG;
			goto err;
		}
		read_extent_buffer(path->nodes[0], ptr + 1,
				   (unsigned long)(root_ref + 1), len);
		ptr[0] = '/';
		dirid = btrfs_root_ref_dirid(path->nodes[0], root_ref);
		btrfs_release_path(path);

		key.objectid = subvol_objectid;
		key.type = BTRFS_ROOT_ITEM_KEY;
		key.offset = (u64)-1;
		fs_root = btrfs_read_fs_root_no_name(fs_info, &key);
		if (IS_ERR(fs_root)) {
			ret = PTR_ERR(fs_root);
			goto err;
		}

		/*
		 * Walk up the filesystem tree by inode refs until we hit the
		 * root directory.
		 */
		while (dirid != BTRFS_FIRST_FREE_OBJECTID) {
			key.objectid = dirid;
			key.type = BTRFS_INODE_REF_KEY;
			key.offset = (u64)-1;

			ret = btrfs_search_slot(NULL, fs_root, &key, path, 0, 0);
			if (ret < 0) {
				goto err;
			} else if (ret > 0) {
				ret = btrfs_previous_item(fs_root, path, dirid,
							  BTRFS_INODE_REF_KEY);
				if (ret < 0) {
					goto err;
				} else if (ret > 0) {
					ret = -ENOENT;
					goto err;
				}
			}

			btrfs_item_key_to_cpu(path->nodes[0], &key, path->slots[0]);
			dirid = key.offset;

			inode_ref = btrfs_item_ptr(path->nodes[0],
						   path->slots[0],
						   struct btrfs_inode_ref);
			len = btrfs_inode_ref_name_len(path->nodes[0],
						       inode_ref);
			ptr -= len + 1;
			if (ptr < name) {
				ret = -ENAMETOOLONG;
				goto err;
			}
			read_extent_buffer(path->nodes[0], ptr + 1,
					   (unsigned long)(inode_ref + 1), len);
			ptr[0] = '/';
			btrfs_release_path(path);
		}
	}

	btrfs_free_path(path);
	if (ptr == name + PATH_MAX - 1) {
		name[0] = '/';
		name[1] = '\0';
	} else {
		memmove(name, ptr, name + PATH_MAX - ptr);
	}
	return name;

err:
	btrfs_free_path(path);
	kfree(name);
	return ERR_PTR(ret);
}
 */
static char *setup_root_args(char *args)
{
	char *buf, *dst, *sep;

	if (!args)
		return kstrdup("subvolid=0", GFP_NOFS);

	/* The worst case is that we add ",subvolid=0" to the end. */
	buf = dst = kmalloc(strlen(args) + strlen(",subvolid=0") + 1, GFP_NOFS);
	if (!buf)
		return NULL;

	while (1) {
		sep = strchrnul(args, ',');
		if (!strstarts(args, "subvol=") &&
		    !strstarts(args, "subvolid=")) {
			memcpy(dst, args, sep - args);
			dst += sep - args;
			*dst++ = ',';
		}
		if (*sep)
			args = sep + 1;
		else
			break;
	}
	strcpy(dst, "subvolid=0");

	return buf;
}
static int btrfs_calc_avail_data_space(struct btrfs_fs_info *fs_info,
				       u64 *free_bytes)
{
	struct btrfs_root *root = fs_info->tree_root;
	struct btrfs_device_info *devices_info;
	struct btrfs_fs_devices *fs_devices = fs_info->fs_devices;
	struct btrfs_device *device;
	u64 skip_space;
	u64 type;
	u64 avail_space;
	u64 used_space;
	u64 min_stripe_size;
	int min_stripes = 1, num_stripes = 1;
	int i = 0, nr_devices;
	int ret;

	/*
	 * We aren't under the device list lock, so this is racy-ish, but good
	 * enough for our purposes.
	 */
	nr_devices = fs_info->fs_devices->open_devices;
	if (!nr_devices) {
		smp_mb();
		nr_devices = fs_info->fs_devices->open_devices;
		ASSERT(nr_devices);
		if (!nr_devices) {
			*free_bytes = 0;
			return 0;
		}
	}

	devices_info = kmalloc_array(nr_devices, sizeof(*devices_info),
			       GFP_NOFS);
	if (!devices_info)
		return -ENOMEM;

	/* calc min stripe number for data space allocation */
	type = btrfs_get_alloc_profile(root, 1);
	if (type & BTRFS_BLOCK_GROUP_RAID0) {
		min_stripes = 2;
		num_stripes = nr_devices;
	} else if (type & BTRFS_BLOCK_GROUP_RAID1) {
		min_stripes = 2;
		num_stripes = 2;
	} else if (type & BTRFS_BLOCK_GROUP_RAID10) {
		min_stripes = 4;
		num_stripes = 4;
	}

	if (type & BTRFS_BLOCK_GROUP_DUP)
		min_stripe_size = 2 * BTRFS_STRIPE_LEN;
	else
		min_stripe_size = BTRFS_STRIPE_LEN;

	if (fs_info->alloc_start)
		mutex_lock(&fs_devices->device_list_mutex);
	rcu_read_lock();
	list_for_each_entry_rcu(device, &fs_devices->devices, dev_list) {
		if (!device->in_fs_metadata || !device->bdev ||
		    device->is_tgtdev_for_dev_replace)
			continue;

		if (i >= nr_devices)
			break;

		avail_space = device->total_bytes - device->bytes_used;

		/* align with stripe_len */
		avail_space = div_u64(avail_space, BTRFS_STRIPE_LEN);
		avail_space *= BTRFS_STRIPE_LEN;

		/*
		 * In order to avoid overwriting the superblock on the drive,
		 * btrfs starts at an offset of at least 1MB when doing chunk
		 * allocation.
		 */
		skip_space = SZ_1M;

		/* user can set the offset in fs_info->alloc_start. */
		if (fs_info->alloc_start &&
		    fs_info->alloc_start + BTRFS_STRIPE_LEN <=
		    device->total_bytes) {
			rcu_read_unlock();
			skip_space = max(fs_info->alloc_start, skip_space);

			/*
			 * btrfs can not use the free space in
			 * [0, skip_space - 1], we must subtract it from the
			 * total. In order to implement it, we account the used
			 * space in this range first.
			 */
			ret = btrfs_account_dev_extents_size(device, 0,
							     skip_space - 1,
							     &used_space);
			if (ret) {
				kfree(devices_info);
				mutex_unlock(&fs_devices->device_list_mutex);
				return ret;
			}

			rcu_read_lock();

			/* calc the free space in [0, skip_space - 1] */
			skip_space -= used_space;
		}

		/*
		 * we can use the free space in [0, skip_space - 1], subtract
		 * it from the total.
		 */
		if (avail_space && avail_space >= skip_space)
			avail_space -= skip_space;
		else
			avail_space = 0;

		if (avail_space < min_stripe_size)
			continue;

		devices_info[i].dev = device;
		devices_info[i].max_avail = avail_space;

		i++;
	}
	rcu_read_unlock();
	if (fs_info->alloc_start)
		mutex_unlock(&fs_devices->device_list_mutex);

	nr_devices = i;

	btrfs_descending_sort_devices(devices_info, nr_devices);

	i = nr_devices - 1;
	avail_space = 0;
	while (nr_devices >= min_stripes) {
		if (num_stripes > nr_devices)
			num_stripes = nr_devices;

		if (devices_info[i].max_avail >= min_stripe_size) {
			int j;
			u64 alloc_size;

			avail_space += devices_info[i].max_avail * num_stripes;
			alloc_size = devices_info[i].max_avail;
			for (j = i + 1 - num_stripes; j <= i; j++)
				devices_info[j].max_avail -= alloc_size;
		}
		i--;
		nr_devices--;
	}

	kfree(devices_info);
	*free_bytes = avail_space;
	return 0;
}
 */
static int btrfs_statfs(struct dentry *dentry, struct kstatfs *buf)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(dentry->d_sb);
	struct btrfs_super_block *disk_super = fs_info->super_copy;
	struct list_head *head = &fs_info->space_info;
	struct btrfs_space_info *found;
	u64 total_used = 0;
	u64 total_free_data = 0;
	u64 total_free_meta = 0;
	int bits = dentry->d_sb->s_blocksize_bits;
	__be32 *fsid = (__be32 *)fs_info->fsid;
	unsigned factor = 1;
	struct btrfs_block_rsv *block_rsv = &fs_info->global_block_rsv;
	int ret;
	u64 thresh = 0;
	int mixed = 0;

	rcu_read_lock();
	list_for_each_entry_rcu(found, head, list) {
		if (found->flags & BTRFS_BLOCK_GROUP_DATA) {
			int i;

			total_free_data += found->disk_total - found->disk_used;
			total_free_data -=
				btrfs_account_ro_block_groups_free_space(found);

			for (i = 0; i < BTRFS_NR_RAID_TYPES; i++) {
				if (!list_empty(&found->block_groups[i])) {
					switch (i) {
					case BTRFS_RAID_DUP:
					case BTRFS_RAID_RAID1:
					case BTRFS_RAID_RAID10:
						factor = 2;
					}
				}
			}
		}

		/*
		 * Metadata in mixed block goup profiles are accounted in data
		 */
		if (!mixed && found->flags & BTRFS_BLOCK_GROUP_METADATA) {
			if (found->flags & BTRFS_BLOCK_GROUP_DATA)
				mixed = 1;
			else
				total_free_meta += found->disk_total -
					found->disk_used;
		}

		total_used += found->disk_used;
	}

	rcu_read_unlock();

	buf->f_blocks = div_u64(btrfs_super_total_bytes(disk_super), factor);
	buf->f_blocks >>= bits;
	buf->f_bfree = buf->f_blocks - (div_u64(total_used, factor) >> bits);

	/* Account global block reserve as used, it's in logical size already */
	spin_lock(&block_rsv->lock);
	/* Mixed block groups accounting is not byte-accurate, avoid overflow */
	if (buf->f_bfree >= block_rsv->size >> bits)
		buf->f_bfree -= block_rsv->size >> bits;
	else
		buf->f_bfree = 0;
	spin_unlock(&block_rsv->lock);

	buf->f_bavail = div_u64(total_free_data, factor);
	ret = btrfs_calc_avail_data_space(fs_info, &total_free_data);
	if (ret)
		return ret;
	buf->f_bavail += div_u64(total_free_data, factor);
	buf->f_bavail = buf->f_bavail >> bits;

	/*
	 * We calculate the remaining metadata space minus global reserve. If
	 * this is (supposedly) smaller than zero, there's no space. But this
	 * does not hold in practice, the exhausted state happens where's still
	 * some positive delta. So we apply some guesswork and compare the
	 * delta to a 4M threshold.  (Practically observed delta was ~2M.)
	 *
	 * We probably cannot calculate the exact threshold value because this
	 * depends on the internal reservations requested by various
	 * operations, so some operations that consume a few metadata will
	 * succeed even if the Avail is zero. But this is better than the other
	 * way around.
	 */
	thresh = 4 * 1024 * 1024;

	if (!mixed && total_free_meta - thresh < block_rsv->size)
		buf->f_bavail = 0;

	buf->f_type = BTRFS_SUPER_MAGIC;
	buf->f_bsize = dentry->d_sb->s_blocksize;
	buf->f_namelen = BTRFS_NAME_LEN;

	/* We treat it as constant endianness (it doesn't matter _which_)
	   because we want the fsid to come out the same whether mounted
	   on a big-endian or little-endian host */
	buf->f_fsid.val[0] = be32_to_cpu(fsid[0]) ^ be32_to_cpu(fsid[2]);
	buf->f_fsid.val[1] = be32_to_cpu(fsid[1]) ^ be32_to_cpu(fsid[3]);
	/* Mask in the root object ID too, to disambiguate subvols */
	buf->f_fsid.val[0] ^= BTRFS_I(d_inode(dentry))->root->objectid >> 32;
	buf->f_fsid.val[1] ^= BTRFS_I(d_inode(dentry))->root->objectid;

	return 0;
}

static int btrfs_show_devname(struct seq_file *m, struct dentry *root)
{
	struct btrfs_fs_info *fs_info = btrfs_sb(root->d_sb);
	struct btrfs_fs_devices *cur_devices;
	struct btrfs_device *dev, *first_dev = NULL;
	struct list_head *head;
	struct rcu_string *name;

	mutex_lock(&fs_info->fs_devices->device_list_mutex);
	cur_devices = fs_info->fs_devices;
	while (cur_devices) {
		head = &cur_devices->devices;
		list_for_each_entry(dev, head, dev_list) {
			if (dev->missing)
				continue;
			if (!dev->name)
				continue;
			if (!first_dev || dev->devid < first_dev->devid)
				first_dev = dev;
		}
		cur_devices = cur_devices->seed;
	}

	if (first_dev) {
		rcu_read_lock();
		name = rcu_dereference(first_dev->name);
		seq_escape(m, name->str, " \t\n\\");
		rcu_read_unlock();
	} else {
		WARN_ON(1);
	}
	mutex_unlock(&fs_info->fs_devices->device_list_mutex);
	return 0;
}
