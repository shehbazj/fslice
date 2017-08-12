
int ext4_register_sysfs(struct super_block *sb)
{
	struct ext4_sb_info *sbi = EXT4_SB(sb);
	const struct ext4_proc_files *p;
	int err;

	sbi->s_kobj.kset = &ext4_kset;
	init_completion(&sbi->s_kobj_unregister);
	err = kobject_init_and_add(&sbi->s_kobj, &ext4_sb_ktype, NULL,
				   "%s", sb->s_id);
	if (err)
		return err;

	if (ext4_proc_root)
		sbi->s_proc = proc_mkdir(sb->s_id, ext4_proc_root);

	if (sbi->s_proc) {
		for (p = proc_files; p->name; p++)
			proc_create_data(p->name, S_IRUGO, sbi->s_proc,
					 p->fops, sb);
	}
	return 0;
}

void ext4_unregister_sysfs(struct super_block *sb)
{
	struct ext4_sb_info *sbi = EXT4_SB(sb);
	const struct ext4_proc_files *p;

	if (sbi->s_proc) {
		for (p = proc_files; p->name; p++)
			remove_proc_entry(p->name, sbi->s_proc);
		remove_proc_entry(sb->s_id, ext4_proc_root);
	}
	kobject_del(&sbi->s_kobj);
}
