
#include<stdint.h>
#include<sys/types.h>


struct list_head {
    struct list_head *next, *prev;
};

struct hlist_node {
        struct hlist_node *next, **pprev;
};

typedef unsigned int ext4_group_t;

/* data type for filesystem-wide blocks number */
typedef unsigned long long ext4_fsblk_t;

typedef struct {
        uint64_t counter;
} atomic64_t;

typedef struct {
        gid_t val;
} kgid_t;

typedef struct {
        uid_t val;
} kuid_t;

#define aligned_u64 __u64 __attribute__((aligned(8)))

typedef struct {
        volatile unsigned int lock;
} arch_spinlock_t;



typedef struct raw_spinlock {
        arch_spinlock_t raw_lock;
#ifdef CONFIG_GENERIC_LOCKBREAK
        unsigned int break_lock;
#endif
#ifdef CONFIG_DEBUG_SPINLOCK
        unsigned int magic, owner_cpu;
        void *owner;
#endif
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map dep_map;
#endif
} raw_spinlock_t;

struct ratelimit_state {
        raw_spinlock_t  lock;           /* protect the state */

        int             interval;
        int             burst;
        int             printed;
        int             missed;
        unsigned long   begin;
        unsigned long   flags;
};

struct rcuwait {
        struct task_struct *task;
};

typedef struct spinlock {
        union { 
                struct raw_spinlock rlock;

#ifdef CONFIG_DEBUG_LOCK_ALLOC
# define LOCK_PADSIZE (offsetof(struct raw_spinlock, dep_map))
                struct {
                        u8 __padding[LOCK_PADSIZE];
                        struct lockdep_map dep_map;
                };
#endif  
        };
} spinlock_t;



struct __wait_queue_head {
        spinlock_t              lock;
        struct list_head        task_list;
};
typedef struct __wait_queue_head wait_queue_head_t;



enum rcu_sync_type { RCU_SYNC, RCU_SCHED_SYNC, RCU_BH_SYNC };


struct cds_wfcq_node {
        struct cds_wfcq_node *next;
};



struct rcu_head {
        struct cds_wfcq_node next;
        void (*func)(struct rcu_head *head);
};

/* Structure to mediate between updaters and fastpath-using readers.  */
struct rcu_sync {
        int                     gp_state;
        int                     gp_count;
        wait_queue_head_t       gp_wait;

        int                     cb_state;
        struct rcu_head         cb_head;

        enum rcu_sync_type      gp_type;
};

struct rw_semaphore {
        uint32_t                   count;
        raw_spinlock_t          wait_lock;
        struct list_head        wait_list;
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map dep_map;
#endif
};


struct percpu_rw_semaphore {
        struct rcu_sync         rss;
        unsigned int   *read_count;
        struct rw_semaphore     rw_sem; /* slowpath */
        struct rcuwait          writer; /* blocked writer */
        int                     readers_block;
};

#define u32 unsigned int

#define aligned_u64 __u64 __attribute__((aligned(8)))
struct kref {
        uint64_t refcount;
};


typedef struct {
        int counter;
} atomic_t;

typedef atomic_t atomic_long_t;

struct rb_node {
        unsigned long  __rb_parent_color;
        struct rb_node *rb_right;
        struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
    /* The alignment might seem pointless, but allegedly CRIS needs it */

struct rb_root {
        struct rb_node *rb_node;
};

struct percpu_counter {
        raw_spinlock_t lock;
        uint64_t count;
#ifdef CONFIG_HOTPLUG_CPU
        struct list_head list;  /* All percpu_counters are on a list */
#endif  
        uint32_t *counters;
};

struct kobject {
        const char              *name;
        struct list_head        entry;
        struct kobject          *parent;
        struct kset             *kset;
        struct kobj_type        *ktype;
        struct kernfs_node      *sd; /* sysfs directory entry */
        struct kref             kref;
#ifdef CONFIG_DEBUG_KOBJECT_RELEASE
        struct delayed_work     release;
#endif
        unsigned int state_initialized:1;
        unsigned int state_in_sysfs:1;
        unsigned int state_add_uevent_sent:1;
        unsigned int state_remove_uevent_sent:1;
        unsigned int uevent_suppress:1;
};

struct completion {
        /* Hopefuly this won't overflow. */
        unsigned int count;
};

struct mutex {
        atomic_long_t           owner;
        spinlock_t              wait_lock;
#ifdef CONFIG_MUTEX_SPIN_ON_OWNER
        struct optimistic_spin_queue osq; /* Spinner MCS lock */
#endif
        struct list_head        wait_list;
#ifdef CONFIG_DEBUG_MUTEXES
        void                    *magic;
#endif
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map      dep_map;
#endif
};

#define PREALLOC_TB_SIZE 10
struct ext4_locality_group {
        /* for allocator */
        /* to serialize allocates */
        struct mutex            lg_mutex;
        /* list of preallocations */
        struct list_head        lg_prealloc_list[PREALLOC_TB_SIZE];
        spinlock_t              lg_prealloc_lock;
};

struct timer_list {
        /*
 *          * All fields that change during normal runtime grouped to the
 *                   * same cacheline
 *                            */
        struct hlist_node       entry;
        unsigned long           expires;
        void                    (*function)(unsigned long);
        unsigned long           data;
        u32                     flags;

#ifdef CONFIG_LOCKDEP
        struct lockdep_map      lockdep_map;
#endif
};

struct shrinker {
        unsigned long (*count_objects)(struct shrinker *,
                                       struct shrink_control *sc);
        unsigned long (*scan_objects)(struct shrinker *,
                                      struct shrink_control *sc);

        int seeks;      /* seeks to recreate an obj */
        long batch;     /* reclaim batch size, 0 = default */
        unsigned long flags;

        /* These are for internal use */
        struct list_head list;
        /* objs pending delete, per node */
        atomic_long_t *nr_deferred;
};

struct ext4_es_stats {
        unsigned long es_stats_shrunk;
        unsigned long es_stats_cache_hits;
        unsigned long es_stats_cache_misses;
        uint64_t es_stats_scan_time;
        uint64_t es_stats_max_scan_time;
        struct percpu_counter es_stats_all_cnt;
        struct percpu_counter es_stats_shk_cnt;
};

struct ext4_sb_info {
        unsigned long s_desc_size;      /* Size of a group descriptor in bytes */
        unsigned long s_inodes_per_block;/* Number of inodes per block */
        unsigned long s_blocks_per_group;/* Number of blocks in a group */
        unsigned long s_clusters_per_group; /* Number of clusters in a group */
        unsigned long s_inodes_per_group;/* Number of inodes in a group */
        unsigned long s_itb_per_group;  /* Number of inode table blocks per group */
        unsigned long s_gdb_count;      /* Number of group descriptor blocks */
        unsigned long s_desc_per_block; /* Number of group descriptors per block */
        ext4_group_t s_groups_count;    /* Number of groups in the fs */
        ext4_group_t s_blockfile_groups;/* Groups acceptable for non-extent files */
        unsigned long s_overhead;  /* # of fs overhead clusters */
        unsigned int s_cluster_ratio;   /* Number of blocks per cluster */
        unsigned int s_cluster_bits;    /* log2 of s_cluster_ratio */
        off_t s_bitmap_maxbytes;       /* max bytes for bitmap files */
        struct buffer_head * s_sbh;     /* Buffer containing the super block */
        struct ext4_super_block *s_es;  /* Pointer to the super block in the buffer */
        struct buffer_head **s_group_desc;
        unsigned int s_mount_opt;
        unsigned int s_mount_opt2;
        unsigned int s_mount_flags;
        unsigned int s_def_mount_opt;
        ext4_fsblk_t s_sb_block;
        atomic64_t s_resv_clusters;
        kuid_t s_resuid;
        kgid_t s_resgid;
        unsigned short s_mount_state;
        unsigned short s_pad;
        int s_addr_per_block_bits;
        int s_desc_per_block_bits;
        int s_inode_size;
        int s_first_ino;
        unsigned int s_inode_readahead_blks;
        unsigned int s_inode_goal;
        spinlock_t s_next_gen_lock;
        u32 s_next_generation;
        u32 s_hash_seed[4];
        int s_def_hash_version;
        int s_hash_unsigned;    /* 3 if hash should be signed, 0 if not */
        struct percpu_counter s_freeclusters_counter;
        struct percpu_counter s_freeinodes_counter;
        struct percpu_counter s_dirs_counter;

 struct percpu_counter s_dirtyclusters_counter;
        struct blockgroup_lock *s_blockgroup_lock;
        struct proc_dir_entry *s_proc;
        struct kobject s_kobj;
        struct completion s_kobj_unregister;
        struct super_block *s_sb;

        /* Journaling */
        struct journal_s *s_journal;
        struct list_head s_orphan;
        struct mutex s_orphan_lock;
        unsigned long s_ext4_flags;             /* Ext4 superblock flags */
        unsigned long s_commit_interval;
        u32 s_max_batch_time;
        u32 s_min_batch_time;
        struct block_device *journal_bdev;
#ifdef CONFIG_QUOTA
        char *s_qf_names[EXT4_MAXQUOTAS];       /* Names of quota files with journalled quota */
        int s_jquota_fmt;                       /* Format of quota to use */
#endif
        unsigned int s_want_extra_isize; /* New inodes should reserve # bytes */
        struct rb_root system_blks;

#ifdef EXTENTS_STATS
        /* ext4 extents stats */
        unsigned long s_ext_min;
        unsigned long s_ext_max;
        unsigned long s_depth_max;
        spinlock_t s_ext_stats_lock;
        unsigned long s_ext_blocks;
        unsigned long s_ext_extents;
#endif

        /* for buddy allocator */
        struct ext4_group_info ***s_group_info;
        struct inode *s_buddy_cache;
        spinlock_t s_md_lock;
        unsigned short *s_mb_offsets;
        unsigned int *s_mb_maxs;
        unsigned int s_group_info_size;
        unsigned int s_mb_free_pending;

        /* tunables */
        unsigned long s_stripe;
        unsigned int s_mb_stream_request;
        unsigned int s_mb_max_to_scan;
        unsigned int s_mb_min_to_scan;
        unsigned int s_mb_stats;
        unsigned int s_mb_order2_reqs;
        unsigned int s_mb_group_prealloc;
        unsigned int s_max_dir_size_kb;
        /* where last allocation was done - for stream allocation */
        unsigned long s_mb_last_group;

unsigned long s_mb_last_start;

        /* stats for buddy allocator */
        atomic_t s_bal_reqs;    /* number of reqs with len > 1 */
        atomic_t s_bal_success; /* we found long enough chunks */
        atomic_t s_bal_allocated;       /* in blocks */
        atomic_t s_bal_ex_scanned;      /* total extents scanned */
        atomic_t s_bal_goals;   /* goal hits */
        atomic_t s_bal_breaks;  /* too long searches */
        atomic_t s_bal_2orders; /* 2^order hits */
        spinlock_t s_bal_lock;
        unsigned long s_mb_buddies_generated;
        unsigned long long s_mb_generation_time;
        atomic_t s_mb_lost_chunks;
        atomic_t s_mb_preallocated;
        atomic_t s_mb_discarded;
        atomic_t s_lock_busy;

        /* locality groups */
        struct ext4_locality_group *s_locality_groups;

        /* for write statistics */
        unsigned long s_sectors_written_start;
        uint64_t s_kbytes_written;

        /* the size of zero-out chunk */
        unsigned int s_extent_max_zeroout_kb;

        unsigned int s_log_groups_per_flex;
        struct flex_groups *s_flex_groups;
        ext4_group_t s_flex_groups_allocated;

        /* workqueue for reserved extent conversions (buffered io) */
        struct workqueue_struct *rsv_conversion_wq;

        /* timer for periodic error stats printing */
        struct timer_list s_err_report;

        /* Lazy inode table initialization info */
        struct ext4_li_request *s_li_request;
        /* Wait multiplier for lazy initialization thread */
        unsigned int s_li_wait_mult;

        /* Kernel thread for multiple mount protection */
        struct task_struct *s_mmp_tsk;

        /* record the last minlen when FITRIM is called. */
        atomic_t s_last_trim_minblks;

        /* Reference to checksum algorithm driver via cryptoapi */
        struct crypto_shash *s_chksum_driver;

        /* Precomputed FS UUID checksum for seeding other checksums */
        uint32_t s_csum_seed;

        /* Reclaim extents from extent status tree */
        struct shrinker s_es_shrinker;
        struct list_head s_es_list;     /* List of inodes with reclaimable extents */
        long s_es_nr_inode;
        struct ext4_es_stats s_es_stats;
        struct mb_cache *s_mb_cache;
        spinlock_t ____cacheline_aligned_in_smp;

        /* Ratelimit ext4 messages. */
        struct ratelimit_state s_err_ratelimit_state;
        struct ratelimit_state s_warning_ratelimit_state;
        struct ratelimit_state s_msg_ratelimit_state;

        /* Barrier between changing inodes' journal flags and writepages ops. */
        struct percpu_rw_semaphore s_journal_flag_rwsem;
};

/*
 *  * Structure of a blocks group descriptor
 *   */
struct ext4_group_desc
{
        uint32_t  bg_block_bitmap_lo;     /* Blocks bitmap block */
        uint32_t  bg_inode_bitmap_lo;     /* Inodes bitmap block */
        uint32_t  bg_inode_table_lo;      /* Inodes table block */
        uint16_t  bg_free_blocks_count_lo;/* Free blocks count */
        uint16_t  bg_free_inodes_count_lo;/* Free inodes count */
        uint16_t  bg_used_dirs_count_lo;  /* Directories count */
        uint16_t  bg_flags;               /* EXT4_BG_flags (INODE_UNINIT, etc) */
        uint32_t  bg_exclude_bitmap_lo;   /* Exclude bitmap for snapshots */
        uint16_t  bg_block_bitmap_csum_lo;/* crc32c(s_uuid+grp_num+bbitmap) LE */
        uint16_t  bg_inode_bitmap_csum_lo;/* crc32c(s_uuid+grp_num+ibitmap) LE */
        uint16_t  bg_itable_unused_lo;    /* Unused inodes count */
        uint16_t  bg_checksum;            /* crc16(sb_uuid+group+desc) */
        uint32_t  bg_block_bitmap_hi;     /* Blocks bitmap block MSB */
        uint32_t  bg_inode_bitmap_hi;     /* Inodes bitmap block MSB */
        uint32_t  bg_inode_table_hi;      /* Inodes table block MSB */
        uint16_t  bg_free_blocks_count_hi;/* Free blocks count MSB */
        uint16_t  bg_free_inodes_count_hi;/* Free inodes count MSB */
        uint16_t  bg_used_dirs_count_hi;  /* Directories count MSB */
        uint16_t  bg_itable_unused_hi;    /* Unused inodes count MSB */
        uint32_t  bg_exclude_bitmap_hi;   /* Exclude bitmap block MSB */
        uint16_t  bg_block_bitmap_csum_hi;/* crc32c(s_uuid+grp_num+bbitmap) BE */
        uint16_t  bg_inode_bitmap_csum_hi;/* crc32c(s_uuid+grp_num+ibitmap) BE */
        uint32_t   bg_reserved;
};

/* data type for filesystem-wide blocks number */


typedef unsigned long long ext4_fsblk_t;


/* Return the number of clusters used for file system metadata; this
 * represents the overhead needed by the file system.
 */
static unsigned ext4_num_overhead_clusters(struct super_block *sb,
					   ext4_group_t block_group,
					   struct ext4_group_desc *gdp)
{
	unsigned num_clusters;
	int block_cluster = -1, inode_cluster = -1, itbl_cluster = -1, i, c;
	ext4_fsblk_t start = ext4_group_first_block_no(sb, block_group);
	ext4_fsblk_t itbl_blk;
	struct ext4_sb_info *sbi = EXT4_SB(sb);

	/* This is the number of clusters used by the superblock,
	 * block group descriptors, and reserved block group
	 * descriptor blocks */
	num_clusters = ext4_num_base_meta_clusters(sb, block_group);

	/*
	 * For the allocation bitmaps and inode table, we first need
	 * to check to see if the block is in the block group.  If it
	 * is, then check to see if the cluster is already accounted
	 * for in the clusters used for the base metadata cluster, or
	 * if we can increment the base metadata cluster to include
	 * that block.  Otherwise, we will have to track the cluster
	 * used for the allocation bitmap or inode table explicitly.
	 * Normally all of these blocks are contiguous, so the special
	 * case handling shouldn't be necessary except for *very*
	 * unusual file system layouts.
	 */
	if (ext4_block_in_group(sb, ext4_block_bitmap(sb, gdp), block_group)) {
		block_cluster = EXT4_B2C(sbi,
					 ext4_block_bitmap(sb, gdp) - start);
		if (block_cluster < num_clusters)
			block_cluster = -1;
		else if (block_cluster == num_clusters) {
			num_clusters++;
			block_cluster = -1;
		}
	}

	if (ext4_block_in_group(sb, ext4_inode_bitmap(sb, gdp), block_group)) {
		inode_cluster = EXT4_B2C(sbi,
					 ext4_inode_bitmap(sb, gdp) - start);
		if (inode_cluster < num_clusters)
			inode_cluster = -1;
		else if (inode_cluster == num_clusters) {
			num_clusters++;
			inode_cluster = -1;
		}
	}

	itbl_blk = ext4_inode_table(sb, gdp);
	for (i = 0; i < sbi->s_itb_per_group; i++) {
		if (ext4_block_in_group(sb, itbl_blk + i, block_group)) {
			c = EXT4_B2C(sbi, itbl_blk + i - start);
			if ((c < num_clusters) || (c == inode_cluster) ||
			    (c == block_cluster) || (c == itbl_cluster))
				continue;
			if (c == num_clusters) {
				num_clusters++;
				continue;
			}
			num_clusters++;
			itbl_cluster = c;
		}
	}

	if (block_cluster != -1)
		num_clusters++;
	if (inode_cluster != -1)
		num_clusters++;

	return num_clusters;
}

