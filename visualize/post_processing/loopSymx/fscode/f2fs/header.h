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

include<stddef.h>
#include<stdint.h>
#include<stdbool.h>

#define __le32 uint32_t
#define __le16 uint16_t

#define ERR_PTR(x) x

#define EINVAL 10
#define ENOMEM 11

#define READ 0

#define GFP_NOFS 12

#define u32 uint32_t

typedef u32 block_t;

typedef unsigned long sector_t;


enum {  
        META_CP,
        META_NAT,
        META_SIT,
        META_SSA,
        META_POR,
};

#define NAT_ENTRY_PER_BLOCK (PAGE_SIZE / sizeof(struct f2fs_nat_entry))
#define NAT_ENTRY_BITMAP_SIZE   ((NAT_ENTRY_PER_BLOCK + 7) / 8)

#define WB_DATA_TYPE(p) (__is_cp_guaranteed(p) ? F2FS_WB_CP_DATA : F2FS_WB_DATA)
enum count_type {
        F2FS_DIRTY_DENTS,
        F2FS_DIRTY_DATA,
        F2FS_DIRTY_NODES,
        F2FS_DIRTY_META,
        F2FS_INMEM_PAGES,
        F2FS_DIRTY_IMETA,
        F2FS_WB_CP_DATA,
        F2FS_WB_DATA,
        NR_COUNT_TYPE,
};

#define PAGE_TYPE_OF_BIO(type)  ((type) > META ? META : (type))
enum page_type {
        DATA,
        NODE,
        META,
        NR_PAGE_TYPE,
        META_FLUSH,
        INMEM,          /* the below types are used by tracepoints only. */
        INMEM_DROP,
        INMEM_INVALIDATE,
        INMEM_REVOKE,
        IPU,
        OPU,
};

struct list_head {
    struct list_head *next, *prev;
};


#define PAGE_TYPE_OF_BIO(type)  ((type) > META ? META : (type))
struct f2fs_io_info {
        struct f2fs_sb_info *sbi;       /* f2fs_sb_info pointer */
        enum page_type type;    /* contains DATA/NODE/META/META_FLUSH */
        int op;                 /* contains REQ_OP_ */
        int op_flags;           /* req_flag_bits */
        block_t new_blkaddr;    /* new block address to be written */
        block_t old_blkaddr;    /* old block address before Cow */
        struct page *page;      /* page to be written */
        struct page *encrypted_page;    /* encrypted page */
        bool submitted;         /* indicate IO submission */
        bool need_lock;         /* indicate we need to lock cp_rwsem */
};

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


#define __s32 uint32_t

struct rw_semaphore {
        __s32                   count;
        raw_spinlock_t          wait_lock;
        struct list_head        wait_list;
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map dep_map;
#endif
};




struct f2fs_bio_info {
        struct f2fs_sb_info *sbi;       /* f2fs superblock */
        struct bio *bio;                /* bios to merge */
        sector_t last_block_in_bio;     /* last block number */
        struct f2fs_io_info fio;        /* store buffered io info. */
        struct rw_semaphore io_rwsem;   /* blocking op for bio */
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

typedef enum {
        GFP_KERNEL,
        GFP_ATOMIC,
        __GFP_HIGHMEM,
        __GFP_HIGH
} gfp_t;

struct __wait_queue_head {
        spinlock_t              lock;
        struct list_head        task_list;
};
typedef struct __wait_queue_head wait_queue_head_t;

enum {  
        CP_TIME,
        REQ_TIME,
        MAX_TIME,
};

typedef void * (mempool_alloc_t)(gfp_t gfp_mask, void *pool_data);
typedef void (mempool_free_t)(void *element, void *pool_data);

typedef struct mempool_s {
        spinlock_t lock;
        int min_nr;             /* nr of elements at *elements */
        int curr_nr;            /* Current nr of elements at *elements */
        void **elements;

        void *pool_data;
        mempool_alloc_t *alloc;
        mempool_free_t *free;
        wait_queue_head_t wait;
} mempool_t;





typedef struct {
        long long counter;
} atomic64_t;
 
typedef atomic64_t atomic_long_t;

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

struct callback_head {
        struct callback_head *next;
        void (*func)(struct callback_head *head);
} __attribute__((aligned(sizeof(void *))));
#define rcu_head callback_head

enum inode_type {
        DIR_INODE,                      /* for dirty dir inode */
        FILE_INODE,                     /* for dirty regular/symlink inode */
        DIRTY_META,                     /* for all dirtied inode metadata */
        NR_INODE_TYPE,
};

# define __rcu          __attribute__((noderef, address_space(4)))

#define RADIX_TREE_MAX_TAGS 3

#define CONFIG_BASE_SMALL 0

#define BITS_PER_LONG 32

#ifndef RADIX_TREE_MAP_SHIFT
#define RADIX_TREE_MAP_SHIFT    (CONFIG_BASE_SMALL ? 4 : 6)
#endif

#define RADIX_TREE_MAP_SIZE     (1UL << RADIX_TREE_MAP_SHIFT)
#define RADIX_TREE_MAP_MASK     (RADIX_TREE_MAP_SIZE-1)

#define RADIX_TREE_TAG_LONGS    \
        ((RADIX_TREE_MAP_SIZE + BITS_PER_LONG - 1) / BITS_PER_LONG)

#define RADIX_TREE_INDEX_BITS  (8 /* CHAR_BIT */ * sizeof(unsigned long))
#define RADIX_TREE_MAX_PATH (DIV_ROUND_UP(RADIX_TREE_INDEX_BITS, \
                                          RADIX_TREE_MAP_SHIFT))


struct radix_tree_node {
        unsigned char   shift;          /* Bits remaining in each slot */
        unsigned char   offset;         /* Slot offset in parent */
        unsigned char   count;          /* Total entry count */
        unsigned char   exceptional;    /* Exceptional entry count */
        struct radix_tree_node *parent;         /* Used when ascending tree */
        struct radix_tree_root *root;           /* The tree we belong to */
        union { 
                struct list_head private_list;  /* For tree user */
                struct rcu_head rcu_head;       /* Used when freeing node */
        };
        void __rcu      *slots[RADIX_TREE_MAP_SIZE];
        unsigned long   tags[RADIX_TREE_MAX_TAGS][RADIX_TREE_TAG_LONGS];
};



struct radix_tree_root {
        gfp_t                   gfp_mask;
        struct radix_tree_node  __rcu *rnode;
};

/* for inner inode cache management */
struct inode_management {
        struct radix_tree_root ino_root;        /* ino entry array */
        spinlock_t ino_lock;                    /* for ino entry lock */
        struct list_head ino_list;              /* inode list head */
        unsigned long ino_num;                  /* number of entries */
};



/* for the list of ino */ 
enum {  
        ORPHAN_INO,             /* for orphan ino list */ 
        APPEND_INO,             /* for append ino list */ 
        UPDATE_INO,             /* for update ino list */ 
        MAX_INO_ENTRY,          /* max. list */ 
};

struct f2fs_mount_info {
        unsigned int    opt;
};

struct hd_struct {
        sector_t start_sect;
        /*
 *          * nr_sects is protected by sequence counter. One might extend a
 *                   * partition while IO is happening to it and update of nr_sects
 *                            * can be non-atomic on 32bit machines with 64bit sector_t.
 *                                     */
        sector_t nr_sects;
        seqcount_t nr_sects_seq;
        sector_t alignment_offset;
        unsigned int discard_alignment;
        struct device __dev;
        struct kobject *holder_dir;
        int policy, partno;
        struct partition_meta_info *info;
#ifdef CONFIG_FAIL_MAKE_REQUEST
        int make_it_fail;
#endif  
        unsigned long stamp;
        atomic_t in_flight[2];
#ifdef  CONFIG_SMP
        struct disk_stats __percpu *dkstats;
#else   
        struct disk_stats dkstats;
#endif  
        struct percpu_ref ref;
        struct rcu_head rcu_head;
};


struct f2fs_sb_info {
        struct super_block *sb;                 /* pointer to VFS super block */
        struct proc_dir_entry *s_proc;          /* proc entry */
        struct f2fs_super_block *raw_super;     /* raw super block pointer */
        int valid_super_block;                  /* valid super block no */
        unsigned long s_flag;                           /* flags for sbi */

//#ifdef CONFIG_BLK_DEV_ZONED
        unsigned int blocks_per_blkz;           /* F2FS blocks per zone */
        unsigned int log_blocks_per_blkz;       /* log2 F2FS blocks per zone */
//#endif  

        /* for node-related operations */
        struct f2fs_nm_info *nm_info;           /* node manager */
        struct inode *node_inode;               /* cache node blocks */

        /* for segment-related operations */
        struct f2fs_sm_info *sm_info;           /* segment manager */

        /* for bio operations */
        struct f2fs_bio_info read_io;                   /* for read bios */
        struct f2fs_bio_info write_io[NR_PAGE_TYPE];    /* for write bios */
        struct mutex wio_mutex[NODE + 1];       /* bio ordering for NODE/DATA */
        int write_io_size_bits;                 /* Write IO size bits */
        mempool_t *write_io_dummy;              /* Dummy pages */

        /* for checkpoint */
        struct f2fs_checkpoint *ckpt;           /* raw checkpoint pointer */
        int cur_cp_pack;                        /* remain current cp pack */
        spinlock_t cp_lock;                     /* for flag in ckpt */
        struct inode *meta_inode;               /* cache meta blocks */
        struct mutex cp_mutex;                  /* checkpoint procedure lock */
        struct rw_semaphore cp_rwsem;           /* blocking FS operations */
        struct rw_semaphore node_write;         /* locking node writes */
        struct rw_semaphore node_change;        /* locking node change */
        wait_queue_head_t cp_wait;
        unsigned long last_time[MAX_TIME];      /* to store time in jiffies */
        long interval_time[MAX_TIME];           /* to store thresholds */

        struct inode_management im[MAX_INO_ENTRY];      /* manage inode cache */

        /* for orphan inode, use 0'th array */
        unsigned int max_orphans;               /* max orphan inodes */

        /* for inode management */
        struct list_head inode_list[NR_INODE_TYPE];     /* dirty inode list */
        spinlock_t inode_lock[NR_INODE_TYPE];   /* for dirty inode list lock */

        /* for extent tree cache */
        struct radix_tree_root extent_tree_root;/* cache extent cache entries */
        struct mutex extent_tree_lock;  /* locking extent radix tree */
        struct list_head extent_list;           /* lru list for shrinker */
        spinlock_t extent_lock;                 /* locking extent lru list */
        atomic_t total_ext_tree;                /* extent tree count */
        struct list_head zombie_list;           /* extent zombie tree list */
        atomic_t total_zombie_tree;             /* extent zombie tree count */
        atomic_t total_ext_node;                /* extent info count */

        /* basic filesystem units */
        unsigned int log_sectors_per_block;     /* log2 sectors per block */
        unsigned int log_blocksize;             /* log2 block size */
        unsigned int blocksize;                 /* block size */
        unsigned int root_ino_num;              /* root inode number*/
        unsigned int node_ino_num;              /* node inode number*/
        unsigned int meta_ino_num;              /* meta inode number*/
        unsigned int log_blocks_per_seg;        /* log2 blocks per segment */
        unsigned int blocks_per_seg;            /* blocks per segment */
        unsigned int segs_per_sec;              /* segments per section */
        unsigned int secs_per_zone;             /* sections per zone */
        unsigned int total_sections;            /* total section count */
        unsigned int total_node_count;          /* total node block count */
        unsigned int total_valid_node_count;    /* valid node block count */
        loff_t max_file_blocks;                 /* max block index of file */
        int active_logs;                        /* # of active logs */
        int dir_level;                          /* directory level */

	    block_t user_block_count;               /* # of user blocks */
        block_t total_valid_block_count;        /* # of valid blocks */
        block_t discard_blks;                   /* discard command candidats */
        block_t last_valid_block_count;         /* for recovery */
        u32 s_next_generation;                  /* for NFS support */

        /* # of pages, see count_type */
        atomic_t nr_pages[NR_COUNT_TYPE];
        /* # of allocated blocks */
        struct percpu_counter alloc_valid_block_count;

        /* writeback control */
        atomic_t wb_sync_req;                   /* count # of WB_SYNC threads */

        /* valid inode count */
        struct percpu_counter total_valid_inode_count;

        struct f2fs_mount_info mount_opt;       /* mount options */

        /* for cleaning operations */
        struct mutex gc_mutex;                  /* mutex for GC */
        struct f2fs_gc_kthread  *gc_thread;     /* GC thread */
        unsigned int cur_victim_sec;            /* current victim section num */

        /* threshold for converting bg victims for fg */
        u64 fggc_threshold;

        /* maximum # of trials to find a victim segment for SSR and GC */
        unsigned int max_victim_search;

        /*
 *          * for stat information.
 *                   * one is for the LFS mode, and the other is for the SSR mode.
 *                            */

	#ifdef CONFIG_F2FS_STAT_FS
        struct f2fs_stat_info *stat_info;       /* FS status information */
        unsigned int segment_count[2];          /* # of allocated segments */
        unsigned int block_count[2];            /* # of allocated blocks */
        atomic_t inplace_count;         /* # of inplace update */
        atomic64_t total_hit_ext;               /* # of lookup extent cache */
        atomic64_t read_hit_rbtree;             /* # of hit rbtree extent node */
        atomic64_t read_hit_largest;            /* # of hit largest extent node */
        atomic64_t read_hit_cached;             /* # of hit cached extent node */
        atomic_t inline_xattr;                  /* # of inline_xattr inodes */
        atomic_t inline_inode;                  /* # of inline_data inodes */
        atomic_t inline_dir;                    /* # of inline_dentry inodes */
        atomic_t aw_cnt;                        /* # of atomic writes */
        atomic_t vw_cnt;                        /* # of volatile writes */
        atomic_t max_aw_cnt;                    /* max # of atomic writes */
        atomic_t max_vw_cnt;                    /* max # of volatile writes */
        int bg_gc;                              /* background gc calls */
        unsigned int ndirty_inode[NR_INODE_TYPE];       /* # of dirty inodes */
#endif
        spinlock_t stat_lock;                   /* lock for stat operations */

        /* For sysfs suppport */
        struct kobject s_kobj;
        struct completion s_kobj_unregister;

        /* For shrinker support */
        struct list_head s_list;
        int s_ndevs;                            /* number of devices */
        struct f2fs_dev_info *devs;             /* for device list */
        struct mutex umount_mutex;
        unsigned int shrinker_run_no;

        /* For write statistics */
        u64 sectors_written_start;
        u64 kbytes_written;

        /* Reference to checksum algorithm driver via cryptoapi */
        struct crypto_shash *s_chksum_driver;

	        /* For fault injection */
#ifdef CONFIG_F2FS_FAULT_INJECTION
        struct f2fs_fault_info fault_info;
#endif
};

static inline struct f2fs_nm_info *NM_I(struct f2fs_sb_info *sbi)
{
        return (struct f2fs_nm_info *)(sbi->nm_info);
}

enum req_opf {
        /* read sectors from the device */
        REQ_OP_READ             = 0,
        /* write sectors to the device */
        REQ_OP_WRITE            = 1,
        /* flush the volatile write cache */
        REQ_OP_FLUSH            = 2,
        /* discard sectors */
        REQ_OP_DISCARD          = 3,
        /* get zone information */
        REQ_OP_ZONE_REPORT      = 4,
        /* securely erase sectors */
        REQ_OP_SECURE_ERASE     = 5,
        /* seset a zone write pointer */
        REQ_OP_ZONE_RESET       = 6,
        /* write the same sector many times */
        REQ_OP_WRITE_SAME       = 7,
        /* write the zero filled sector many times */
        REQ_OP_WRITE_ZEROES     = 9,

        /* SCSI passthrough using struct scsi_request */
        REQ_OP_SCSI_IN          = 32,
        REQ_OP_SCSI_OUT         = 33,
        /* Driver private requests */
        REQ_OP_DRV_IN           = 34,
        REQ_OP_DRV_OUT          = 35,

        REQ_OP_LAST,
};

#define REQ_META (1ULL << __REQ_META)


#define REQ_OP_BITS     8
#define REQ_OP_MASK     ((1 << REQ_OP_BITS) - 1)
#define REQ_FLAG_BITS   24



enum req_flag_bits {
        __REQ_FAILFAST_DEV =    /* no driver retries of device errors */
                REQ_OP_BITS,
        __REQ_FAILFAST_TRANSPORT, /* no driver retries of transport errors */
        __REQ_FAILFAST_DRIVER,  /* no driver retries of driver errors */
        __REQ_SYNC,             /* request is sync (sync write or read) */
        __REQ_META,             /* metadata io request */
        __REQ_PRIO,             /* boost priority in cfq */
        __REQ_NOMERGE,          /* don't touch this for merging */
        __REQ_IDLE,             /* anticipate more IO after this one */
        __REQ_INTEGRITY,        /* I/O includes block integrity payload */
        __REQ_FUA,              /* forced unit access */
        __REQ_PREFLUSH,         /* request for cache flush */
        __REQ_RAHEAD,           /* read ahead, can fail anytime */
        __REQ_BACKGROUND,       /* background IO */

        /* command specific flags for REQ_OP_WRITE_ZEROES: */
        __REQ_NOUNMAP,          /* do not free blocks when zeroing */

        __REQ_NR_BITS,          /* stops here */
};


#define REQ_FAILFAST_DEV        (1ULL << __REQ_FAILFAST_DEV)
#define REQ_FAILFAST_TRANSPORT  (1ULL << __REQ_FAILFAST_TRANSPORT)
#define REQ_FAILFAST_DRIVER     (1ULL << __REQ_FAILFAST_DRIVER)
#define REQ_SYNC                (1ULL << __REQ_SYNC)
#define REQ_META                (1ULL << __REQ_META)
#define REQ_PRIO                (1ULL << __REQ_PRIO)
#define REQ_NOMERGE             (1ULL << __REQ_NOMERGE)
#define REQ_IDLE                (1ULL << __REQ_IDLE)
#define REQ_INTEGRITY           (1ULL << __REQ_INTEGRITY)
#define REQ_FUA                 (1ULL << __REQ_FUA)
#define REQ_PREFLUSH            (1ULL << __REQ_PREFLUSH)
#define REQ_RAHEAD              (1ULL << __REQ_RAHEAD)
#define REQ_BACKGROUND          (1ULL << __REQ_BACKGROUND)

#define REQ_NOUNMAP             (1ULL << __REQ_NOUNMAP)

#define REQ_FAILFAST_MASK \
        (REQ_FAILFAST_DEV | REQ_FAILFAST_TRANSPORT | REQ_FAILFAST_DRIVER)

#define REQ_NOMERGE_FLAGS \
        (REQ_NOMERGE | REQ_PREFLUSH | REQ_FUA)

#define bio_op(bio) \
        ((bio)->bi_opf & REQ_OP_MASK)
#define req_op(req) \
        ((req)->cmd_flags & REQ_OP_MASK)

/* checkpoint.c*/



struct blk_plug {
        struct list_head list; /* requests */
        struct list_head mq_list; /* blk-mq requests */
        struct list_head cb_list; /* md requires an unplug callback */
};




/* acl.c*/

struct cds_wfcq_node {
        struct cds_wfcq_node *next;
};

struct rcu_head {
        struct cds_wfcq_node next;
        void (*func)(struct rcu_head *head);
};

typedef struct {
        int counter;
} atomic_t;

struct rb_node {
        unsigned long  __rb_parent_color;
        struct rb_node *rb_right;
        struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
    /* The alignment might seem pointless, but allegedly CRIS needs it */

struct rb_root {
        struct rb_node *rb_node;
};

#define uid_t unsigned
#define gid_t unsigned

typedef struct {
        uid_t val;
} kuid_t;

typedef struct { 
        gid_t val;
} kgid_t;

#define ACL_USER_OBJ            (0x01)
#define ACL_USER                (0x02)
#define ACL_GROUP_OBJ           (0x04)
#define ACL_GROUP               (0x08)

#define ACL_MASK                (0x10)
#define ACL_OTHER               (0x20)

/* permissions in the e_perm field */
#define ACL_READ                (0x04)
#define ACL_WRITE               (0x02)
#define ACL_EXECUTE             (0x01)

#define GLOBAL_ROOT_UID KUIDT_INIT(0)
#define GLOBAL_ROOT_GID KGIDT_INIT(0)

#define INVALID_UID KUIDT_INIT(-1)
#define INVALID_GID KGIDT_INIT(-1)

#define KUIDT_INIT(value) (kuid_t){ value }
#define KGIDT_INIT(value) (kgid_t){ value }

#define USERNS_SETGROUPS_ALLOWED 1UL

#define USERNS_INIT_FLAGS USERNS_SETGROUPS_ALLOWED
#define UID_GID_MAP_MAX_EXTENTS 5



struct proc_ns_operations {
        const char *name;
        const char *real_ns_name;
        int type;
        struct ns_common *(*get)(struct task_struct *task);
        void (*put)(struct ns_common *ns);
        int (*install)(struct nsproxy *nsproxy, struct ns_common *ns);
        struct user_namespace *(*owner)(struct ns_common *ns);
        struct ns_common *(*get_parent)(struct ns_common *ns);
};

typedef void (*work_func_t)(struct work_struct *work);

struct work_struct {
        atomic_long_t data;
        struct list_head entry;
        work_func_t func;
#ifdef CONFIG_LOCKDEP
        struct lockdep_map lockdep_map;
#endif
};

#define XXX_LOCK_USAGE_STATES           (1+3*4)

#define NR_LOCKDEP_CACHING_CLASSES 2

#define ATOMIC_INIT(i) { (i) }

enum ucount_type {
        UCOUNT_USER_NAMESPACES,
        UCOUNT_PID_NAMESPACES,
        UCOUNT_UTS_NAMESPACES,
        UCOUNT_IPC_NAMESPACES,
        UCOUNT_NET_NAMESPACES,
        UCOUNT_MNT_NAMESPACES,
        UCOUNT_CGROUP_NAMESPACES,
#ifdef CONFIG_INOTIFY_USER
        UCOUNT_INOTIFY_INSTANCES,
        UCOUNT_INOTIFY_WATCHES,
#endif  
        UCOUNT_COUNTS,
};


struct stack_trace {
        unsigned int nr_entries, max_entries;
        unsigned long *entries;
        int skip;       /* input argument: How many entries to skip */
};

struct hlist_node {
        struct hlist_node *next, **pprev;
};



/*
 *  * The lock-class itself:
 *   */
struct lock_class {
        /*
 *          * class-hash:
 *                   */
        struct hlist_node               hash_entry;

        /*
 *          * global list of all lock-classes:
 *                   */
        struct list_head                lock_entry;

        struct lockdep_subclass_key     *key;
        unsigned int                    subclass;
        unsigned int                    dep_gen_id;

        /*
 *          * IRQ/softirq usage tracking bits:
 *                   */
        unsigned long                   usage_mask;
        struct stack_trace              usage_traces[XXX_LOCK_USAGE_STATES];

        /*
 *          * These fields represent a directed graph of lock dependencies,
 *                   * to every node we attach a list of "forward" and a list of
 *                            * "backward" graph nodes.
 *                                     */
        struct list_head                locks_after, locks_before;

        /*
 *          * Generation counter, when doing certain classes of graph walking,
 *                   * to ensure that we check one node only once:
 *                            */
        unsigned int                    version;

        /*
 *          * Statistics counter:
 *                   */
        unsigned long                   ops;
        const char                      *name;
        int                             name_version;

#ifdef CONFIG_LOCK_STAT
        unsigned long                   contention_point[LOCKSTAT_POINTS];
        unsigned long                   contending_point[LOCKSTAT_POINTS];
#endif
};




struct lock_class_key { };

struct lockdep_map {
        struct lock_class_key           *key;
        struct lock_class               *class_cache[NR_LOCKDEP_CACHING_CLASSES];
        const char                      *name;
#ifdef CONFIG_LOCK_STAT
        int                             cpu;
        unsigned long                   ip;
#endif
};





struct ns_common {
        atomic_long_t stashed;
        const struct proc_ns_operations *ops;
        unsigned int inum;
};





struct uid_gid_map {    /* 64 bytes -- 1 cache line */
        u32 nr_extents;
        struct uid_gid_extent {
                u32 first;
                u32 lower_first;
                u32 count;
        } extent[UID_GID_MAP_MAX_EXTENTS];
};


struct user_namespace {
        struct uid_gid_map      uid_map;
        struct uid_gid_map      gid_map;
        struct uid_gid_map      projid_map;
        atomic_t                count;
        struct user_namespace   *parent;
        int                     level;
        kuid_t                  owner;
        kgid_t                  group;
        struct ns_common        ns;
        unsigned long           flags;

        /* Register of per-UID persistent keyrings for this namespace */
#ifdef CONFIG_PERSISTENT_KEYRINGS
        struct key              *persistent_keyring_register;
        struct rw_semaphore     persistent_keyring_register_sem;
#endif
        struct work_struct      work;
#ifdef CONFIG_SYSCTL
        struct ctl_table_set    set;
        struct ctl_table_header *sysctls;
#endif
        struct ucounts          *ucounts;
        int ucount_max[UCOUNT_COUNTS];
};


enum {  
        PROC_ROOT_INO           = 1,
        PROC_IPC_INIT_INO       = 0xEFFFFFFFU,
        PROC_UTS_INIT_INO       = 0xEFFFFFFEU,
        PROC_USER_INIT_INO      = 0xEFFFFFFDU,
        PROC_PID_INIT_INO       = 0xEFFFFFFCU,
        PROC_CGROUP_INIT_INO    = 0xEFFFFFFBU,
};


struct user_namespace init_user_ns = {
        .uid_map = {
                .nr_extents = 1,
                .extent[0] = {
                        .first = 0,
                        .lower_first = 0,
                        .count = 4294967295U,
                },
        },
        .gid_map = {
                .nr_extents = 1,
                .extent[0] = {
                        .first = 0,
                        .lower_first = 0,
                        .count = 4294967295U,
                },
        },
        .projid_map = {
                .nr_extents = 1,
                .extent[0] = {
                        .first = 0,
                        .lower_first = 0,
                        .count = 4294967295U,
                },
        },
        .count = ATOMIC_INIT(3),
        .owner = GLOBAL_ROOT_UID,
        .group = GLOBAL_ROOT_GID,
        .ns.inum = PROC_USER_INIT_INO,
#ifdef CONFIG_USER_NS
        .ns.ops = &userns_operations,
#endif
        .flags = USERNS_INIT_FLAGS,
#ifdef CONFIG_PERSISTENT_KEYRINGS
        .persistent_keyring_register_sem =
        __RWSEM_INITIALIZER(init_user_ns.persistent_keyring_register_sem),
#endif
};



struct posix_acl_entry {
        short                   e_tag;
        unsigned short          e_perm;
        union { 
                kuid_t          e_uid;
                kgid_t          e_gid;
        };
};

struct posix_acl {
        atomic_t                a_refcount;
        struct rcu_head         a_rcu;
        unsigned int            a_count;
        struct posix_acl_entry  a_entries[0];
};


