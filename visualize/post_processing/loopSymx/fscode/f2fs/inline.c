#include<stdio.h>
#include<stdint.h>
#include<stdbool.h>
#include<string.h>


typedef unsigned char           u8;
typedef unsigned short          u16;
typedef unsigned int            u32;
typedef unsigned int            __u32;
typedef unsigned long long      u64;
typedef signed char             s8;
typedef short                   s16;
typedef int                     s32;
typedef long long               s64;

#ifdef __CHECKER__
#define __bitwise__ __attribute__((bitwise))
#else
#define __bitwise__
#endif
#define __bitwise __bitwise__

typedef uint32_t __le32;
typedef uint16_t __le16;
typedef uint64_t __le64;
typedef uint8_t __u8;
typedef uint16_t __u16;

#define MAX_VOLUME_NAME         512
#define MAX_DEVICES             8

#define MAX_PATH_LEN            64

#define S_SHIFT 12

#define uid_t unsigned
#define gid_t unsigned

typedef long long dev_t;
typedef unsigned long blkcnt_t;


typedef struct {
        uid_t val;
} kuid_t;

typedef struct { 
        gid_t val;
} kgid_t;

typedef unsigned short umode_t;

/*
 *  * For superblock
 *   */
struct f2fs_device {
        __u8 path[MAX_PATH_LEN];
        __le32 total_segments;
} __packed;



typedef __u16 __bitwise __le16;
//typedef __u16 __bitwise __be16;
//typedef __u32 __bitwise __le32;
//typedef __u32 __bitwise __be32;
//typedef __u64 __bitwise __le64;
//typedef __u64 __bitwise __be64;
//
//typedef __u16 __bitwise __sum16;
//typedef __u32 __bitwise __wsum;
//
//typedef __le16 le16;
//typedef __le32 le32;
//typedef __le64 le64;
//typedef __u16 __bitwise sle16;
//typedef __u32 __bitwise sle32;
//typedef __u64 __bitwise sle64;
//
//#
//


typedef u64 sector_t;

typedef long long __kernel_loff_t;
typedef __kernel_loff_t loff_t;

#define u32 uint32_t
typedef u32 block_t;



#define __s32 uint32_t


struct list_head {
    struct list_head *next, *prev;
};

typedef struct {
        volatile unsigned int lock;
} arch_spinlock_t;

struct hlist_node {
        struct hlist_node *next, **pprev;
};

struct hlist_head {
        struct hlist_node *first;
};


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




struct rw_semaphore {
        __s32                   count;
        raw_spinlock_t          wait_lock;
        struct list_head        wait_list;
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map dep_map;
#endif
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


typedef enum {
        GFP_KERNEL,
        GFP_ATOMIC,
        __GFP_HIGHMEM,
        __GFP_HIGH
} gfp_t;

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

struct f2fs_bio_info {
        struct f2fs_sb_info *sbi;       /* f2fs superblock */
        struct bio *bio;                /* bios to merge */
        sector_t last_block_in_bio;     /* last block number */
        struct f2fs_io_info fio;        /* store buffered io info. */
        struct rw_semaphore io_rwsem;   /* blocking op for bio */
};

enum {  
        CP_TIME,
        REQ_TIME,
        MAX_TIME,
};

/* for the list of ino */ 
enum {  
        ORPHAN_INO,             /* for orphan ino list */ 
        APPEND_INO,             /* for append ino list */ 
        UPDATE_INO,             /* for update ino list */ 
        MAX_INO_ENTRY,          /* max. list */ 
};

enum inode_type {
        DIR_INODE,                      /* for dirty dir inode */
        FILE_INODE,                     /* for dirty regular/symlink inode */
        DIRTY_META,                     /* for all dirtied inode metadata */
        NR_INODE_TYPE,
};

struct callback_head {
        struct callback_head *next;
        void (*func)(struct callback_head *head);
} __attribute__((aligned(sizeof(void *))));
#define rcu_head callback_head

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

typedef struct {
        int counter;
} atomic_t;

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

struct percpu_counter { 
        raw_spinlock_t lock; 
        s64 count; 
#ifdef CONFIG_HOTPLUG_CPU 
        struct list_head list;  /* All percpu_counters are on a list */ 
#endif  
//        s32 __percpu *counters; 
        s32 *counters; 
}; 

enum kobject_action {
        KOBJ_ADD,
        KOBJ_REMOVE,
        KOBJ_CHANGE,
        KOBJ_MOVE,
        KOBJ_ONLINE,
        KOBJ_OFFLINE,
        KOBJ_MAX
};

typedef struct refcount_struct {
        atomic_t refs;
} refcount_t;

struct kref {
        refcount_t refcount;
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
        unsigned int done;
        wait_queue_head_t wait;
};

struct f2fs_mount_info {
        unsigned int    opt;
};

#define F2FS_MAX_EXTENSION              64
#define VERSION_LEN     256

struct f2fs_super_block {
        __le32 magic;                   /* Magic Number */
        __le16 major_ver;               /* Major Version */
        __le16 minor_ver;               /* Minor Version */
        __le32 log_sectorsize;          /* log2 sector size in bytes */
        __le32 log_sectors_per_block;   /* log2 # of sectors per block */
        __le32 log_blocksize;           /* log2 block size in bytes */
        __le32 log_blocks_per_seg;      /* log2 # of blocks per segment */
        __le32 segs_per_sec;            /* # of segments per section */
        __le32 secs_per_zone;           /* # of sections per zone */
        __le32 checksum_offset;         /* checksum offset inside super block */
        __le64 block_count;             /* total # of user blocks */
        __le32 section_count;           /* total # of sections */
        __le32 segment_count;           /* total # of segments */
        __le32 segment_count_ckpt;      /* # of segments for checkpoint */
        __le32 segment_count_sit;       /* # of segments for SIT */
        __le32 segment_count_nat;       /* # of segments for NAT */
        __le32 segment_count_ssa;       /* # of segments for SSA */
        __le32 segment_count_main;      /* # of segments for main area */
        __le32 segment0_blkaddr;        /* start block address of segment 0 */
        __le32 cp_blkaddr;              /* start block address of checkpoint */
        __le32 sit_blkaddr;             /* start block address of SIT */
        __le32 nat_blkaddr;             /* start block address of NAT */
        __le32 ssa_blkaddr;             /* start block address of SSA */
        __le32 main_blkaddr;            /* start block address of main area */
        __le32 root_ino;                /* root inode number */
        __le32 node_ino;                /* node inode number */
        __le32 meta_ino;                /* meta inode number */
        __u8 uuid[16];                  /* 128-bit uuid for volume */
        __le16 volume_name[MAX_VOLUME_NAME];    /* volume name */
        __le32 extension_count;         /* # of extensions below */
        __u8 extension_list[F2FS_MAX_EXTENSION][8];     /* extension array */
        __le32 cp_payload;
        __u8 version[VERSION_LEN];      /* the kernel version */
        __u8 init_version[VERSION_LEN]; /* the initial kernel version */
        __le32 feature;                 /* defined features */
        __u8 encryption_level;          /* versioning level for encryption */
        __u8 encrypt_pw_salt[16];       /* Salt used for string2key algorithm */
        struct f2fs_device devs[MAX_DEVICES];   /* device list */
        __u8 reserved[327];             /* valid reserved region */
} ; //__packed;




struct f2fs_sb_info {
        struct super_block *sb;                 /* pointer to VFS super block */
        struct proc_dir_entry *s_proc;          /* proc entry */
        struct f2fs_super_block *raw_super;     /* raw super block pointer */
        int valid_super_block;                  /* valid super block no */
        unsigned long s_flag;                           /* flags for sbi */

#ifdef CONFIG_BLK_DEV_ZONED
        unsigned int blocks_per_blkz;           /* F2FS blocks per zone */
        unsigned int log_blocks_per_blkz;       /* log2 F2FS blocks per zone */
#endif  

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

/** added for inline **/

typedef long long __kernel_long_t;

typedef __kernel_long_t __kernel_time_t;

struct timespec {
        __kernel_time_t tv_sec;                 /* seconds */
        long            tv_nsec;                /* nanoseconds */
};

struct rb_node {
        unsigned long  __rb_parent_color;
        struct rb_node *rb_right;
        struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
    /* The alignment might seem pointless, but allegedly CRIS needs it */

struct rb_root {
        struct rb_node *rb_node;
};

#define pgoff_t unsigned long

struct address_space {
        struct inode            *host;          /* owner: inode, block_device */
        struct radix_tree_root  page_tree;      /* radix tree of all pages */
        spinlock_t              tree_lock;      /* and lock protecting it */
        atomic_t                i_mmap_writable;/* count VM_SHARED mappings */
        struct rb_root          i_mmap;         /* tree of private and shared mappings */
        struct rw_semaphore     i_mmap_rwsem;   /* protect tree, count, list */
        /* Protected by tree_lock together with the radix tree */
        unsigned long           nrpages;        /* number of total pages */
        /* number of shadow or DAX exceptional entries */
        unsigned long           nrexceptional;
        pgoff_t                 writeback_index;/* writeback starts here */
        const struct address_space_operations *a_ops;   /* methods */
        unsigned long           flags;          /* error bits */
        spinlock_t              private_lock;   /* for use by the address_space */
        gfp_t                   gfp_mask;       /* implicit gfp mask for allocations */
        struct list_head        private_list;   /* ditto */
        void                    *private_data;  /* ditto */
} __attribute__((aligned(sizeof(long))));

/*
 *  * Keep mostly read-only and often accessed (especially for
 *   * the RCU path lookup and 'stat' data) fields at the beginning
 *    * of the 'struct inode'
 *     */
struct inode {
        umode_t                 i_mode;
        unsigned short          i_opflags;
        kuid_t                  i_uid;
        kgid_t                  i_gid;
        unsigned int            i_flags;

#ifdef CONFIG_FS_POSIX_ACL
        struct posix_acl        *i_acl;
        struct posix_acl        *i_default_acl;
#endif

        const struct inode_operations   *i_op;
        struct super_block      *i_sb;
        struct address_space    *i_mapping;

#ifdef CONFIG_SECURITY
        void                    *i_security;
#endif

        /* Stat data, not accessed from path walking */
        unsigned long           i_ino;
        /*
 *          * Filesystems may only read i_nlink directly.  They shall use the
 *                   * following functions for modification:
 *                            *
 *                                     *    (set|clear|inc|drop)_nlink
 *                                              *    inode_(inc|dec)_link_count
 *                                                       */
        union {
                const unsigned int i_nlink;
                unsigned int __i_nlink;
        };
        dev_t                   i_rdev;
        loff_t                  i_size;
        struct timespec         i_atime;
        struct timespec         i_mtime;
        struct timespec         i_ctime;
        spinlock_t              i_lock; /* i_blocks, i_bytes, maybe i_size */
        unsigned short          i_bytes;
        unsigned int            i_blkbits;
        blkcnt_t                i_blocks;

#ifdef __NEED_I_SIZE_ORDERED
        seqcount_t              i_size_seqcount;
#endif

        /* Misc */
        unsigned long           i_state;
        struct rw_semaphore     i_rwsem;

        unsigned long           dirtied_when;   /* jiffies of first dirtying */
        unsigned long           dirtied_time_when;

        struct hlist_node       i_hash;
        struct list_head        i_io_list;      /* backing dev IO list */
#ifdef CONFIG_CGROUP_WRITEBACK
        struct bdi_writeback    *i_wb;          /* the associated cgroup wb */

        /* foreign inode detection, see wbc_detach_inode() */
        int                     i_wb_frn_winner;
        u16                     i_wb_frn_avg_time;
        u16                     i_wb_frn_history;
#endif
        struct list_head        i_lru;          /* inode LRU list */
        struct list_head        i_sb_list;
        struct list_head        i_wb_list;      /* backing dev writeback list */
        union {
                struct hlist_head       i_dentry;
                struct rcu_head         i_rcu;
        };
        u64                     i_version;
        atomic_t                i_count;
        atomic_t                i_dio_count;
        atomic_t                i_writecount;
#ifdef CONFIG_IMA
        atomic_t                i_readcount; /* struct files open RO */
#endif
        const struct file_operations    *i_fop; /* former ->i_op->default_file_ops */
        struct file_lock_context        *i_flctx;
        struct address_space    i_data;
        struct list_head        i_devices;
        union {
                struct pipe_inode_info  *i_pipe;
                struct block_device     *i_bdev;
                struct cdev             *i_cdev;
                char                    *i_link;
                unsigned                i_dir_seq;
        };

        __u32                   i_generation;

#ifdef CONFIG_FSNOTIFY
        __u32                   i_fsnotify_mask; /* all events this inode cares about */
        struct fsnotify_mark_connector __rcu    *i_fsnotify_marks;
#endif

//#if IS_ENABLED(CONFIG_FS_ENCRYPTION)
        struct fscrypt_info     *i_crypt_info;
//#endif

        void                    *i_private; /* fs or device private pointer */
};



/* One directory entry slot covers 8bytes-long file name */
#define F2FS_SLOT_LEN           8
#define F2FS_SLOT_LEN_BITS      3

typedef u32 nid_t;

u64 ino;

#ifdef __LITTLE_ENDIAN
 #define HASH_LEN_DECLARE u32 hash; u32 len
 #define bytemask_from_count(cnt)       (~(~0ul << (cnt)*8))
#else
 #define HASH_LEN_DECLARE u32 len; u32 hash
 #define bytemask_from_count(cnt)       (~(~0ul >> (cnt)*8))
#endif

struct qstr {
        union { 
                struct {
                        HASH_LEN_DECLARE;
                };
                u64 hash_len;
        };
        const unsigned char *name;
};

/* One directory entry slot representing F2FS_SLOT_LEN-sized file name */
struct f2fs_dir_entry {
        __le32 hash_code;       /* hash code of file name */
        __le32 ino;             /* inode number */
        __le16 name_len;        /* lengh of file name */
        __u8 file_type;         /* file type */
};

/*
 *  * For INODE and NODE manager
 *   */
/* for directory operations */
struct f2fs_dentry_ptr {
        struct inode *inode;
        const void *bitmap;
        struct f2fs_dir_entry *dentry;
        __u8 (*filename)[F2FS_SLOT_LEN];
        int max;
};

#define BITS_PER_BYTE 8
#define SIZE_OF_DIR_ENTRY       11      /* by byte */



#define DEF_ADDRS_PER_INODE     923     /* Address Pointers in an Inode */
#define F2FS_INLINE_XATTR_ADDRS 50      /* 200 bytes for inline xattrs */


#define MAX_INLINE_DATA         (sizeof(__le32) * (DEF_ADDRS_PER_INODE - \
                                                F2FS_INLINE_XATTR_ADDRS - 1))

/* for inline dir */
#define NR_INLINE_DENTRY        (MAX_INLINE_DATA * BITS_PER_BYTE / \
                                ((SIZE_OF_DIR_ENTRY + F2FS_SLOT_LEN) * \
                                BITS_PER_BYTE + 1))
#define INLINE_DENTRY_BITMAP_SIZE       ((NR_INLINE_DENTRY + \
                                        BITS_PER_BYTE - 1) / BITS_PER_BYTE)
#define INLINE_RESERVED_SIZE    (MAX_INLINE_DATA - \
                                ((SIZE_OF_DIR_ENTRY + F2FS_SLOT_LEN) * \
                                NR_INLINE_DENTRY + INLINE_DENTRY_BITMAP_SIZE))

/* inline directory entry structure */
struct f2fs_inline_dentry {
        __u8 dentry_bitmap[INLINE_DENTRY_BITMAP_SIZE];
        __u8 reserved[INLINE_RESERVED_SIZE];
        struct f2fs_dir_entry dentry[NR_INLINE_DENTRY];
        __u8 filename[NR_INLINE_DENTRY][F2FS_SLOT_LEN];
};

static int is_multimedia_file(const unsigned char *s, const char *sub)
{
	size_t slen = strlen(s);
	size_t sublen = strlen(sub);
	int i;

	/*
	 * filename format of multimedia file should be defined as:
	 * "filename + '.' + extension + (optional: '.' + temp extension)".
	 */
	if (slen < sublen + 2)
		return 0;

	for (i = 1; i < slen - sublen; i++) {
		if (s[i] != '.')
			continue;
		if (!strncasecmp(s + i + 1, sub, sublen))
			return 1;
	}

	return 0;
}

static inline void set_cold_files(struct f2fs_sb_info *sbi, struct inode *inode,
		const unsigned char *name)
{
	int i;
	__u8 (*extlist)[8] = sbi->raw_super->extension_list;

	int count = le32_to_cpu(sbi->raw_super->extension_count);
	for (i = 0; i < count; i++) {
		if (is_multimedia_file(name, extlist[i])) {
			file_set_cold(inode);
			break;
		}
	}
}



static int f2fs_add_inline_entries(struct inode *dir,
			struct f2fs_inline_dentry *inline_dentry)
{
	struct f2fs_dentry_ptr d;
	unsigned long bit_pos = 0;
	int err = 0;

	make_dentry_ptr_inline(NULL, &d, inline_dentry);

	while (bit_pos < d.max) {
		struct f2fs_dir_entry *de;
		struct qstr new_name;
		nid_t ino;
		umode_t fake_mode;

		if (!test_bit_le(bit_pos, d.bitmap)) {
			bit_pos++;
			continue;
		}

		de = &d.dentry[bit_pos];

		if (unlikely(!de->name_len)) {
			bit_pos++;
			continue;
		}

		new_name.name = d.filename[bit_pos];
		new_name.len = le16_to_cpu(de->name_len);

		ino = le32_to_cpu(de->ino);
		fake_mode = get_de_type(de) << S_SHIFT;

		err = f2fs_add_regular_entry(dir, &new_name, NULL, NULL,
							ino, fake_mode);
		if (err)
			goto punch_dentry_pages;

		bit_pos += GET_DENTRY_SLOTS(le16_to_cpu(de->name_len));
	}
	return 0;
punch_dentry_pages:
	truncate_inode_pages(&dir->i_data, 0);
	truncate_blocks(dir, 0, false);
	remove_dirty_inode(dir);
	return err;
}

void f2fs_delete_inline_entry(struct f2fs_dir_entry *dentry, struct page *page,
					struct inode *dir, struct inode *inode)
{
	struct f2fs_inline_dentry *inline_dentry;
	int slots = GET_DENTRY_SLOTS(le16_to_cpu(dentry->name_len));
	unsigned int bit_pos;
	int i;

	lock_page(page);
	f2fs_wait_on_page_writeback(page, NODE, true);

	inline_dentry = inline_data_addr(page);
	bit_pos = dentry - inline_dentry->dentry;
	for (i = 0; i < slots; i++)
		__clear_bit_le(bit_pos + i,
				&inline_dentry->dentry_bitmap);

	set_page_dirty(page);
	f2fs_put_page(page, 1);

	dir->i_ctime.tv_sec = dir->i_mtime.tv_sec = (unsigned long )current_time(dir);
	f2fs_mark_inode_dirty_sync(dir, false);

	if (inode)
		f2fs_drop_nlink(dir, inode);
}
