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

# define __rcu  __attribute__((noderef, address_space(4)))

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

/****** hash.c ***************/

#define F2FS_HASH_COL_BIT       ((0x1ULL) << 63)

#define DELTA 0x9E3779B9
typedef __le32  f2fs_hash_t;

struct fscrypt_str {
        unsigned char *name;
        u32 len;
};

struct fscrypt_name {
        const struct qstr *usr_fname;
        struct fscrypt_str disk_name;
        u32 hash;
        u32 minor_hash;
        struct fscrypt_str crypto_buf;
};

/************** shrinker.c ********************/

#ifndef VM_EVENT_ITEM_H_INCLUDED
#define VM_EVENT_ITEM_H_INCLUDED
#endif

#ifdef CONFIG_ZONE_DMA
#define DMA_ZONE(xx) xx##_DMA,
#else
#define DMA_ZONE(xx)
#endif

#ifdef CONFIG_ZONE_DMA32
#define DMA32_ZONE(xx) xx##_DMA32,
#else
#define DMA32_ZONE(xx)
#endif

#ifdef CONFIG_HIGHMEM
#define HIGHMEM_ZONE(xx) xx##_HIGH,
#else
#define HIGHMEM_ZONE(xx)
#endif

#define FOR_ALL_ZONES(xx) DMA_ZONE(xx) DMA32_ZONE(xx) xx##_NORMAL, HIGHMEM_ZONE(xx) xx##_MOVABLE



enum node_stat_item {
        NR_LRU_BASE,
        NR_INACTIVE_ANON = NR_LRU_BASE, /* must match order of LRU_[IN]ACTIVE */
        NR_ACTIVE_ANON,         /*  "     "     "   "       "         */
        NR_INACTIVE_FILE,       /*  "     "     "   "       "         */
        NR_ACTIVE_FILE,         /*  "     "     "   "       "         */
        NR_UNEVICTABLE,         /*  "     "     "   "       "         */
        NR_ISOLATED_ANON,       /* Temporary isolated pages from anon lru */
        NR_ISOLATED_FILE,       /* Temporary isolated pages from file lru */
        WORKINGSET_REFAULT,
        WORKINGSET_ACTIVATE,
        WORKINGSET_NODERECLAIM,
        NR_ANON_MAPPED, /* Mapped anonymous pages */
        NR_FILE_MAPPED, /* pagecache pages mapped into pagetables.
                           only modified from process context */
        NR_FILE_PAGES,
        NR_FILE_DIRTY,
        NR_WRITEBACK,
        NR_WRITEBACK_TEMP,      /* Writeback using temporary buffers */
        NR_SHMEM,               /* shmem pages (included tmpfs/GEM pages) */
        NR_SHMEM_THPS,
        NR_SHMEM_PMDMAPPED,
        NR_ANON_THPS,
        NR_UNSTABLE_NFS,        /* NFS unstable pages */
        NR_VMSCAN_WRITE,
        NR_VMSCAN_IMMEDIATE,    /* Prioritise for reclaim when writeback ends */
        NR_DIRTIED,             /* page dirtyings since bootup */
        NR_WRITTEN,             /* page writings since bootup */
        NR_VM_NODE_STAT_ITEMS
};




struct mem_cgroup;
struct page;
struct mm_struct;
struct kmem_cache;

/* Cgroup-specific page state, on top of universal node page state */
enum memcg_stat_item {
        MEMCG_CACHE = NR_VM_NODE_STAT_ITEMS,
        MEMCG_RSS,
        MEMCG_RSS_HUGE,
        MEMCG_SWAP,
        MEMCG_SOCK,
        /* XXX: why are these zone and not node counters? */
        MEMCG_KERNEL_STACK_KB,
        MEMCG_SLAB_RECLAIMABLE,
        MEMCG_SLAB_UNRECLAIMABLE,
        MEMCG_NR_STAT,
};




enum vm_event_item { PGPGIN, PGPGOUT, PSWPIN, PSWPOUT,
                FOR_ALL_ZONES(PGALLOC),
                FOR_ALL_ZONES(ALLOCSTALL),
                FOR_ALL_ZONES(PGSCAN_SKIP),
                PGFREE, PGACTIVATE, PGDEACTIVATE, PGLAZYFREE,
                PGFAULT, PGMAJFAULT,
                PGLAZYFREED,
                PGREFILL,
                PGSTEAL_KSWAPD,
                PGSTEAL_DIRECT,
                PGSCAN_KSWAPD,
                PGSCAN_DIRECT,
                PGSCAN_DIRECT_THROTTLE,
#ifdef CONFIG_NUMA
                PGSCAN_ZONE_RECLAIM_FAILED,
#endif
                PGINODESTEAL, SLABS_SCANNED, KSWAPD_INODESTEAL,
                KSWAPD_LOW_WMARK_HIT_QUICKLY, KSWAPD_HIGH_WMARK_HIT_QUICKLY,
                PAGEOUTRUN, PGROTATED,
                DROP_PAGECACHE, DROP_SLAB,
#ifdef CONFIG_NUMA_BALANCING
                NUMA_PTE_UPDATES,
                NUMA_HUGE_PTE_UPDATES,
                NUMA_HINT_FAULTS,
                NUMA_HINT_FAULTS_LOCAL,
                NUMA_PAGE_MIGRATE,
#endif
#ifdef CONFIG_MIGRATION
                PGMIGRATE_SUCCESS, PGMIGRATE_FAIL,
#endif
#ifdef CONFIG_COMPACTION
                COMPACTMIGRATE_SCANNED, COMPACTFREE_SCANNED,
                COMPACTISOLATED,
                COMPACTSTALL, COMPACTFAIL, COMPACTSUCCESS,
                KCOMPACTD_WAKE,
                KCOMPACTD_MIGRATE_SCANNED, KCOMPACTD_FREE_SCANNED,
#endif
#ifdef CONFIG_HUGETLB_PAGE
                HTLB_BUDDY_PGALLOC, HTLB_BUDDY_PGALLOC_FAIL,
#endif
                UNEVICTABLE_PGCULLED,   /* culled to noreclaim list */
                UNEVICTABLE_PGSCANNED,  /* scanned for reclaimability */
                UNEVICTABLE_PGRESCUED,  /* rescued from noreclaim list */
                UNEVICTABLE_PGMLOCKED,
                UNEVICTABLE_PGMUNLOCKED,
                UNEVICTABLE_PGCLEARED,  /* on COW, page truncate */
                UNEVICTABLE_PGSTRANDED, /* unable to isolate on unlock */
#ifdef CONFIG_TRANSPARENT_HUGEPAGE
                THP_FAULT_ALLOC,
                THP_FAULT_FALLBACK,
                THP_COLLAPSE_ALLOC,
                THP_COLLAPSE_ALLOC_FAILED,
                THP_FILE_ALLOC,
                THP_FILE_MAPPED,
                THP_SPLIT_PAGE,
                THP_SPLIT_PAGE_FAILED,
                THP_DEFERRED_SPLIT_PAGE,
                THP_SPLIT_PMD,
#ifdef CONFIG_HAVE_ARCH_TRANSPARENT_HUGEPAGE_PUD
                THP_SPLIT_PUD,
#endif
                THP_ZERO_PAGE_ALLOC,
                THP_ZERO_PAGE_ALLOC_FAILED,
#endif
#ifdef CONFIG_MEMORY_BALLOON
                BALLOON_INFLATE,
                BALLOON_DEFLATE,
#ifdef CONFIG_BALLOON_COMPACTION
                BALLOON_MIGRATE,
#endif
#endif
#ifdef CONFIG_DEBUG_TLBFLUSH
#ifdef CONFIG_SMP
                NR_TLB_REMOTE_FLUSH,    /* cpu tried to flush others' tlbs */
                NR_TLB_REMOTE_FLUSH_RECEIVED,/* cpu received ipi for flush */
#endif /* CONFIG_SMP */
                NR_TLB_LOCAL_FLUSH_ALL,
                NR_TLB_LOCAL_FLUSH_ONE,
#endif /* CONFIG_DEBUG_TLBFLUSH */
#ifdef CONFIG_DEBUG_VM_VMACACHE
                VMACACHE_FIND_CALLS,
                VMACACHE_FIND_HITS,
                VMACACHE_FULL_FLUSHES,
#endif
                NR_VM_EVENT_ITEMS
};



/* Cgroup-specific events, on top of universal VM events */
enum memcg_event_item {
        MEMCG_LOW = NR_VM_EVENT_ITEMS,
        MEMCG_HIGH,
        MEMCG_MAX,
        MEMCG_OOM,
        MEMCG_NR_EVENTS,
};

enum zone_type {
#ifdef CONFIG_ZONE_DMA
        /*
 *          * ZONE_DMA is used when there are devices that are not able
 *                   * to do DMA to all of addressable memory (ZONE_NORMAL). Then we
 *                            * carve out the portion of memory that is needed for these devices.
 *                                     * The range is arch specific.
 *                                              *
 *
        *
        *          * Some examples
        *                   *
        *                            * Architecture         Limit
        *                                     * ---------------------------
        *                                              * parisc, ia64, sparc  <4G
        *                                                       * s390                 <2G
        *                                                                * arm                  Various
        *                                                                         * alpha                Unlimited or 0-16MB.
        *                                                                                  *
        *                                                                                           * i386, x86_64 and multiple other arches
        *                                                                                                    *                      <16M.
        *                                                                                                             */
        ZONE_DMA,
#endif
#ifdef CONFIG_ZONE_DMA32
        /*
 *          * x86_64 needs two ZONE_DMAs because it supports devices that are
 *                   * only able to do DMA to the lower 16M but also 32 bit devices that
 *                            * can only do DMA areas below 4G.
 *                                     */
        ZONE_DMA32,
#endif  
        /*
 *          * Normal addressable memory is in ZONE_NORMAL. DMA operations can be
 *                   * performed on pages in ZONE_NORMAL if the DMA devices support
 *                            * transfers to all addressable memory.
 *                                     */
        ZONE_NORMAL,
#ifdef CONFIG_HIGHMEM
        /*
 *          * A memory area that is only addressable by the kernel through
 *                   * mapping portions into its own address space. This is for example
 *                            * used by i386 to allow the kernel to address the memory beyond
 *                                     * 900MB. The kernel will set up special mappings (page
 *                                              * table entries on i386) for each page that the kernel needs to
 *                                                       * access.
 *                                                                */
        ZONE_HIGHMEM,
#endif
        ZONE_MOVABLE,
#ifdef CONFIG_ZONE_DEVICE
        ZONE_DEVICE,
#endif
        __MAX_NR_ZONES
};

enum {  
        ZONELIST_FALLBACK,      /* zonelist with fallback */
#ifdef CONFIG_NUMA
        /*
 *          * The NUMA zonelists are doubled because we need zonelists that
 *                   * restrict the allocations to a single node for __GFP_THISNODE.
 *                            */
        ZONELIST_NOFALLBACK,    /* zonelist without fallback (__GFP_THISNODE) */
#endif  
        MAX_ZONELISTS
};

enum migratetype {
        MIGRATE_UNMOVABLE,
        MIGRATE_MOVABLE,
        MIGRATE_RECLAIMABLE,
        MIGRATE_PCPTYPES,       /* the number of types on the pcp lists */
        MIGRATE_HIGHATOMIC = MIGRATE_PCPTYPES,
#ifdef CONFIG_CMA
        /*
 *          * MIGRATE_CMA migration type is designed to mimic the way
 *                   * ZONE_MOVABLE works.  Only movable pages can be allocated
 *                            * from MIGRATE_CMA pageblocks and page allocator never
 *                                     * implicitly change migration type of MIGRATE_CMA pageblock.
 *                                              *
 *                                                       * The way to use it is to change migratetype of a range of
 *                                                                * pageblocks to MIGRATE_CMA which can be done by
 *                                                                         * __free_pageblock_cma() function.  What is important though
 *                                                                                  * is that a range of pageblocks must be aligned to
 *                                                                                           * MAX_ORDER_NR_PAGES should biggest page be bigger then
 *                                                                                                    * a single pageblock.
 *                                                                                                             */
        MIGRATE_CMA,
#endif
#ifdef CONFIG_MEMORY_ISOLATION
        MIGRATE_ISOLATE,        /* can't allocate from here */
#endif  
        MIGRATE_TYPES
};




struct per_cpu_pages {
        int count;              /* number of pages in the list */
        int high;               /* high watermark, emptying needed */
        int batch;              /* chunk size for buddy add/remove */

        /* Lists of pages, one per migrate type stored on the pcp-lists */
        struct list_head lists[MIGRATE_PCPTYPES];
};

struct per_cpu_pageset {
        struct per_cpu_pages pcp;
#ifdef CONFIG_NUMA
        s8 expire;
#endif
#ifdef CONFIG_SMP
        s8 stat_threshold;
        s8 vm_stat_diff[NR_VM_ZONE_STAT_ITEMS];
#endif
};

#define MAX_ORDER 11

enum zone_watermarks {
        WMARK_MIN,
        WMARK_LOW,
        WMARK_HIGH,
        NR_WMARK
};

struct zone_padding {
        char x[0];
} ____cacheline_internodealigned_in_smp;


#define ZONE_PADDING(name) struct zone_padding name;

#define MAX_NR_ZONES 4 /* __MAX_NR_ZONES */

enum zone_stat_item {
        /* First 128 byte cacheline (assuming 64 bit words) */
        NR_FREE_PAGES,
        NR_ZONE_LRU_BASE, /* Used only for compaction and reclaim retry */
        NR_ZONE_INACTIVE_ANON = NR_ZONE_LRU_BASE,
        NR_ZONE_ACTIVE_ANON,
        NR_ZONE_INACTIVE_FILE,
        NR_ZONE_ACTIVE_FILE,
        NR_ZONE_UNEVICTABLE,
        NR_ZONE_WRITE_PENDING,  /* Count of dirty, writeback and unstable pages */
        NR_MLOCK,               /* mlock()ed pages found and moved off LRU */
        NR_SLAB_RECLAIMABLE,
        NR_SLAB_UNRECLAIMABLE,
        NR_PAGETABLE,           /* used for pagetables */
        NR_KERNEL_STACK_KB,     /* measured in KiB */
        /* Second 128 byte cacheline */
        NR_BOUNCE,
//#if IS_ENABLED(CONFIG_ZSMALLOC)
        NR_ZSPAGES,             /* allocated in zsmalloc */
//#endif
#ifdef CONFIG_NUMA
        NUMA_HIT,               /* allocated in intended node */
        NUMA_MISS,              /* allocated in non intended node */
        NUMA_FOREIGN,           /* was intended here, hit elsewhere */
        NUMA_INTERLEAVE_HIT,    /* interleaver preferred this zone */
        NUMA_LOCAL,             /* allocation from local node */
        NUMA_OTHER,             /* allocation from other node */
#endif  
        NR_FREE_CMA_PAGES,
        NR_VM_ZONE_STAT_ITEMS };

struct free_area {
        struct list_head        free_list[MIGRATE_TYPES];
        unsigned long           nr_free;
};

struct zone {
        /* Read-mostly fields */

        /* zone watermarks, access with *_wmark_pages(zone) macros */
        unsigned long watermark[NR_WMARK];

        unsigned long nr_reserved_highatomic;

        /*
 *          * We don't know if the memory that we're going to allocate will be
 *                   * freeable or/and it will be released eventually, so to avoid totally
 *                            * wasting several GB of ram we must reserve some of the lower zone
 *                                     * memory (otherwise we risk to run OOM on the lower zones despite
 *                                              * there being tons of freeable ram on the higher zones).  This array is
 *                                                       * recalculated at runtime if the sysctl_lowmem_reserve_ratio sysctl
 *                                                                * changes.
 *                                                                         */
        long lowmem_reserve[MAX_NR_ZONES];

#ifdef CONFIG_NUMA
        int node;
#endif  
        struct pglist_data      *zone_pgdat;
        struct per_cpu_pageset *pageset;

#ifndef CONFIG_SPARSEMEM
        /*
 *          * Flags for a pageblock_nr_pages block. See pageblock-flags.h.
 *                   * In SPARSEMEM, this map is stored in struct mem_section
 *                            */
        unsigned long           *pageblock_flags;
#endif /* CONFIG_SPARSEMEM */
        /* zone_start_pfn == zone_start_paddr >> PAGE_SHIFT */
        unsigned long           zone_start_pfn;
        unsigned long           managed_pages;
        unsigned long           spanned_pages;
        unsigned long           present_pages;

        const char              *name;

#ifdef CONFIG_MEMORY_ISOLATION
        /*
 *          * Number of isolated pageblock. It is used to solve incorrect
 *                   * freepage counting problem due to racy retrieving migratetype
 *                            * of pageblock. Protected by zone->lock.
 *                                     */
        unsigned long           nr_isolate_pageblock;
#endif

#ifdef CONFIG_MEMORY_HOTPLUG
        /* see spanned/present_pages for more description */
        seqlock_t               span_seqlock;
#endif

        int initialized;

        /* Write-intensive fields used from the page allocator */
        ZONE_PADDING(_pad1_)

        /* free areas of different sizes */
        struct free_area        free_area[MAX_ORDER];

        /* zone flags, see below */
        unsigned long           flags;

        /* Primarily protects free_area */
        spinlock_t              lock;

        /* Write-intensive fields used by compaction and vmstats. */
        ZONE_PADDING(_pad2_)

        /*
 *          * When free pages are below this point, additional steps are taken
 *                   * when reading the number of free pages to avoid per-cpu counter
 *                            * drift allowing watermarks to be breached
 *                                     */
        unsigned long percpu_drift_mark;

#if defined CONFIG_COMPACTION || defined CONFIG_CMA
        /* pfn where compaction free scanner should start */
        unsigned long           compact_cached_free_pfn;
        /* pfn where async and sync compaction migration scanner should start */
        unsigned long           compact_cached_migrate_pfn[2];
#endif

#ifdef CONFIG_COMPACTION
        /*
 *          * On compaction failure, 1<<compact_defer_shift compactions
 *                   * are skipped before trying again. The number attempted since
 *                            * last failure is tracked with compact_considered.
 *                                     */
        unsigned int            compact_considered;
        unsigned int            compact_defer_shift;
        int                     compact_order_failed;
#endif

#if defined CONFIG_COMPACTION || defined CONFIG_CMA
        /* Set to true when the PG_migrate_skip bits should be cleared */
        bool                    compact_blockskip_flush;
#endif

        bool                    contiguous;

        ZONE_PADDING(_pad3_)
        /* Zone statistics */
        atomic_long_t           vm_stat[NR_VM_ZONE_STAT_ITEMS];
} ;

#define NODES_SHIFT 0


#define MAX_NUMNODES    (1 << NODES_SHIFT)
#define MAX_NR_NODES    64


#define MAX_ZONES_PER_ZONELIST (MAX_NUMNODES * MAX_NR_ZONES)

struct zone_reclaim_stat {
       unsigned long           recent_rotated[2];
        unsigned long           recent_scanned[2];
};

#define LRU_BASE 0
#define LRU_ACTIVE 1
#define LRU_FILE 2


enum lru_list {
        LRU_INACTIVE_ANON = LRU_BASE,
        LRU_ACTIVE_ANON = LRU_BASE + LRU_ACTIVE,
        LRU_INACTIVE_FILE = LRU_BASE + LRU_FILE,
        LRU_ACTIVE_FILE = LRU_BASE + LRU_FILE + LRU_ACTIVE,
        LRU_UNEVICTABLE,
        NR_LRU_LISTS
};

struct lruvec {
        struct list_head                lists[NR_LRU_LISTS];
        struct zone_reclaim_stat        reclaim_stat;
        /* Evictions & activations on the inactive file list */
        atomic_long_t                   inactive_age;
        /* Refaults at the time of last reclaim cycle */
        unsigned long                   refaults;
#ifdef CONFIG_MEMCG
        struct pglist_data *pgdat;
#endif
};



struct zoneref {
        struct zone *zone;      /* Pointer to actual zone */
        int zone_idx;           /* zone_idx(zoneref->zone) */
};



struct zonelist {
        struct zoneref _zonerefs[MAX_ZONES_PER_ZONELIST + 1];
};

struct per_cpu_nodestat {
        s8 stat_threshold;
        s8 vm_node_stat_diff[NR_VM_NODE_STAT_ITEMS];
};

struct bootmem_data;
typedef struct pglist_data {
        struct zone node_zones[MAX_NR_ZONES];
        struct zonelist node_zonelists[MAX_ZONELISTS];
        int nr_zones;
#ifdef CONFIG_FLAT_NODE_MEM_MAP /* means !SPARSEMEM */
        struct page *node_mem_map;
#ifdef CONFIG_PAGE_EXTENSION
        struct page_ext *node_page_ext;
#endif
#endif
#ifndef CONFIG_NO_BOOTMEM
        struct bootmem_data *bdata;
#endif
#ifdef CONFIG_MEMORY_HOTPLUG
        /*
 *          * Must be held any time you expect node_start_pfn, node_present_pages
 *                   * or node_spanned_pages stay constant.  Holding this will also
 *                            * guarantee that any pfn_valid() stays that way.
 *                                     *
 *                                              * pgdat_resize_lock() and pgdat_resize_unlock() are provided to
 *                                                       * manipulate node_size_lock without checking for CONFIG_MEMORY_HOTPLUG.
 *                                                                *
 *                                                                         * Nests above zone->lock and zone->span_seqlock
 *                                                                                  */
        spinlock_t node_size_lock;
#endif
        unsigned long node_start_pfn;
        unsigned long node_present_pages; /* total number of physical pages */
        unsigned long node_spanned_pages; /* total size of physical page
                                             range, including holes */
        int node_id;
        wait_queue_head_t kswapd_wait;
        wait_queue_head_t pfmemalloc_wait;
        struct task_struct *kswapd;     /* Protected by
                                           mem_hotplug_begin/end() */
        int kswapd_order;
        enum zone_type kswapd_classzone_idx;

        int kswapd_failures;            /* Number of 'reclaimed == 0' runs */

#ifdef CONFIG_COMPACTION
        int kcompactd_max_order;
        enum zone_type kcompactd_classzone_idx;
        wait_queue_head_t kcompactd_wait;
        struct task_struct *kcompactd;

#endif
#ifdef CONFIG_NUMA_BALANCING
        /* Lock serializing the migrate rate limiting window */
        spinlock_t numabalancing_migrate_lock;

        /* Rate limiting time interval */
        unsigned long numabalancing_migrate_next_window;

        /* Number of pages migrated during the rate limiting time interval */
        unsigned long numabalancing_migrate_nr_pages;
#endif
        /*
 *          * This is a per-node reserve of pages that are not available
 *                   * to userspace allocations.
 *                            */
        unsigned long           totalreserve_pages;

#ifdef CONFIG_NUMA
        /*
 *          * zone reclaim becomes active if more unmapped pages exist.
 *                   */
        unsigned long           min_unmapped_pages;
        unsigned long           min_slab_pages;
#endif /* CONFIG_NUMA */

        /* Write-intensive fields used by page reclaim */
        ZONE_PADDING(_pad1_)
        spinlock_t              lru_lock;

#ifdef CONFIG_DEFERRED_STRUCT_PAGE_INIT
        /*
 *          * If memory initialisation on large machines is deferred then this
 *                   * is the first PFN that needs to be initialised.
 *                            */
        unsigned long first_deferred_pfn;
        unsigned long static_init_size;
#endif /* CONFIG_DEFERRED_STRUCT_PAGE_INIT */

#ifdef CONFIG_TRANSPARENT_HUGEPAGE
        spinlock_t split_queue_lock;
        struct list_head split_queue;
        unsigned long split_queue_len;
#endif

        /* Fields commonly accessed by the page reclaim scanner */
        struct lruvec           lruvec;

     /*
 *          * The target ratio of ACTIVE_ANON to INACTIVE_ANON pages on
 *                   * this node's LRU.  Maintained by the pageout code.
 *                            */
        unsigned int inactive_ratio;

        unsigned long           flags;

        ZONE_PADDING(_pad2_)

        /* Per-node vmstats */
        struct per_cpu_nodestat  *per_cpu_nodestats;
        atomic_long_t           vm_stat[NR_VM_NODE_STAT_ITEMS];
} pg_data_t;



struct mem_cgroup_reclaim_cookie {
        pg_data_t *pgdat;
        int priority;
        unsigned int generation;
};


#define MEM_CGROUP_ID_SHIFT     16
#define MEM_CGROUP_ID_MAX       USHRT_MAX

struct mem_cgroup_id {
        int id;
        atomic_t ref;
};


/*
 *  * Per memcg event counter is incremented at every pagein/pageout. With THP,
 *   * it will be incremated by the number of pages. This counter is used for
 *    * for trigger some periodic events. This is straightforward and better
 *     * than using jiffies etc. to handle periodic memcg event.
 *      */
enum mem_cgroup_events_target {
        MEM_CGROUP_TARGET_THRESH,
        MEM_CGROUP_TARGET_SOFTLIMIT,
        MEM_CGROUP_TARGET_NUMAINFO,
        MEM_CGROUP_NTARGETS,
};

struct mem_cgroup_stat_cpu {
        long count[MEMCG_NR_STAT];
        unsigned long events[MEMCG_NR_EVENTS];
        unsigned long nr_page_events;
        unsigned long targets[MEM_CGROUP_NTARGETS];
};

struct mem_cgroup_reclaim_iter {
        struct mem_cgroup *position;
        /* scan generation, increased every round-trip */
        unsigned int generation;
};

#define DEF_PRIORITY 12


/*
 *  * per-zone information in memory controller.
 *   */
struct mem_cgroup_per_node {
        struct lruvec           lruvec;
        unsigned long           lru_zone_size[MAX_NR_ZONES][NR_LRU_LISTS];

        struct mem_cgroup_reclaim_iter  iter[DEF_PRIORITY + 1];

        struct rb_node          tree_node;      /* RB tree node */
        unsigned long           usage_in_excess;/* Set to the value by which */
                                                /* the soft limit is exceeded*/
        bool                    on_tree;
        struct mem_cgroup       *memcg;         /* Back pointer, we cannot */
                                                /* use container_of        */
};

struct mem_cgroup_threshold {
        struct eventfd_ctx *eventfd;
        unsigned long threshold;
};

/* For threshold */
struct mem_cgroup_threshold_ary {
        /* An array index points to threshold just below or equal to usage. */
        int current_threshold;
        /* Size of entries[] */
        unsigned int size;
        /* Array of thresholds */
        struct mem_cgroup_threshold entries[0];
};

struct percpu_ref;
typedef void (percpu_ref_func_t)(struct percpu_ref *);

struct work_struct;
typedef void (*work_func_t)(struct work_struct *work);

struct page_counter {
        atomic_long_t count;
        unsigned long limit;
        struct page_counter *parent;

        /* legacy */
        unsigned long watermark;
        unsigned long failcnt;
};



struct work_struct {
        atomic_long_t data;
        struct list_head entry;
        work_func_t func;
#ifdef CONFIG_LOCKDEP
        struct lockdep_map lockdep_map;
#endif
};


struct percpu_ref {
        atomic_long_t           count;
        /*
 *          * The low bit of the pointer indicates whether the ref is in percpu
 *                   * mode; if set, then get/put will manipulate the atomic_t.
 *                            */
        unsigned long           percpu_count_ptr;
        percpu_ref_func_t       *release;
        percpu_ref_func_t       *confirm_switch;
        bool                    force_atomic:1;
        struct rcu_head         rcu;
};

struct mem_cgroup_thresholds {
        /* Primary thresholds array */
        struct mem_cgroup_threshold_ary *primary;
        /*
 *          * Spare threshold array.
 *                   * This is needed to make mem_cgroup_unregister_event() "never fail".
 *                            * It must be able to store at least primary->size - 1 entries.
 *                                     */
        struct mem_cgroup_threshold_ary *spare;
};

enum memcg_kmem_state {
        KMEM_NONE,
        KMEM_ALLOCATED,
        KMEM_ONLINE,
};

struct cgroup_subsys_state {
        /* PI: the cgroup that this css is attached to */
        struct cgroup *cgroup;

        /* PI: the cgroup subsystem that this css is attached to */
        struct cgroup_subsys *ss;

        /* reference count - access via css_[try]get() and css_put() */
        struct percpu_ref refcnt;

        /* siblings list anchored at the parent's ->children */
        struct list_head sibling;
        struct list_head children;

        /*
 *          * PI: Subsys-unique ID.  0 is unused and root is always 1.  The
 *                   * matching css can be looked up using css_from_id().
 *                            */
        int id;

        unsigned int flags;

        /*
 *          * Monotonically increasing unique serial number which defines a
 *                   * uniform order among all csses.  It's guaranteed that all
 *                            * ->children lists are in the ascending order of ->serial_nr and
 *                                     * used to allow interrupting and resuming iterations.
 *                                              */
        u64 serial_nr;

        /*
 *          * Incremented by online self and children.  Used to guarantee that
 *                   * parents are not offlined before their children.
 *                            */
        atomic_t online_cnt;

        /* percpu_ref killing and RCU release */
        struct rcu_head rcu_head;
        struct work_struct destroy_work;

        /*
 *          * PI: the parent css.  Placed here for cache proximity to following
 *                   * fields of the containing structure.
 *                            */
        struct cgroup_subsys_state *parent;
};

struct llist_head {
        struct llist_node *first;
};

struct llist_node {
        struct llist_node *next;
};

#define XXX_LOCK_USAGE_STATES           (1+3*4)
#define NR_LOCKDEP_CACHING_CLASSES 2


struct stack_trace {
        unsigned int nr_entries, max_entries;
        unsigned long *entries;
        int skip;       /* input argument: How many entries to skip */
};


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

#define NR_LOCKDEP_CACHING_CLASSES 2

struct lockdep_map {
        struct lock_class_key           *key;
        struct lock_class               *class_cache[NR_LOCKDEP_CACHING_CLASSES];
        const char                      *name;
#ifdef CONFIG_LOCK_STAT
        int                             cpu;
        unsigned long                   ip;
#endif  
};      


struct simple_xattrs {
        struct list_head head;
        spinlock_t lock;
};


struct dentry;
struct vfsmount;

struct path {
        struct vfsmount *mnt;
        struct dentry *dentry;
};

typedef struct { 
        volatile unsigned int lock;
} arch_rwlock_t;

struct kernfs_elem_symlink {
        struct kernfs_node      *target_kn;
};

struct kernfs_elem_attr {
        const struct kernfs_ops *ops;
        struct kernfs_open_node *open;
        loff_t                  size;
        struct kernfs_node      *notify_next;   /* for kernfs_notify() */
};


struct kernfs_elem_dir {
        unsigned long           subdirs;
        /* children rbtree starts here and goes through kn->rb */
        struct rb_root          children;

        /*
 *          * The kernfs hierarchy this directory belongs to.  This fits
 *                   * better directly in kernfs_node but is here to save space.
 *                            */
        struct kernfs_root      *root;
};

struct file_ra_state {
        pgoff_t start;                  /* where readahead started */
        unsigned int size;              /* # of readahead pages */
        unsigned int async_size;        /* do asynchronous readahead when
                                           there are only # of pages ahead */

        unsigned int ra_pages;          /* Maximum readahead window */
        unsigned int mmap_miss;         /* Cache miss stat for mmap accesses */
        loff_t prev_pos;                /* Cache last read() position */
};



enum pid_type
{
        PIDTYPE_PID,
        PIDTYPE_PGID,
        PIDTYPE_SID,
        PIDTYPE_MAX
};


typedef struct {
        arch_rwlock_t raw_lock;
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
} rwlock_t;


struct fown_struct {
        rwlock_t lock;          /* protects pid, uid, euid fields */
        struct pid *pid;        /* pid or -pgrp where SIGIO should be sent */
        enum pid_type pid_type; /* Kind of process group SIGIO should be sent to */
        kuid_t uid, euid;       /* uid/euid of process setting the owner */
        int signum;             /* posix.1b rt signal to be delivered on IO */
};

typedef unsigned fmode_t;

struct file {
        union { 
                struct llist_node       fu_llist;
                struct rcu_head         fu_rcuhead;
        } f_u;
        struct path             f_path;
        struct inode            *f_inode;       /* cached value */
        const struct file_operations    *f_op;

        /*
 *          * Protects f_ep_links, f_flags.
 *                   * Must not be taken from IRQ context.
 *                            */
        spinlock_t              f_lock;
        atomic_long_t           f_count;
        unsigned int            f_flags;
        fmode_t                 f_mode;
        struct mutex            f_pos_lock;
        loff_t                  f_pos;
        struct fown_struct      f_owner;
        const struct cred       *f_cred;
        struct file_ra_state    f_ra;

        u64                     f_version;
#ifdef CONFIG_SECURITY
        void                    *f_security;
#endif  
        /* needed for tty driver, and maybe others */
        void                    *private_data;

#ifdef CONFIG_EPOLL
        /* Used by fs/eventpoll.c to link all the hooks to this file */
        struct list_head        f_ep_links;
        struct list_head        f_tfile_llink;
#endif /* #ifdef CONFIG_EPOLL */
        struct address_space    *f_mapping;
} __attribute__((aligned(4)));  /* lest something weird decides that 2 is OK */

struct iattr {
        unsigned int    ia_valid;
        umode_t         ia_mode;
        kuid_t          ia_uid;
        kgid_t          ia_gid;
        loff_t          ia_size;
        struct timespec ia_atime;
        struct timespec ia_mtime;
        struct timespec ia_ctime;

        /*
 *          * Not an attribute, but an auxiliary info for filesystems wanting to
 *                   * implement an ftruncate() like method.  NOTE: filesystem should
 *                            * check for (ia_valid & ATTR_FILE), and not for (ia_file != NULL).
 *                                     */
        struct file     *ia_file;
};

struct kernfs_iattrs {
        struct iattr            ia_iattr;
        void                    *ia_secdata;
        u32                     ia_secdata_len;

        struct simple_xattrs    xattrs; 
};



struct kernfs_node {
        atomic_t                count;
        atomic_t                active;
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map      dep_map;
#endif
        /*
 *          * Use kernfs_get_parent() and kernfs_name/path() instead of
 *                   * accessing the following two fields directly.  If the node is
 *                            * never moved to a different parent, it is safe to access the
 *                                     * parent directly.
 *                                              */
        struct kernfs_node      *parent;
        const char              *name;

        struct rb_node          rb;

        const void              *ns;    /* namespace tag */
        unsigned int            hash;   /* ns + name hash */
        union {
                struct kernfs_elem_dir          dir;
                struct kernfs_elem_symlink      symlink;
                struct kernfs_elem_attr         attr;
        };

        void                    *priv;

        unsigned short          flags;
        umode_t                 mode;
        unsigned int            ino;
        struct kernfs_iattrs    *iattr;
};



struct cgroup_file {
        /* do not access any fields from outside cgroup core */
        struct kernfs_node *kn;
};


struct vmpressure {
        unsigned long scanned;
        unsigned long reclaimed;

        unsigned long tree_scanned;
        unsigned long tree_reclaimed;
        /* The lock is used to keep the scanned/reclaimed above in sync. */
        struct spinlock sr_lock;

        /* The list of vmpressure_event structs. */
        struct list_head events;
        /* Have to grab the lock on events traversal or modifications. */
        struct mutex events_lock;

        struct work_struct work;
};



/*
 *  * The memory controller data structure. The memory controller controls both
 *   * page cache and RSS per cgroup. We would eventually like to provide
 *    * statistics based on the statistics developed by Rik Van Riel for clock-pro,
 *     * to help the administrator determine what knobs to tune.
 *      */
struct mem_cgroup {
        struct cgroup_subsys_state css;

        /* Private memcg ID. Used to ID objects that outlive the cgroup */
        struct mem_cgroup_id id;

        /* Accounted resources */
        struct page_counter memory;
        struct page_counter swap;

        /* Legacy consumer-oriented counters */
        struct page_counter memsw;
        struct page_counter kmem;
        struct page_counter tcpmem;

        /* Normal memory consumption range */
        unsigned long low;
        unsigned long high;

        /* Range enforcement for interrupt charges */
        struct work_struct high_work;

        unsigned long soft_limit;

        /* vmpressure notifications */
        struct vmpressure vmpressure;

        /*
 *          * Should the accounting and control be hierarchical, per subtree?
 *                   */
        bool use_hierarchy;

        /* protected by memcg_oom_lock */
        bool            oom_lock;
        int             under_oom;

        int     swappiness;
        /* OOM-Killer disable */
        int             oom_kill_disable;

        /* handle for "memory.events" */
        struct cgroup_file events_file;

        /* protect arrays of thresholds */
        struct mutex thresholds_lock;

        /* thresholds for memory usage. RCU-protected */
        struct mem_cgroup_thresholds thresholds;

        /* thresholds for mem+swap usage. RCU-protected */
        struct mem_cgroup_thresholds memsw_thresholds;

        /* For oom notifier event fd */
        struct list_head oom_notify;



       /*
 *          * Should we move charges of a task when a task is moved into this
 *                   * mem_cgroup ? And what type of charges should we move ?
 *                            */
        unsigned long move_charge_at_immigrate;
        /*
 *          * set > 0 if pages under this cgroup are moving to other cgroup.
 *                   */
        atomic_t                moving_account;
        /* taken only while moving_account > 0 */
        spinlock_t              move_lock;
        struct task_struct      *move_lock_task;
        unsigned long           move_lock_flags;
        /*
 *          * percpu counter.
 *                   */
        struct mem_cgroup_stat_cpu *stat;

        unsigned long           socket_pressure;

        /* Legacy tcp memory accounting */
        bool                    tcpmem_active;
        int                     tcpmem_pressure;

#ifndef CONFIG_SLOB
        /* Index in the kmem_cache->memcg_params.memcg_caches array */
        int kmemcg_id;
        enum memcg_kmem_state kmem_state;
        struct list_head kmem_caches;
#endif

        int last_scanned_node;
#if MAX_NUMNODES > 1
        nodemask_t      scan_nodes;
        atomic_t        numainfo_events;
        atomic_t        numainfo_updating;
#endif

#ifdef CONFIG_CGROUP_WRITEBACK
        struct list_head cgwb_list;
        struct wb_domain cgwb_domain;
#endif

        /* List of events which userspace want to receive */
        struct list_head event_list;
        spinlock_t event_list_lock;

        struct mem_cgroup_per_node *nodeinfo[0];
        /* WARNING: nodeinfo must be the last member here */
};




/*
 *  * This struct is used to pass information from page reclaim to the shrinkers.
 *   * We consolidate the values for easier extention later.
 *    *
 *     * The 'gfpmask' refers to the allocation we are currently trying to
 *      * fulfil.
 *       */
struct shrink_control {
        gfp_t gfp_mask;

        /*
 *          * How many objects scan_objects should scan and try to reclaim.
 *                   * This is reset before every call, so it is safe for callees
 *                            * to modify.
 *                                     */
        unsigned long nr_to_scan;

        /* current node being shrunk (for NUMA aware shrinkers) */
        int nid;

        /* current memcg being shrunk (for memcg aware shrinkers) */
        struct mem_cgroup *memcg;
};

struct list_head s_list;

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
        struct list_head name = LIST_HEAD_INIT(name)

static LIST_HEAD(f2fs_list);

 #define __ARCH_SPIN_LOCK_UNLOCKED { 0 }

#ifdef CONFIG_DEBUG_SPINLOCK
# define SPIN_DEBUG_INIT(lockname)              \
        .magic = SPINLOCK_MAGIC,                \
        .owner_cpu = -1,                        \
        .owner = SPINLOCK_OWNER_INIT,
#else
# define SPIN_DEBUG_INIT(lockname)
#endif

#define __RAW_SPIN_LOCK_INITIALIZER(lockname)   \
        {                                       \
        .raw_lock = __ARCH_SPIN_LOCK_UNLOCKED,  \
        SPIN_DEBUG_INIT(lockname)               \
        SPIN_DEP_MAP_INIT(lockname) }

#define __RAW_SPIN_LOCK_UNLOCKED(lockname)      \
        (raw_spinlock_t) __RAW_SPIN_LOCK_INITIALIZER(lockname)

#define DEFINE_RAW_SPINLOCK(x)  raw_spinlock_t x = __RAW_SPIN_LOCK_UNLOCKED(x)

#define __SPIN_LOCK_INITIALIZER(lockname) \
        { { .rlock = __RAW_SPIN_LOCK_INITIALIZER(lockname) } }

#define __SPIN_LOCK_UNLOCKED(lockname) \
        (spinlock_t ) __SPIN_LOCK_INITIALIZER(lockname)

#define DEFINE_SPINLOCK(x)      spinlock_t x = __SPIN_LOCK_UNLOCKED(x)

static DEFINE_SPINLOCK(f2fs_list_lock);


#define list_entry(ptr, type, member) \
        container_of(ptr, type, member)

unsigned int shrinker_run_no;

unsigned long f2fs_shrink_count(struct shrinker *shrink,
				struct shrink_control *sc)
{
	struct f2fs_sb_info *sbi;
	struct f2fs_sb_info dummy;
	struct list_head *p;
	unsigned long count = 0;

	spin_lock(&f2fs_list_lock);
	p = f2fs_list.next;
	while (p != &f2fs_list) {
//		sbi = list_entry(p, struct f2fs_sb_info, s_list);
		sbi = list_entry(p, dummy, s_list);

		/* stop f2fs_put_super */
		if (!mutex_trylock(&sbi->umount_mutex)) {
			p = p->next;
			continue;
		}
		spin_unlock(&f2fs_list_lock);

		/* count extent cache entries */
		count += __count_extent_cache(sbi);

		/* shrink clean nat cache entries */
		count += __count_nat_entries(sbi);

		/* count free nids cache entries */
		count += __count_free_nids(sbi);

		spin_lock(&f2fs_list_lock);
		p = p->next;
		mutex_unlock(&sbi->umount_mutex);
	}
	spin_unlock(&f2fs_list_lock);
	return count;
}
unsigned long f2fs_shrink_scan(struct shrinker *shrink,
				struct shrink_control *sc)
{
	unsigned long nr = sc->nr_to_scan;
	struct f2fs_sb_info *sbi;
	struct list_head *p;
	unsigned int run_no;
	unsigned long freed = 0;

	spin_lock(&f2fs_list_lock);
	do {
		run_no = ++shrinker_run_no;
	} while (run_no == 0);
	p = f2fs_list.next;
	while (p != &f2fs_list) {
		struct f2fs_sb_info dummy;
		sbi = list_entry(p, dummy, s_list);

		if (sbi->shrinker_run_no == run_no)
			break;

		/* stop f2fs_put_super */
		if (!mutex_trylock(&sbi->umount_mutex)) {
			p = p->next;
			continue;
		}
		spin_unlock(&f2fs_list_lock);

		sbi->shrinker_run_no = run_no;

		/* shrink extent cache entries */
		freed += f2fs_shrink_extent_tree(sbi, nr >> 1);

		/* shrink clean nat cache entries */
		if (freed < nr)
			freed += try_to_free_nats(sbi, nr - freed);

		/* shrink free nids cache entries */
		if (freed < nr)
			freed += try_to_free_nids(sbi, nr - freed);

		spin_lock(&f2fs_list_lock);
		p = p->next;
		list_move_tail(&sbi->s_list, &f2fs_list);
		mutex_unlock(&sbi->umount_mutex);
		if (freed >= nr)
			break;
	}
	spin_unlock(&f2fs_list_lock);
	return freed;
}
