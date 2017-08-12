#include<stdio.h>
#include<stdint.h>
#include<stdbool.h>
#include<string.h>

#define ENOMEM 12
#define EINVAL 22
#define EIO 5
 #define EROFS 30


typedef unsigned char           u8;
typedef unsigned short          u16;
typedef unsigned int            u32;
typedef unsigned int            __u32;
typedef unsigned long long      u64;
typedef unsigned long long      __u64;
typedef signed char             s8;
typedef short                   s16;
typedef int                     s32;
typedef long long               s64;

/*
#define ATTR_LIST(name) (&f2fs_attr_##name.attr)
static struct attribute *f2fs_attrs[] = {
        ATTR_LIST(gc_min_sleep_time),
        ATTR_LIST(gc_max_sleep_time),
        ATTR_LIST(gc_no_gc_sleep_time),
        ATTR_LIST(gc_idle),
        ATTR_LIST(reclaim_segments),
        ATTR_LIST(max_small_discards),
        ATTR_LIST(batched_trim_sections),
        ATTR_LIST(ipu_policy),
        ATTR_LIST(min_ipu_util),
        ATTR_LIST(min_fsync_blocks),
        ATTR_LIST(min_hot_blocks),
        ATTR_LIST(max_victim_search),
        ATTR_LIST(dir_level),
        ATTR_LIST(ram_thresh),
        ATTR_LIST(ra_nid_pages),
        ATTR_LIST(dirty_nats_ratio),
        ATTR_LIST(cp_interval),
        ATTR_LIST(idle_interval),
#ifdef CONFIG_F2FS_FAULT_INJECTION
        ATTR_LIST(inject_rate),
        ATTR_LIST(inject_type),
#endif  
        ATTR_LIST(lifetime_write_kbytes),
        NULL,
};
*/

enum {  
        BG_GC = 0,
        FG_GC,
        FORCE_FG_GC,
};

enum mt76_msg_port {
        WLAN_PORT,
        CPU_RX_PORT,
        CPU_TX_PORT,
        HOST_PORT,
        VIRTUAL_CPU_RX_PORT,
        VIRTUAL_CPU_TX_PORT,
        DISCARD,
};


static struct kset *f2fs_kset;
/*
static struct kobj_type f2fs_ktype = {
        .default_attrs  = f2fs_attrs,
        .sysfs_ops      = &f2fs_attr_ops,
        .release        = f2fs_sb_release,
};
*/
#define CP_TRIMMED_FLAG         0x00000100
#define CP_NAT_BITS_FLAG        0x00000080
#define CP_CRC_RECOVERY_FLAG    0x00000040
#define CP_FASTBOOT_FLAG        0x00000020
#define CP_FSCK_FLAG            0x00000010
#define CP_ERROR_FLAG           0x00000008
#define CP_COMPACT_SUM_FLAG     0x00000004
#define CP_ORPHAN_PRESENT_FLAG  0x00000002
#define CP_UMOUNT_FLAG          0x00000001


#define KERN_SOH        "\001"          /* ASCII Start Of Header */
#define KERN_SOH_ASCII  '\001'

#define KERN_EMERG      KERN_SOH "0"    /* system is unusable */
#define KERN_ALERT      KERN_SOH "1"    /* action must be taken immediately */
#define KERN_CRIT       KERN_SOH "2"    /* critical conditions */
#define KERN_ERR        KERN_SOH "3"    /* error conditions */
#define KERN_WARNING    KERN_SOH "4"    /* warning conditions */
#define KERN_NOTICE     KERN_SOH "5"    /* normal but significant condition */
#define KERN_INFO       KERN_SOH "6"    /* informational */
#define KERN_DEBUG      KERN_SOH "7"    /* debug-level messages */

#define KERN_DEFAULT    KERN_SOH "d"    /* the default kernel loglevel */

/*
 *  * Annotation for a "continued" line of log printout (only done after a
 *   * line that had no enclosing \n). Only to be used by core/arch code
 *    * during early bootup (a continued line is not SMP-safe otherwise).
 *     */
#define KERN_CONT       KERN_SOH "c"

#define NR_CURSEG_DATA_TYPE     (3)
#define NR_CURSEG_NODE_TYPE     (3)
#define NR_CURSEG_TYPE  (NR_CURSEG_DATA_TYPE + NR_CURSEG_NODE_TYPE)

#define BIO_MAX_PAGES           256

#define MS_LAZYTIME     (1<<25) /* Update the on-disk [acm]times lazily */

#define F2FS_IO_SIZE_BITS(sbi)  ((sbi)->write_io_size_bits) /* power of 2 */

#define test_opt(sbi, option)   ((sbi)->mount_opt.opt & F2FS_MOUNT_##option)

#define clear_opt(sbi, option)  ((sbi)->mount_opt.opt &= ~F2FS_MOUNT_##option)

#define set_opt(sbi, option)    ((sbi)->mount_opt.opt |= F2FS_MOUNT_##option)

#define F2FS_MOUNT_BG_GC                0x00000001
#define F2FS_MOUNT_DISABLE_ROLL_FORWARD 0x00000002
#define F2FS_MOUNT_DISCARD              0x00000004
#define F2FS_MOUNT_NOHEAP               0x00000008
#define F2FS_MOUNT_XATTR_USER           0x00000010
#define F2FS_MOUNT_POSIX_ACL            0x00000020
#define F2FS_MOUNT_DISABLE_EXT_IDENTIFY 0x00000040
#define F2FS_MOUNT_INLINE_XATTR         0x00000080
#define F2FS_MOUNT_INLINE_DATA          0x00000100
#define F2FS_MOUNT_INLINE_DENTRY        0x00000200
#define F2FS_MOUNT_FLUSH_MERGE          0x00000400
#define F2FS_MOUNT_NOBARRIER            0x00000800
#define F2FS_MOUNT_FASTBOOT             0x00001000
#define F2FS_MOUNT_EXTENT_CACHE         0x00002000
#define F2FS_MOUNT_FORCE_FG_GC          0x00004000
#define F2FS_MOUNT_DATA_FLUSH           0x00008000
#define F2FS_MOUNT_FAULT_INJECTION      0x00010000
#define F2FS_MOUNT_ADAPTIVE             0x00020000
#define F2FS_MOUNT_LFS                  0x00040000

#ifdef __CHECKER__
#define __bitwise__ __attribute__((bitwise))
#else
#define __bitwise__
#endif
#define __bitwise __bitwise__

typedef unsigned fmode_t;

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

struct seg_entry {
        unsigned int type:6;            /* segment type like CURSEG_XXX_TYPE */
        unsigned int valid_blocks:10;   /* # of valid blocks */
        unsigned int ckpt_valid_blocks:10;      /* # of valid blocks last cp */
        unsigned int padding:6;         /* padding */
        unsigned char *cur_valid_map;   /* validity bitmap of blocks */
#ifdef CONFIG_F2FS_CHECK_FS
        unsigned char *cur_valid_map_mir;       /* mirror of current valid bitmap */
#endif  
        /*
 *          * # of valid blocks and the validity bitmap stored in the the last
 *                   * checkpoint pack. This information is used by the SSR mode.
 *                            */
        unsigned char *ckpt_valid_map;  /* validity bitmap of blocks last cp */
        unsigned char *discard_map;
        unsigned long long mtime;       /* modification time of the segment */
};

struct seq_file {
        char *buf;
        size_t size;
        size_t from;
        size_t count;
        size_t pad_until;
        loff_t index;
        loff_t read_pos;
        u64 version;
        struct mutex lock;
        const struct seq_operations *op;
        int poll_event;
        const struct file *file;
        void *private;
};

struct f2fs_sb_info {
        struct super_block *sb;                 /* pointer to VFS super block */
        struct proc_dir_entry *s_proc;          /* proc entry */
        struct f2fs_super_block *raw_super;     /* raw super block pointer */
        int valid_super_block;                  /* valid super block no */
        unsigned long s_flag;                           /* flags for sbi */

        unsigned int blocks_per_blkz;           /* F2FS blocks per zone */
        unsigned int log_blocks_per_blkz;       /* log2 F2FS blocks per zone */

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

enum {  
        Opt_gc_background,
        Opt_disable_roll_forward,
        Opt_norecovery,
        Opt_discard,
        Opt_nodiscard,
        Opt_noheap,
        Opt_heap,
        Opt_user_xattr,
        Opt_nouser_xattr,
        Opt_acl,
        Opt_noacl,
        Opt_active_logs,
        Opt_disable_ext_identify,
        Opt_inline_xattr,
        Opt_noinline_xattr,
        Opt_inline_data,
        Opt_inline_dentry,
        Opt_noinline_dentry,
        Opt_flush_merge,
        Opt_noflush_merge,
        Opt_nobarrier,
        Opt_fastboot,
        Opt_extent_cache,
        Opt_noextent_cache,
        Opt_noinline_data,
        Opt_data_flush,
        Opt_mode,
        Opt_io_size_bits,
        Opt_fault_injection,
        Opt_lazytime,
        Opt_nolazytime,
        Opt_err,
};


struct match_token {
        int token;
        const char *pattern;
};

typedef struct match_token match_table_t[];

static match_table_t f2fs_tokens = {
        {Opt_gc_background, "background_gc=%s"},
        {Opt_disable_roll_forward, "disable_roll_forward"},
        {Opt_norecovery, "norecovery"},
        {Opt_discard, "discard"},
        {Opt_nodiscard, "nodiscard"},
        {Opt_noheap, "no_heap"},
        {Opt_heap, "heap"},
        {Opt_user_xattr, "user_xattr"},
        {Opt_nouser_xattr, "nouser_xattr"},
        {Opt_acl, "acl"},
        {Opt_noacl, "noacl"},
        {Opt_active_logs, "active_logs=%u"},
        {Opt_disable_ext_identify, "disable_ext_identify"},
        {Opt_inline_xattr, "inline_xattr"},
        {Opt_noinline_xattr, "noinline_xattr"},
        {Opt_inline_data, "inline_data"},
        {Opt_inline_dentry, "inline_dentry"},
        {Opt_noinline_dentry, "noinline_dentry"},
        {Opt_flush_merge, "flush_merge"},
        {Opt_noflush_merge, "noflush_merge"},
        {Opt_nobarrier, "nobarrier"},
        {Opt_fastboot, "fastboot"},
        {Opt_extent_cache, "extent_cache"},
        {Opt_noextent_cache, "noextent_cache"},
        {Opt_noinline_data, "noinline_data"},
        {Opt_data_flush, "data_flush"},
        {Opt_mode, "mode=%s"},
        {Opt_io_size_bits, "io_bits=%u"},
        {Opt_fault_injection, "fault_injection=%u"},
        {Opt_lazytime, "lazytime"},
        {Opt_nolazytime, "nolazytime"},
        {Opt_err, NULL},
};

#define FDEV(i)                         (sbi->devs[i])


typedef struct match_token match_table_t[];



/* Describe the location within a string of a substring */
typedef struct {
        char *from;
        char *to;
} substring_t;

enum {MAX_OPT_ARGS = 3};


#define FMODE_EXCL              (( fmode_t)0x80)


struct f2fs_dev_info {
        struct block_device *bdev;
        char path[MAX_PATH_LEN];
        unsigned int total_segments;
        block_t start_blk;
        block_t end_blk;
        unsigned int nr_blkz;                   /* Total number of zones */
        u8 *blkz_type;                          /* Array of zones type */
};

typedef struct seqcount {
        unsigned sequence;
#ifdef CONFIG_DEBUG_LOCK_ALLOC
        struct lockdep_map dep_map;
#endif
} seqcount_t;


#define MAXQUOTAS 3


struct quota_format_type;

typedef long long qsize_t;

struct mem_dqinfo {
        struct quota_format_type *dqi_format;
        int dqi_fmt_id;         /* Id of the dqi_format - used when turning
                                 * quotas on after remount RW */
        struct list_head dqi_dirty_list;        /* List of dirty dquots */
        unsigned long dqi_flags;
        unsigned int dqi_bgrace;
        unsigned int dqi_igrace;
        qsize_t dqi_max_spc_limit;
        qsize_t dqi_max_ino_limit;
        void *dqi_priv;
};



enum rcu_sync_type { RCU_SYNC, RCU_SCHED_SYNC, RCU_BH_SYNC };

/* Structure to mediate between updaters and fastpath-using readers.  */
struct rcu_sync {
        int                     gp_state;
        int                     gp_count;
        wait_queue_head_t       gp_wait;

        int                     cb_state;
        struct rcu_head         cb_head;

        enum rcu_sync_type      gp_type;
};



struct rcuwait {
        struct task_struct *task;
};



struct percpu_rw_semaphore {
        struct rcu_sync         rss;
        unsigned int  *read_count;
        struct rw_semaphore     rw_sem; /* slowpath */
        struct rcuwait          writer; /* blocked writer */
        int                     readers_block;
};



/* Possible states of 'frozen' field */
enum {  
        SB_UNFROZEN = 0,                /* FS is unfrozen */
        SB_FREEZE_WRITE = 1,            /* Writes, dir ops, ioctls frozen */
        SB_FREEZE_PAGEFAULT = 2,        /* Page faults stopped as well */
        SB_FREEZE_FS = 3,               /* For internal FS use (e.g. to stop
                                         * internal threads if needed) */
        SB_FREEZE_COMPLETE = 4,         /* ->freeze_fs finished successfully */
};

#define SB_FREEZE_LEVELS (SB_FREEZE_COMPLETE - 1)



struct sb_writers {
        int                             frozen;         /* Is sb frozen? */
        wait_queue_head_t               wait_unfrozen;  /* for get_super_thawed() */
        struct percpu_rw_semaphore      rw_sem[SB_FREEZE_LEVELS];
};

struct quota_info {
        unsigned int flags;                     /* Flags for diskquotas on this device */
        struct mutex dqio_mutex;                /* lock device while I/O in progress */
        struct inode *files[MAXQUOTAS];         /* inodes of quotafiles */
        struct mem_dqinfo info[MAXQUOTAS];      /* Information for each quota type */
        const struct quota_format_ops *ops[MAXQUOTAS];  /* Operations for each type */
};

struct hlist_bl_head {
        struct hlist_bl_node *first;
};

struct list_lru_one {
        struct list_head        list;
        /* may become negative during memcg reparenting */
        long                    nr_items;
};

struct list_lru_memcg {
        /* array of per cgroup lists, indexed by memcg_cache_id */
        struct list_lru_one     *lru[0];
};

struct list_lru_node {
        /* protects all lists on the node, including per cgroup */
        spinlock_t              lock;
        /* global list, used for the root cgroup in cgroup aware lrus */
        struct list_lru_one     lru;
#if defined(CONFIG_MEMCG) && !defined(CONFIG_SLOB)
        /* for cgroup aware lrus points to per cgroup lists, otherwise NULL */
        struct list_lru_memcg   *memcg_lrus;
#endif  
        long nr_items;
} ____cacheline_aligned_in_smp;

struct list_lru {
        struct list_lru_node    *node;
#if defined(CONFIG_MEMCG) && !defined(CONFIG_SLOB)
        struct list_head        list;
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


struct super_block {
        struct list_head        s_list;         /* Keep this first */
        dev_t                   s_dev;          /* search index; _not_ kdev_t */
        unsigned char           s_blocksize_bits;
        unsigned long           s_blocksize;
        loff_t                  s_maxbytes;     /* Max file size */
        struct file_system_type *s_type;
        const struct super_operations   *s_op;
        const struct dquot_operations   *dq_op;
        const struct quotactl_ops       *s_qcop;
        const struct export_operations *s_export_op;
        unsigned long           s_flags;
        unsigned long           s_iflags;       /* internal SB_I_* flags */
        unsigned long           s_magic;
        struct dentry           *s_root;
        struct rw_semaphore     s_umount;
        int                     s_count;
        atomic_t                s_active;
#ifdef CONFIG_SECURITY
        void                    *s_security;
#endif
        const struct xattr_handler **s_xattr;

        const struct fscrypt_operations *s_cop;

        struct hlist_bl_head    s_anon;         /* anonymous dentries for (nfs) exporting */
        struct list_head        s_mounts;       /* list of mounts; _not_ for fs use */
        struct block_device     *s_bdev;
        struct backing_dev_info *s_bdi;
        struct mtd_info         *s_mtd;
        struct hlist_node       s_instances;
        unsigned int            s_quota_types;  /* Bitmask of supported quota types */
        struct quota_info       s_dquot;        /* Diskquota specific options */

        struct sb_writers       s_writers;

        char s_id[32];                          /* Informational name */
        u8 s_uuid[16];                          /* UUID */

        void                    *s_fs_info;     /* Filesystem private info */
        unsigned int            s_max_links;
        fmode_t                 s_mode;

        /* Granularity of c/m/atime in ns.
 *            Cannot be worse than a second */
        u32                s_time_gran;

        /*
 *          * The next field is for VFS *only*. No filesystems have any business
 *                   * even looking at it. You had been warned.
 *                            */
        struct mutex s_vfs_rename_mutex;        /* Kludge */

       /*
 *          * Filesystem subtype.  If non-empty the filesystem type field
 *                   * in /proc/mounts will be "type.subtype"
 *                            */
        char *s_subtype;

        /*
 *          * Saved mount options for lazy filesystems using
 *                   * generic_show_options()
 *                            */
        char __rcu *s_options;
        const struct dentry_operations *s_d_op; /* default d_op for dentries */

        /*
 *          * Saved pool identifier for cleancache (-1 means none)
 *                   */
        int cleancache_poolid;

        struct shrinker s_shrink;       /* per-sb shrinker handle */

        /* Number of inodes with nlink == 0 but still referenced */
        atomic_long_t s_remove_count;

        /* Being remounted read-only */
        int s_readonly_remount;

        /* AIO completions deferred from interrupt context */
        struct workqueue_struct *s_dio_done_wq;
        struct hlist_head s_pins;

        /*
 *          * Owning user namespace and default context in which to
 *                   * interpret filesystem uids, gids, quotas, device nodes,
 *                            * xattrs and security labels.
 *                                     */
        struct user_namespace *s_user_ns;

        /*
 *          * Keep the lru lists last in the structure so they always sit on their
 *                   * own individual cachelines.
 *                            */
//        struct list_lru         s_dentry_lru ____cacheline_aligned_in_smp;
  //      struct list_lru         s_inode_lru ____cacheline_aligned_in_smp;
        struct rcu_head         rcu;
        struct work_struct      destroy_work;

        struct mutex            s_sync_lock;    /* sync serialisation lock */

       /*
 *          * Indicates how deep in a filesystem stack this SB is
 *                   */
        int s_stack_depth;

        /* s_inode_list_lock protects s_inodes */
//        spinlock_t              s_inode_list_lock ____cacheline_aligned_in_smp;
        struct list_head        s_inodes;       /* all inodes */

        spinlock_t              s_inode_wblist_lock;
        struct list_head        s_inodes_wb;    /* writeback inodes */
};

#define F2FS_MIN_SEGMENTS       9 /* SB + 2 (CP + SIT + NAT) + SSA + MAIN */

#define NULL_SECNO                      ((unsigned int)(~0))

#define NULL_SEGNO                      ((unsigned int)(~0))

#define DEF_MAX_VICTIM_SEARCH 4096 /* covers 8GB */

#define DEF_DIR_LEVEL           0

#define DEF_CP_INTERVAL                 60      /* 60 secs */

#define DEF_IDLE_INTERVAL               5       /* 5 secs */

enum {  
        SBI_IS_DIRTY,                           /* dirty flag for checkpoint */
        SBI_IS_CLOSE,                           /* specify unmounting */
        SBI_NEED_FSCK,                          /* need fsck.f2fs to fix */
        SBI_POR_DOING,                          /* recovery is doing or not */
        SBI_NEED_SB_WRITE,                      /* need to recover superblock */
        SBI_NEED_CP,                            /* need to checkpoint */
};

#define PAGE_SHIFT      13
#define PAGE_SIZE       (1 << PAGE_SHIFT)
#define PAGE_MASK       (~(PAGE_SIZE-1))

#define MAX_ACTIVE_LOGS 16
#define MAX_ACTIVE_NODE_LOGS    8
#define MAX_ACTIVE_DATA_LOGS    8

#define NAT_ENTRY_PER_BLOCK (PAGE_SIZE / sizeof(struct f2fs_nat_entry))
#define NAT_ENTRY_BITMAP_SIZE   ((NAT_ENTRY_PER_BLOCK + 7) / 8)

struct f2fs_nat_entry {
        __u8 version;           /* latest version of cached nat entry */
        __le32 ino;             /* inode number */
        __le32 block_addr;      /* block address */
} ;

struct f2fs_nat_block {
        struct f2fs_nat_entry entries[NAT_ENTRY_PER_BLOCK];
} ;

struct f2fs_checkpoint {
        __le64 checkpoint_ver;          /* checkpoint block version number */
        __le64 user_block_count;        /* # of user blocks */
        __le64 valid_block_count;       /* # of valid blocks in main area */
        __le32 rsvd_segment_count;      /* # of reserved segments for gc */
        __le32 overprov_segment_count;  /* # of overprovision segments */
        __le32 free_segment_count;      /* # of free segments in main area */

        /* information of current node segments */
        __le32 cur_node_segno[MAX_ACTIVE_NODE_LOGS];
        __le16 cur_node_blkoff[MAX_ACTIVE_NODE_LOGS];
        /* information of current data segments */
        __le32 cur_data_segno[MAX_ACTIVE_DATA_LOGS];
        __le16 cur_data_blkoff[MAX_ACTIVE_DATA_LOGS];
        __le32 ckpt_flags;              /* Flags : umount and journal_present */
        __le32 cp_pack_total_block_count;       /* total # of one cp pack */
        __le32 cp_pack_start_sum;       /* start block number of data summary */
        __le32 valid_node_count;        /* Total number of valid nodes */
        __le32 valid_inode_count;       /* Total number of valid inodes */
        __le32 next_free_nid;           /* Next free node number */
        __le32 sit_ver_bitmap_bytesize; /* Default value 64 */
        __le32 nat_ver_bitmap_bytesize; /* Default value 256 */
        __le32 checksum_offset;         /* checksum offset inside cp block */
        __le64 elapsed_time;            /* mounted time */
        /* allocation type of current segment */
        unsigned char alloc_type[MAX_ACTIVE_LOGS];

        /* SIT and NAT version bitmap */
        unsigned char sit_nat_version_bitmap[1];
} ;

struct block_device {
        dev_t                   bd_dev;  /* not a kdev_t - it's a search key */
        int                     bd_openers;
        struct inode *          bd_inode;       /* will die */
        struct super_block *    bd_super;
        struct mutex            bd_mutex;       /* open/close mutex */
        void *                  bd_claiming;
        void *                  bd_holder;
        int                     bd_holders;
        bool                    bd_write_holder;
#ifdef CONFIG_SYSFS
        struct list_head        bd_holder_disks;
#endif  
        struct block_device *   bd_contains;
        unsigned                bd_block_size;
        struct hd_struct *      bd_part;
        /* number of times partitions within this device have been opened. */
        unsigned                bd_part_count;
        int                     bd_invalidated;
        struct gendisk *        bd_disk;
        struct request_queue *  bd_queue;
        struct backing_dev_info *bd_bdi;
        struct list_head        bd_list;
        /*
 *          * Private data.  You must have bd_claim'ed the block_device
 *                   * to use this.  NOTE:  bd_claim allows an owner to claim
 *                            * the same device multiple times, the owner must take special
 *                                     * care to not mess up bd_private for that case.
 *                                              */
        unsigned long           bd_private;

        /* The counter of freeze processes */
        int                     bd_fsfreeze_count;
        /* Mutex for freeze */
        struct mutex            bd_fsfreeze_mutex;
};

struct dev_archdata {
#ifdef CONFIG_DMABOUNCE
        struct dmabounce_device_info *dmabounce;
#endif
#ifdef CONFIG_IOMMU_API
        void *iommu; /* private IOMMU data */
#endif
#ifdef CONFIG_ARM_DMA_USE_IOMMU
        struct dma_iommu_mapping        *mapping;
#endif
#ifdef CONFIG_XEN
        const struct dma_map_ops *dev_dma_ops;
#endif  
        unsigned int dma_coherent:1;
        unsigned int dma_ops_setup:1;
};


struct klist_node {
        void                    *n_klist;       /* never access directly */
        struct list_head        n_node;
        struct kref             n_ref;
};



enum dl_dev_state {
        DL_DEV_NO_DRIVER = 0,
        DL_DEV_PROBING,
        DL_DEV_DRIVER_BOUND,
        DL_DEV_UNBINDING,
};

struct dev_links_info {
        struct list_head suppliers;
        struct list_head consumers;
        enum dl_dev_state status;
};

typedef struct pm_message {
        int event;
} pm_message_t;


struct dev_pm_info {
        pm_message_t            power_state;
        unsigned int            can_wakeup:1;
        unsigned int            async_suspend:1;
        bool                    in_dpm_list:1;  /* Owned by the PM core */
        bool                    is_prepared:1;  /* Owned by the PM core */
        bool                    is_suspended:1; /* Ditto */
        bool                    is_noirq_suspended:1;
        bool                    is_late_suspended:1;
        bool                    early_init:1;   /* Owned by the PM core */
        bool                    direct_complete:1;      /* Owned by the PM core */
        spinlock_t              lock;
#ifdef CONFIG_PM_SLEEP
        struct list_head        entry;
        struct completion       completion;
        struct wakeup_source    *wakeup;
        bool                    wakeup_path:1;
        bool                    syscore:1;
        bool                    no_pm_callbacks:1;      /* Owned by the PM core */
#else   
        unsigned int            should_wakeup:1;
#endif
#ifdef CONFIG_PM
        struct timer_list       suspend_timer;
        unsigned long           timer_expires;
        struct work_struct      work;
        wait_queue_head_t       wait_queue;
        struct wake_irq         *wakeirq;
        atomic_t                usage_count;
        atomic_t                child_count;
        unsigned int            disable_depth:3;
        unsigned int            idle_notification:1;
        unsigned int            request_pending:1;
        unsigned int            deferred_resume:1;
        unsigned int            run_wake:1;
        unsigned int            runtime_auto:1;
        bool                    ignore_children:1;
        unsigned int            no_callbacks:1;
        unsigned int            irq_safe:1;
        unsigned int            use_autosuspend:1;
        unsigned int            timer_autosuspends:1;
        unsigned int            memalloc_noio:1;
        unsigned int            links_count;
        enum rpm_request        request;
        enum rpm_status         runtime_status;
        int                     runtime_error;
        int                     autosuspend_delay;
        unsigned long           last_busy;
        unsigned long           active_jiffies;
        unsigned long           suspended_jiffies;
        unsigned long           accounting_timestamp;
#endif
        struct pm_subsys_data   *subsys_data;  /* Owned by the subsystem. */
        void (*set_latency_tolerance)(struct device *, s32);
        struct dev_pm_qos       *qos;
};




struct device {
        struct device           *parent;

        struct device_private   *p;

        struct kobject kobj;
        const char              *init_name; /* initial name of the device */
        const struct device_type *type;

        struct mutex            mutex;  /* mutex to synchronize calls to
                                         * its driver.
                                         *                                          */

        struct bus_type *bus;           /* type of bus device is on */
        struct device_driver *driver;   /* which driver has allocated this
                                           device */
        void            *platform_data; /* Platform specific data, device
                                           core doesn't touch it */
        void            *driver_data;   /* Driver data, set and get with
                                           dev_set/get_drvdata */
        struct dev_links_info   links;
        struct dev_pm_info      power;
        struct dev_pm_domain    *pm_domain;

#ifdef CONFIG_GENERIC_MSI_IRQ_DOMAIN
        struct irq_domain       *msi_domain;
#endif
#ifdef CONFIG_PINCTRL
        struct dev_pin_info     *pins;
#endif
#ifdef CONFIG_GENERIC_MSI_IRQ
        struct list_head        msi_list;
#endif

#ifdef CONFIG_NUMA
        int             numa_node;      /* NUMA node this device is close to */
#endif
        const struct dma_map_ops *dma_ops;
        u64             *dma_mask;      /* dma mask (if dma'able device) */
        u64             coherent_dma_mask;/* Like dma_mask, but for
                                             alloc_coherent mappings as
                                             not all hardware supports
                                             64 bit addresses for consistent
                                             allocations such descriptors. */

      unsigned long   dma_pfn_offset;

        struct device_dma_parameters *dma_parms;

        struct list_head        dma_pools;      /* dma pools (if dma'ble) */

        struct dma_coherent_mem *dma_mem; /* internal for coherent mem
                                             override */
#ifdef CONFIG_DMA_CMA
        struct cma *cma_area;           /* contiguous memory area for dma
                                           allocations */
#endif
        /* arch specific additions */
        struct dev_archdata     archdata;

        struct device_node      *of_node; /* associated device tree node */
        struct fwnode_handle    *fwnode; /* firmware device node */

        dev_t                   devt;   /* dev_t, creates the sysfs "dev" */
        u32                     id;     /* device instance */

        spinlock_t              devres_lock;
        struct list_head        devres_head;

        struct klist_node       knode_class;
        struct class            *class;
        const struct attribute_group **groups;  /* optional groups */

        void    (*release)(struct device *dev);
        struct iommu_group      *iommu_group;
        struct iommu_fwspec     *iommu_fwspec;

        bool                    offline_disabled:1;
        bool                    offline:1;
};



struct blk_zone {
        __u64   start;          /* Zone start sector */
        __u64   len;            /* Zone length in number of sectors */
        __u64   wp;             /* Zone write pointer position */
        __u8    type;           /* Zone type */
        __u8    cond;           /* Zone condition */
        __u8    non_seq;        /* Non-sequential write resources active */
        __u8    reset;          /* Reset write pointer recommended */
        __u8    reserved[36];
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
//#ifdef  CONFIG_SMP
//        struct disk_stats __percpu *dkstats;
//#else   
//        struct disk_stats dkstats;
//#endif  
        struct percpu_ref ref;
        struct rcu_head rcu_head;
};

typedef void (bh_end_io_t)(struct buffer_head *bh, int uptodate);

#define F2FS_SUPER_OFFSET               1024    /* byte-size offset */
#define RDEV(i)                         (raw_super->devs[i])

struct buffer_head {
        unsigned long b_state;          /* buffer state bitmap (see above) */
        struct buffer_head *b_this_page;/* circular list of page's buffers */
        struct page *b_page;            /* the page this bh is mapped to */

        sector_t b_blocknr;             /* start block number */
        size_t b_size;                  /* size of mapping */
        char *b_data;                   /* pointer to data within the page */

        struct block_device *b_bdev;
        bh_end_io_t *b_end_io;          /* I/O completion */
        void *b_private;                /* reserved for b_end_io */
        struct list_head b_assoc_buffers; /* associated with another mapping */
        struct address_space *b_assoc_map;      /* mapping this buffer is
                                                   associated with */
        atomic_t b_count;               /* users using this buffer_head */
};

#define F2FS_BLKSIZE                    4096    /* support only 4KB block */

#define F2FS_LINK_MAX   0xffffffff      /* maximum link count per file */


static struct inode *f2fs_alloc_inode(struct super_block *sb);
static int f2fs_drop_inode(struct inode *inode);
static void f2fs_destroy_inode(struct inode *inode);
int f2fs_write_inode(struct inode *inode, struct writeback_control *wbc);
static void f2fs_dirty_inode(struct inode *inode, int flags);
static int f2fs_show_options(struct seq_file *seq, struct dentry *root);
void f2fs_evict_inode(struct inode *inode);
static void f2fs_put_super(struct super_block *sb);
int f2fs_sync_fs(struct super_block *sb, int sync);
static int f2fs_freeze(struct super_block *sb);
static int f2fs_unfreeze(struct super_block *sb);
static int f2fs_statfs(struct dentry *dentry, struct kstatfs *buf);
static int f2fs_remount(struct super_block *sb, int *flags, char *data);


#define FADVISE_ENCRYPT_BIT     0x04


struct f2fs_inode_info {
        struct inode vfs_inode;         /* serve a vfs inode */
        unsigned long i_flags;          /* keep an inode flags for ioctl */
        unsigned char i_advise;         /* use to give file attribute hints */
        unsigned char i_dir_level;      /* use for dentry level for large dir */
        unsigned int i_current_depth;   /* use only in directory structure */
        unsigned int i_pino;            /* parent inode number */
        umode_t i_acl_mode;             /* keep file acl mode temporarily */

        /* Use below internally in f2fs*/
        unsigned long flags;            /* use to pass per-file flags */
        struct rw_semaphore i_sem;      /* protect fi info */
        atomic_t dirty_pages;           /* # of dirty pages */
        f2fs_hash_t chash;              /* hash value of given file name */
        unsigned int clevel;            /* maximum level of given file name */
        struct task_struct *task;       /* lookup and create consistency */
        nid_t i_xattr_nid;              /* node id that contains xattrs */
        loff_t  last_disk_size;         /* lastly written file size */

        struct list_head dirty_list;    /* dirty list for dirs and files */
        struct list_head gdirty_list;   /* linked in global dirty list */
        struct list_head inmem_pages;   /* inmemory pages managed by f2fs */
        struct mutex inmem_lock;        /* lock for inmemory pages */
        struct extent_tree *extent_tree;        /* cached extent_tree entry */
        struct rw_semaphore dio_rwsem[2];/* avoid racing between dio and gc */
};



struct super_operations {
        struct inode *(*alloc_inode)(struct super_block *sb);
        void (*destroy_inode)(struct inode *);

        void (*dirty_inode) (struct inode *, int flags);
        int (*write_inode) (struct inode *, struct writeback_control *wbc);
        int (*drop_inode) (struct inode *);
        void (*evict_inode) (struct inode *);
        void (*put_super) (struct super_block *);
        int (*sync_fs)(struct super_block *sb, int wait);
        int (*freeze_super) (struct super_block *);
        int (*freeze_fs) (struct super_block *);
        int (*thaw_super) (struct super_block *);
        int (*unfreeze_fs) (struct super_block *);
        int (*statfs) (struct dentry *, struct kstatfs *);
        int (*remount_fs) (struct super_block *, int *, char *);
        void (*umount_begin) (struct super_block *);

        int (*show_options)(struct seq_file *, struct dentry *);
        int (*show_devname)(struct seq_file *, struct dentry *);
        int (*show_path)(struct seq_file *, struct dentry *);
        int (*show_stats)(struct seq_file *, struct dentry *);
#ifdef CONFIG_QUOTA
        ssize_t (*quota_read)(struct super_block *, int, char *, size_t, loff_t);
        ssize_t (*quota_write)(struct super_block *, int, const char *, size_t, loff_t);
        struct dquot **(*get_dquots)(struct inode *);
#endif  
        int (*bdev_try_to_free_page)(struct super_block*, struct page*, gfp_t);
        long (*nr_cached_objects)(struct super_block *,
                                  struct shrink_control *);
        long (*free_cached_objects)(struct super_block *,
                                    struct shrink_control *);
};


static struct super_operations f2fs_sops = {
        .alloc_inode    = f2fs_alloc_inode,
        .drop_inode     = f2fs_drop_inode,
        .destroy_inode  = f2fs_destroy_inode,
        .write_inode    = f2fs_write_inode,
        .dirty_inode    = f2fs_dirty_inode,
        .show_options   = f2fs_show_options,
        .evict_inode    = f2fs_evict_inode,
        .put_super      = f2fs_put_super,
        .sync_fs        = f2fs_sync_fs,
        .freeze_fs      = f2fs_freeze,
        .unfreeze_fs    = f2fs_unfreeze,
        .statfs         = f2fs_statfs,
        .remount_fs     = f2fs_remount,
};


#ifndef container_of
#define container_of(ptr, type, member) \
    (type *)((char *)(ptr) - (char *) &((type *)0)->member)
#endif  


static inline struct f2fs_inode_info *F2FS_I(struct inode *inode)
{
        return container_of(inode, struct f2fs_inode_info, vfs_inode);
}


static inline int is_file(struct inode *inode, int type)
{
        return F2FS_I(inode)->i_advise & type;
}


#define file_is_encrypt(inode)  is_file(inode, FADVISE_ENCRYPT_BIT)


static inline bool f2fs_encrypted_inode(struct inode *inode)
{
        return file_is_encrypt(inode);
}


#define F2FS_NAME_LEN           255


#define XATTR_CREATE 0x1

#define F2FS_XATTR_MAGIC                0xF2F52011

/* Maximum number of references to one attribute block */
#define F2FS_XATTR_REFCOUNT_MAX         1024

/* Name indexes */
#define F2FS_SYSTEM_ADVISE_NAME                 "system.advise"
#define F2FS_XATTR_INDEX_USER                   1
#define F2FS_XATTR_INDEX_POSIX_ACL_ACCESS       2
#define F2FS_XATTR_INDEX_POSIX_ACL_DEFAULT      3
#define F2FS_XATTR_INDEX_TRUSTED                4
#define F2FS_XATTR_INDEX_LUSTRE                 5
#define F2FS_XATTR_INDEX_SECURITY               6
#define F2FS_XATTR_INDEX_ADVISE                 7


#define F2FS_XATTR_NAME_ENCRYPTION_CONTEXT      "c"

#define F2FS_XATTR_INDEX_ENCRYPTION             9


static int f2fs_get_context(struct inode *inode, void *ctx, size_t len)
{
        return f2fs_getxattr(inode, F2FS_XATTR_INDEX_ENCRYPTION,
                                F2FS_XATTR_NAME_ENCRYPTION_CONTEXT,
                                ctx, len, NULL);
}

static int f2fs_set_context(struct inode *inode, const void *ctx, size_t len,
                                                        void *fs_data)
{
        return f2fs_setxattr(inode, F2FS_XATTR_INDEX_ENCRYPTION,
                                F2FS_XATTR_NAME_ENCRYPTION_CONTEXT,
                                ctx, len, fs_data, XATTR_CREATE);
}

static unsigned f2fs_max_namelen(struct inode *inode)
{
        return S_ISLNK(inode->i_mode) ?
                        inode->i_sb->s_blocksize : F2FS_NAME_LEN;
}

bool f2fs_empty_dir(struct inode *dir);


struct fscrypt_operations {
        unsigned int flags;
        const char *key_prefix;
        int (*get_context)(struct inode *, void *, size_t);
        int (*set_context)(struct inode *, const void *, size_t, void *);
        int (*dummy_context)(struct inode *);
        bool (*is_encrypted)(struct inode *);
        bool (*empty_dir)(struct inode *);
        unsigned (*max_namelen)(struct inode *);
};


static const struct fscrypt_operations f2fs_cryptops = {
        .key_prefix     = "f2fs:",
        .get_context    = f2fs_get_context,
        .set_context    = f2fs_set_context,
        .is_encrypted   = f2fs_encrypted_inode,
        .empty_dir      = f2fs_empty_dir,
        .max_namelen    = f2fs_max_namelen,
};

enum {  
        CURSEG_HOT_DATA = 0,    /* directory entry blocks */
        CURSEG_WARM_DATA,       /* data blocks */
        CURSEG_COLD_DATA,       /* multimedia or GCed data blocks */
        CURSEG_HOT_NODE,        /* direct node blocks of directory files */
        CURSEG_WARM_NODE,       /* direct node blocks of normal files */
        CURSEG_COLD_NODE,       /* indirect node blocks */
        NO_CHECK_TYPE,
};

struct curseg_info {
        struct mutex curseg_mutex;              /* lock for consistency */
        struct f2fs_summary_block *sum_blk;     /* cached summary block */
        struct rw_semaphore journal_rwsem;      /* protect journal area */
        struct f2fs_journal *journal;           /* cached journal info */
        unsigned char alloc_type;               /* current allocation type */
        unsigned int segno;                     /* current segment number */
        unsigned short next_blkoff;             /* next block offset to write */
        unsigned int zone;                      /* current zone number */
        unsigned int next_segno;                /* preallocated segment */
};

static int f2fs_xattr_generic_get(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, void *buffer, size_t size);

static int f2fs_xattr_generic_set(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, const void *value,
                size_t size, int flags);



static bool f2fs_xattr_trusted_list(struct dentry *dentry);


#define XATTR_TRUSTED_PREFIX "trusted."

struct export_operations {
        int (*encode_fh)(struct inode *inode, __u32 *fh, int *max_len,
                        struct inode *parent);
        struct dentry * (*fh_to_dentry)(struct super_block *sb, struct fid *fid,
                        int fh_len, int fh_type);
        struct dentry * (*fh_to_parent)(struct super_block *sb, struct fid *fid,
                        int fh_len, int fh_type);
        int (*get_name)(struct dentry *parent, char *name,
                        struct dentry *child);
        struct dentry * (*get_parent)(struct dentry *child);
        int (*commit_metadata)(struct inode *inode);

        int (*get_uuid)(struct super_block *sb, u8 *buf, u32 *len, u64 *offset);
        int (*map_blocks)(struct inode *inode, loff_t offset,
                          u64 len, struct iomap *iomap,
                          bool write, u32 *device_generation);
        int (*commit_blocks)(struct inode *inode, struct iomap *iomaps,
                             int nr_iomaps, struct iattr *iattr);
};



#define XATTR_USER_PREFIX "user."

#define F2FS_XATTR_INDEX_USER                   1

#define F2FS_SUPER_MAGIC 0xF2F52010

#define MS_POSIXACL (1<<16)

unsigned long long sectors[2];

static bool f2fs_xattr_user_list(struct dentry *dentry);

static struct dentry *f2fs_fh_to_dentry(struct super_block *sb, struct fid *fid,
                int fh_len, int fh_type);

static struct dentry *f2fs_fh_to_parent(struct super_block *sb, struct fid *fid,
                int fh_len, int fh_type);

struct dentry *f2fs_get_parent(struct dentry *child);



static const struct export_operations f2fs_export_ops = {
        .fh_to_dentry = f2fs_fh_to_dentry,
        .fh_to_parent = f2fs_fh_to_parent,
        .get_parent = f2fs_get_parent,
};



struct xattr_handler {
        const char *name;
        const char *prefix;
        int flags;      /* fs private flags */
        bool (*list)(struct dentry *dentry);
        int (*get)(const struct xattr_handler *, struct dentry *dentry,
                   struct inode *inode, const char *name, void *buffer,
                   size_t size);
        int (*set)(const struct xattr_handler *, struct dentry *dentry,
                   struct inode *inode, const char *name, const void *buffer,
                   size_t size, int flags);
};

static struct proc_dir_entry *f2fs_proc_root;

#define S_IRWXU 00700
#define S_IRUSR 00400
#define S_IWUSR 00200
#define S_IXUSR 00100

#define S_IRWXG 00070
#define S_IRGRP 00040
#define S_IWGRP 00020
#define S_IXGRP 00010

#define S_IRWXO 00007
#define S_IROTH 00004
#define S_IWOTH 00002
#define S_IXOTH 00001


#define S_IRUGO (S_IRUSR|S_IRGRP|S_IROTH)

#define NAT_JOURNAL_ENTRIES     ((SUM_JOURNAL_SIZE - 2) /\
                                sizeof(struct nat_journal_entry))

#define NAT_JOURNAL_RESERVED    ((SUM_JOURNAL_SIZE - 2) %\
                                sizeof(struct nat_journal_entry))

#define SIT_JOURNAL_ENTRIES     ((SUM_JOURNAL_SIZE - 2) /\
                                sizeof(struct sit_journal_entry))
#define SIT_JOURNAL_RESERVED    ((SUM_JOURNAL_SIZE - 2) %\
                                sizeof(struct sit_journal_entry))

/* Reserved area should make size of f2fs_extra_info equals to
 *  * that of nat_journal and sit_journal.
 *   */
#define EXTRA_INFO_RESERVED     (SUM_JOURNAL_SIZE - 2 - 8)

#define SIT_VBLOCK_MAP_SIZE 64

#define SIT_ENTRY_PER_BLOCK (PAGE_SIZE / sizeof(struct f2fs_sit_entry))

#define ENTRIES_IN_SUM          512
#define SUMMARY_SIZE            (7)     /* sizeof(struct summary) */
#define SUM_FOOTER_SIZE         (5)     /* sizeof(struct summary_footer) */
#define SUM_ENTRY_SIZE          (SUMMARY_SIZE * ENTRIES_IN_SUM)

#define F2FS_BLKSIZE                    4096    /* support only 4KB block */



#define SUM_JOURNAL_SIZE        (F2FS_BLKSIZE - SUM_FOOTER_SIZE -\
                                SUM_ENTRY_SIZE)



struct f2fs_sit_entry {
        __le16 vblocks;                         /* reference above */
        __u8 valid_map[SIT_VBLOCK_MAP_SIZE];    /* bitmap for valid blocks */
        __le64 mtime;                           /* segment age for cleaning */
} ;

struct f2fs_sit_block {
        struct f2fs_sit_entry entries[SIT_ENTRY_PER_BLOCK];
} ;




enum {
        NAT_JOURNAL = 0,
        SIT_JOURNAL
};

struct nat_journal_entry {
        __le32 nid;
        struct f2fs_nat_entry ne;
} ;

struct nat_journal {
        struct nat_journal_entry entries[NAT_JOURNAL_ENTRIES];
        __u8 reserved[NAT_JOURNAL_RESERVED];
} ;

struct sit_journal_entry {
        __le32 segno;
        struct f2fs_sit_entry se;
} ;

struct sit_journal {
        struct sit_journal_entry entries[SIT_JOURNAL_ENTRIES];
        __u8 reserved[SIT_JOURNAL_RESERVED];
} ;

struct f2fs_extra_info {
        __le64 kbytes_written;
        __u8 reserved[EXTRA_INFO_RESERVED];
} ;



struct f2fs_journal {
        union { 
                __le16 n_nats;
                __le16 n_sits;
        };
        /* spare area is used by NAT or SIT journals or extra info */
        union { 
                struct nat_journal nat_j;
                struct sit_journal sit_j;
                struct f2fs_extra_info info;
        };
};


static int f2fs_xattr_advise_get(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, void *buffer, size_t size);


static int f2fs_xattr_advise_set(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, const void *value,
                size_t size, int flags);


const struct xattr_handler f2fs_xattr_advise_handler = {
        .name   = F2FS_SYSTEM_ADVISE_NAME,
        .flags  = F2FS_XATTR_INDEX_ADVISE,
        .get    = f2fs_xattr_advise_get,
        .set    = f2fs_xattr_advise_set,
};

const struct xattr_handler f2fs_xattr_trusted_handler = {
        .prefix = XATTR_TRUSTED_PREFIX,
        .flags  = F2FS_XATTR_INDEX_TRUSTED,
        .list   = f2fs_xattr_trusted_list,
        .get    = f2fs_xattr_generic_get,
        .set    = f2fs_xattr_generic_set,
};


static int f2fs_xattr_generic_set(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, const void *value,
                size_t size, int flags);



static int f2fs_xattr_generic_get(const struct xattr_handler *handler,
                struct dentry *unused, struct inode *inode,
                const char *name, void *buffer, size_t size);


const struct xattr_handler f2fs_xattr_user_handler = {
        .prefix = XATTR_USER_PREFIX,
        .flags  = F2FS_XATTR_INDEX_USER,
        .list   = f2fs_xattr_user_list,
        .get    = f2fs_xattr_generic_get,
        .set    = f2fs_xattr_generic_set,
};


const struct xattr_handler *f2fs_xattr_handlers[] = {
        &f2fs_xattr_user_handler,
#ifdef CONFIG_F2FS_FS_POSIX_ACL
        &posix_acl_access_xattr_handler,
        &posix_acl_default_xattr_handler,
#endif
        &f2fs_xattr_trusted_handler,
#ifdef CONFIG_F2FS_FS_SECURITY
        &f2fs_xattr_security_handler,
#endif
        &f2fs_xattr_advise_handler,
        NULL,
};

static int parse_options(struct super_block *sb, char *options)
{
	struct f2fs_sb_info *sbi = F2FS_SB(sb);
	struct request_queue *q;
	substring_t args[MAX_OPT_ARGS];
	char *p, *name;
	int arg = 0;

	if (!options)
		return 0;

	while ((p = strsep(&options, ",")) != NULL) {
		int token;
		if (!*p)
			continue;
		///
		// Initialize args struct so we know whether arg was
		// found; some options take optional arguments.
		// 
		args[0].to = args[0].from = NULL;
		token = match_token(p, f2fs_tokens, args);

		switch (token) {
		case Opt_gc_background:
			name = match_strdup(&args[0]);

			if (!name)
				return -ENOMEM;
			if (strlen(name) == 2 && !strncmp(name, "on", 2)) {
				set_opt(sbi, BG_GC );
				clear_opt(sbi, FORCE_FG_GC);
			} else if (strlen(name) == 3 && !strncmp(name, "off", 3)) {
				clear_opt(sbi, BG_GC);
				clear_opt(sbi, FORCE_FG_GC);
			} else if (strlen(name) == 4 && !strncmp(name, "sync", 4)) {
				set_opt(sbi, BG_GC);
				set_opt(sbi, FORCE_FG_GC);
			} else {
				kfree(name);
				return -EINVAL;
			}
			kfree(name);
			break;
		case Opt_disable_roll_forward:
			set_opt(sbi, DISABLE_ROLL_FORWARD);
			break;
		case Opt_norecovery:
			// this option mounts f2fs with ro 
			set_opt(sbi, DISABLE_ROLL_FORWARD);
			if (!f2fs_readonly(sb))
				return -EINVAL;
			break;
		case Opt_discard:
			q = bdev_get_queue(sb->s_bdev);
			if (blk_queue_discard(q)) {
				set_opt(sbi, DISCARD);
			} else if (!f2fs_sb_mounted_blkzoned(sb)) {
				f2fs_msg(sb, KERN_WARNING,
					"mounting with \"discard\" option, but "
					"the device does not support discard");
			}
			break;
		case Opt_nodiscard:
			if (f2fs_sb_mounted_blkzoned(sb)) {
				f2fs_msg(sb, KERN_WARNING,
					"discard is required for zoned block devices");
				return -EINVAL;
			}
			clear_opt(sbi, DISCARD);
			break;
		case Opt_noheap:
			set_opt(sbi, NOHEAP);
			break;
		case Opt_heap:
			clear_opt(sbi, NOHEAP);
			break;
#ifdef CONFIG_F2FS_FS_XATTR
		case Opt_user_xattr:
			set_opt(sbi, XATTR_USER);
			break;
		case Opt_nouser_xattr:
			clear_opt(sbi, XATTR_USER);
			break;
		case Opt_inline_xattr:
			set_opt(sbi, INLINE_XATTR);
			break;
		case Opt_noinline_xattr:
			clear_opt(sbi, INLINE_XATTR);
			break;
#else
		case Opt_user_xattr:
			f2fs_msg(sb, KERN_INFO,
				"user_xattr options not supported");
			break;
		case Opt_nouser_xattr:
			f2fs_msg(sb, KERN_INFO,
				"nouser_xattr options not supported");
			break;
		case Opt_inline_xattr:
			f2fs_msg(sb, KERN_INFO,
				"inline_xattr options not supported");
			break;
		case Opt_noinline_xattr:
			f2fs_msg(sb, KERN_INFO,
				"noinline_xattr options not supported");
			break;
#endif
#ifdef CONFIG_F2FS_FS_POSIX_ACL
		case Opt_acl:
			set_opt(sbi, POSIX_ACL);
			break;
		case Opt_noacl:
			clear_opt(sbi, POSIX_ACL);
			break;
#else
		case Opt_acl:
			f2fs_msg(sb, KERN_INFO, "acl options not supported");
			break;
		case Opt_noacl:
			f2fs_msg(sb, KERN_INFO, "noacl options not supported");
			break;
#endif
		case Opt_active_logs:
			if (args->from && match_int(args, &arg))
				return -EINVAL;
			if (arg != 2 && arg != 4 && arg != NR_CURSEG_TYPE)
				return -EINVAL;
			sbi->active_logs = arg;
			break;
		case Opt_disable_ext_identify:
			set_opt(sbi, DISABLE_EXT_IDENTIFY);
			break;
		case Opt_inline_data:
			set_opt(sbi, INLINE_DATA);
			break;
		case Opt_inline_dentry:
			set_opt(sbi, INLINE_DENTRY);
			break;
		case Opt_noinline_dentry:
			clear_opt(sbi, INLINE_DENTRY);
			break;
		case Opt_flush_merge:
			set_opt(sbi, FLUSH_MERGE);
			break;
		case Opt_noflush_merge:
			clear_opt(sbi, FLUSH_MERGE);
			break;
		case Opt_nobarrier:
			set_opt(sbi, NOBARRIER);
			break;
		case Opt_fastboot:
			set_opt(sbi, FASTBOOT);
			break;
		case Opt_extent_cache:
			set_opt(sbi, EXTENT_CACHE);
			break;
		case Opt_noextent_cache:
			clear_opt(sbi, EXTENT_CACHE);
			break;
		case Opt_noinline_data:
			clear_opt(sbi, INLINE_DATA);
			break;
		case Opt_data_flush:
			set_opt(sbi, DATA_FLUSH);
			break;
		case Opt_mode:
			name = match_strdup(&args[0]);

			if (!name)
				return -ENOMEM;
			if (strlen(name) == 8 &&
					!strncmp(name, "adaptive", 8)) {
				if (f2fs_sb_mounted_blkzoned(sb)) {
					f2fs_msg(sb, KERN_WARNING,
						 "adaptive mode is not allowed with "
						 "zoned block device feature");
					kfree(name);
					return -EINVAL;
				}
				set_opt_mode(sbi, F2FS_MOUNT_ADAPTIVE);
			} else if (strlen(name) == 3 &&
					!strncmp(name, "lfs", 3)) {
				set_opt_mode(sbi, F2FS_MOUNT_LFS);
			} else {
				kfree(name);
				return -EINVAL;
			}
			kfree(name);
			break;
		case Opt_io_size_bits:
			if (args->from && match_int(args, &arg))
				return -EINVAL;
			if (arg > __ilog2_u32(BIO_MAX_PAGES)) {
				f2fs_msg(sb, KERN_WARNING,
					"Not support %d, larger than %d",
					1 << arg, BIO_MAX_PAGES);
				return -EINVAL;
			}
			sbi->write_io_size_bits = arg;
			break;
		case Opt_fault_injection:
			if (args->from && match_int(args, &arg))
				return -EINVAL;
#ifdef CONFIG_F2FS_FAULT_INJECTION
			f2fs_build_fault_attr(sbi, arg);
			set_opt(sbi, FAULT_INJECTION);
#else
			f2fs_msg(sb, KERN_INFO,
				"FAULT_INJECTION was not selected");
#endif
			break;
		case Opt_lazytime:
			sb->s_flags |= MS_LAZYTIME;
			break;
		case Opt_nolazytime:
			sb->s_flags &= ~MS_LAZYTIME;
			break;
		default:
			f2fs_msg(sb, KERN_ERR,
				"Unrecognized mount option \"%s\" or missing value",
				p);
			return -EINVAL;
		}
	}

	if (F2FS_IO_SIZE_BITS(sbi) && !test_opt(sbi, LFS)) {
		f2fs_msg(sb, KERN_ERR,
				"Should set mode=lfs with %uKB-sized IO",
				F2FS_IO_SIZE_KB(sbi));
		return -EINVAL;
	}
	return 0;
}


static void destroy_device_list(struct f2fs_sb_info *sbi)
{
	int i;

	for (i = 0; i < sbi->s_ndevs; i++) {
		blkdev_put(FDEV(i).bdev, FMODE_EXCL);
#ifdef CONFIG_BLK_DEV_ZONED
		kfree(FDEV(i).blkz_type);
#endif
	}
	kfree(sbi->devs);
}

static int segment_info_seq_show(struct seq_file *seq, void *offset)
{
	struct super_block *sb = seq->private;
	struct f2fs_sb_info *sbi = F2FS_SB(sb);
	unsigned int total_segs =
			le32_to_cpu(sbi->raw_super->segment_count_main);
	int i;

	seq_puts(seq, "format: segment_type|valid_blocks\n"
		"segment_type(0:HD, 1:WD, 2:CD, 3:HN, 4:WN, 5:CN)\n");

	for (i = 0; i < total_segs; i++) {
		struct seg_entry *se = get_seg_entry(sbi, i);

		if ((i % 10) == 0)
			seq_printf(seq, "%-10d", i);
		seq_printf(seq, "%d|%-3u", se->type,
					get_valid_blocks(sbi, i, false));
		if ((i % 10) == 9 || i == (total_segs - 1))
			seq_putc(seq, '\n');
		else
			seq_putc(seq, ' ');
	}

	return 0;
}

#define SIT_VBLOCK_MAP_SIZE 64

static int segment_bits_seq_show(struct seq_file *seq, void *offset)
{
	struct super_block *sb = seq->private;
	struct f2fs_sb_info *sbi = F2FS_SB(sb);
	unsigned int total_segs =
			le32_to_cpu(sbi->raw_super->segment_count_main);
	int i, j;

	seq_puts(seq, "format: segment_type|valid_blocks|bitmaps\n"
		"segment_type(0:HD, 1:WD, 2:CD, 3:HN, 4:WN, 5:CN)\n");

	for (i = 0; i < total_segs; i++) {
		struct seg_entry *se = get_seg_entry(sbi, i);

		seq_printf(seq, "%-10d", i);
		seq_printf(seq, "%d|%-3u|", se->type,
					get_valid_blocks(sbi, i, false));
		for (j = 0; j < SIT_VBLOCK_MAP_SIZE; j++)
			seq_printf(seq, " %.2x", se->cur_valid_map[j]);
		seq_putc(seq, '\n');
	}
	return 0;
}

int sanity_check_ckpt(struct f2fs_sb_info *sbi)
{
	unsigned int total, fsmeta;
	struct f2fs_super_block *raw_super = F2FS_RAW_SUPER(sbi);
	struct f2fs_checkpoint *ckpt = F2FS_CKPT(sbi);
	unsigned int ovp_segments, reserved_segments;
	unsigned int main_segs, blocks_per_seg;
	int i;

	total = le32_to_cpu(raw_super->segment_count);
	fsmeta = le32_to_cpu(raw_super->segment_count_ckpt);
	fsmeta += le32_to_cpu(raw_super->segment_count_sit);
	fsmeta += le32_to_cpu(raw_super->segment_count_nat);
	fsmeta += le32_to_cpu(ckpt->rsvd_segment_count);
	fsmeta += le32_to_cpu(raw_super->segment_count_ssa);

	if (unlikely(fsmeta >= total))
		return 1;

	ovp_segments = le32_to_cpu(ckpt->overprov_segment_count);
	reserved_segments = le32_to_cpu(ckpt->rsvd_segment_count);

	if (unlikely(fsmeta < F2FS_MIN_SEGMENTS ||
			ovp_segments == 0 || reserved_segments == 0)) {
		f2fs_msg(sbi->sb, KERN_ERR,
			"Wrong layout: check mkfs.f2fs version");
		return 1;
	}

	main_segs = le32_to_cpu(raw_super->segment_count_main);
	blocks_per_seg = sbi->blocks_per_seg;

	// XXX if condition can be shown as reachable only after 3 testcases.
	for (i = 0; i < NR_CURSEG_NODE_TYPE; i++) {
		if (le32_to_cpu(ckpt->cur_node_segno[i]) >= main_segs ||
			le16_to_cpu(ckpt->cur_node_blkoff[i]) >= blocks_per_seg)
			return 1;
	}
	// XXX if condition can be shown as reachable only after 3 testcases.
	for (i = 0; i < NR_CURSEG_DATA_TYPE; i++) {
		if (le32_to_cpu(ckpt->cur_data_segno[i]) >= main_segs ||
			le16_to_cpu(ckpt->cur_data_blkoff[i]) >= blocks_per_seg)
			return 1;
	}

	if (unlikely(f2fs_cp_error(sbi))) {
		f2fs_msg(sbi->sb, KERN_ERR, "A bug case: need to run fsck");
		return 1;
	}
	return 0;
}

static void init_sb_info(struct f2fs_sb_info *sbi)
{
	struct f2fs_super_block *raw_super = sbi->raw_super;
	int i;

	sbi->log_sectors_per_block =
		le32_to_cpu(raw_super->log_sectors_per_block);
	sbi->log_blocksize = le32_to_cpu(raw_super->log_blocksize);
	sbi->blocksize = 1 << sbi->log_blocksize;
	sbi->log_blocks_per_seg = le32_to_cpu(raw_super->log_blocks_per_seg);
	sbi->blocks_per_seg = 1 << sbi->log_blocks_per_seg;
	sbi->segs_per_sec = le32_to_cpu(raw_super->segs_per_sec);
	sbi->secs_per_zone = le32_to_cpu(raw_super->secs_per_zone);
	sbi->total_sections = le32_to_cpu(raw_super->section_count);
	sbi->total_node_count =
		(le32_to_cpu(raw_super->segment_count_nat) / 2)
			* sbi->blocks_per_seg * NAT_ENTRY_PER_BLOCK;
	sbi->root_ino_num = le32_to_cpu(raw_super->root_ino);
	sbi->node_ino_num = le32_to_cpu(raw_super->node_ino);
	sbi->meta_ino_num = le32_to_cpu(raw_super->meta_ino);
	sbi->cur_victim_sec = NULL_SECNO;
	sbi->max_victim_search = DEF_MAX_VICTIM_SEARCH;

	sbi->dir_level = DEF_DIR_LEVEL;
	sbi->interval_time[CP_TIME] = DEF_CP_INTERVAL;
	sbi->interval_time[REQ_TIME] = DEF_IDLE_INTERVAL;
	clear_sbi_flag(sbi, SBI_NEED_FSCK);

	for (i = 0; i < NR_COUNT_TYPE; i++)
		atomic_set(&sbi->nr_pages[i], 0);

	atomic_set(&sbi->wb_sync_req, 0);

	INIT_LIST_HEAD(&sbi->s_list);
	mutex_init(&sbi->umount_mutex);
	mutex_init(&sbi->wio_mutex[NODE]);
	mutex_init(&sbi->wio_mutex[DATA]);
	spin_lock_init(&sbi->cp_lock);
}

//#ifdef CONFIG_BLK_DEV_ZONED
static int init_blkz_info(struct f2fs_sb_info *sbi, int devi)
{
	struct block_device *bdev = FDEV(devi).bdev;
	sector_t nr_sectors = bdev->bd_part->nr_sects;
	sector_t sector = 0;
	struct blk_zone *zones;
	unsigned int i, nr_zones;
	unsigned int n = 0;
	int err = -EIO;

	if (!f2fs_sb_mounted_blkzoned(sbi->sb))
		return 0;

	if (sbi->blocks_per_blkz && sbi->blocks_per_blkz !=
				SECTOR_TO_BLOCK(bdev_zone_sectors(bdev)))
		return -EINVAL;
	sbi->blocks_per_blkz = SECTOR_TO_BLOCK(bdev_zone_sectors(bdev));
	if (sbi->log_blocks_per_blkz && sbi->log_blocks_per_blkz !=
				__ilog2_u32(sbi->blocks_per_blkz))
		return -EINVAL;
	sbi->log_blocks_per_blkz = __ilog2_u32(sbi->blocks_per_blkz);
	FDEV(devi).nr_blkz = SECTOR_TO_BLOCK(nr_sectors) >>
					sbi->log_blocks_per_blkz;
	if (nr_sectors & (bdev_zone_sectors(bdev) - 1))
		FDEV(devi).nr_blkz++;

	FDEV(devi).blkz_type = kmalloc(FDEV(devi).nr_blkz, GFP_KERNEL);
	if (!FDEV(devi).blkz_type)
		return -ENOMEM;

#define F2FS_REPORT_NR_ZONES   4096

	zones = kcalloc(F2FS_REPORT_NR_ZONES, sizeof(struct blk_zone),
			GFP_KERNEL);
	if (!zones)
		return -ENOMEM;

	// Get block zones type 
	// XXX LOOP CASE
	while (zones && sector < nr_sectors) {

		nr_zones = F2FS_REPORT_NR_ZONES;
		err = blkdev_report_zones(bdev, sector,
					  zones, &nr_zones,
					  GFP_KERNEL);
		if (err)
			break;
		if (!nr_zones) {
			err = -EIO;
			break;
		}

		for (i = 0; i < nr_zones; i++) {
			FDEV(devi).blkz_type[n] = zones[i].type;
			sector += zones[i].len;
			n++;
		}
	}

	kfree(zones);

	return err;
}

static int read_raw_super_block(struct f2fs_sb_info *sbi,
			struct f2fs_super_block **raw_super,
			int *valid_super_block, int *recovery)
{
	struct super_block *sb = sbi->sb;
	int block;
	struct buffer_head *bh;
	struct f2fs_super_block *super;
	int err = 0;

	super = kzalloc(sizeof(struct f2fs_super_block), GFP_KERNEL);
	if (!super)
		return -ENOMEM;

	for (block = 0; block < 2; block++) {
		bh = sb_bread(sb, block);
		if (!bh) {
			f2fs_msg(sb, KERN_ERR, "Unable to read %dth superblock",
				block + 1);
			err = -EIO;
			continue;
		}

		// sanity checking of raw super 
		if (sanity_check_raw_super(sbi, bh)) {
			f2fs_msg(sb, KERN_ERR,
				"Can't find valid F2FS filesystem in %dth superblock",
				block + 1);
			err = -EINVAL;
			brelse(bh);
			continue;
		}

		if (!*raw_super) {
			memcpy(super, bh->b_data + F2FS_SUPER_OFFSET,
							sizeof(*super));
			*valid_super_block = block;
			*raw_super = super;
		}
		brelse(bh);
	}

	// Fail to read any one of the superblocks
	if (err < 0)
		*recovery = 1;

	// No valid superblock 
	if (!*raw_super)
		kfree(super);
	else
		err = 0;

	return err;
}

static int f2fs_scan_devices(struct f2fs_sb_info *sbi)
{
	struct f2fs_super_block *raw_super = F2FS_RAW_SUPER(sbi);
	unsigned int max_devices = MAX_DEVICES;
	int i;

	// Initialize single device information 
	if (!RDEV(0).path[0]) {
		if (!bdev_is_zoned(sbi->sb->s_bdev))
			return 0;
		max_devices = 1;
	}

	//
	//  Initialize multiple devices information, or single
	//  zoned block device information.
	//
	sbi->devs = kcalloc(max_devices, sizeof(struct f2fs_dev_info),
				GFP_KERNEL);
	if (!sbi->devs)
		return -ENOMEM;

	// XXX 8 rounds. we can do it in only 1

	for (i = 0; i < max_devices; i++) {

		if (i > 0 && !RDEV(i).path[0])
			break;

		if (max_devices == 1) {
			// Single zoned block device mount 
			FDEV(0).bdev =
				blkdev_get_by_dev(sbi->sb->s_bdev->bd_dev,
					sbi->sb->s_mode, sbi->sb->s_type);
		} else {
			// Multi-device mount 
			memcpy(FDEV(i).path, RDEV(i).path, MAX_PATH_LEN);
			FDEV(i).total_segments =
				le32_to_cpu(RDEV(i).total_segments);
			if (i == 0) {
				FDEV(i).start_blk = 0;
				FDEV(i).end_blk = FDEV(i).start_blk +
				    (FDEV(i).total_segments <<
				    sbi->log_blocks_per_seg) - 1 +
				    le32_to_cpu(raw_super->segment0_blkaddr);
			} else {
				FDEV(i).start_blk = FDEV(i - 1).end_blk + 1;
				FDEV(i).end_blk = FDEV(i).start_blk +
					(FDEV(i).total_segments <<
					sbi->log_blocks_per_seg) - 1;
			}
			FDEV(i).bdev = blkdev_get_by_path(FDEV(i).path,
					sbi->sb->s_mode, sbi->sb->s_type);
		}
		if (IS_ERR(FDEV(i).bdev))
			return PTR_ERR(FDEV(i).bdev);

		// to release errored devices 
		sbi->s_ndevs = i + 1;

#ifdef CONFIG_BLK_DEV_ZONED
		if (bdev_zoned_model(FDEV(i).bdev) == BLK_ZONED_HM &&
				!f2fs_sb_mounted_blkzoned(sbi->sb)) {
			f2fs_msg(sbi->sb, KERN_ERR,
				"Zoned block device feature not enabled\n");
			return -EINVAL;
		}
		if (bdev_zoned_model(FDEV(i).bdev) != BLK_ZONED_NONE) {
			if (init_blkz_info(sbi, i)) {
				f2fs_msg(sbi->sb, KERN_ERR,
					"Failed to initialize F2FS blkzone information");
				return -EINVAL;
			}
			if (max_devices == 1)
				break;
			f2fs_msg(sbi->sb, KERN_INFO,
				"Mount Device [%2d]: %20s, %8u, %8x - %8x (zone: %s)",
				i, FDEV(i).path,
				FDEV(i).total_segments,
				FDEV(i).start_blk, FDEV(i).end_blk,
				bdev_zoned_model(FDEV(i).bdev) == BLK_ZONED_HA ?
				"Host-aware" : "Host-managed");
			continue;
		}
#endif
		f2fs_msg(sbi->sb, KERN_INFO,
			"Mount Device [%2d]: %20s, %8u, %8x - %8x",
				i, FDEV(i).path,
				FDEV(i).total_segments,
				FDEV(i).start_blk, FDEV(i).end_blk);
	}
	f2fs_msg(sbi->sb, KERN_INFO,
			"IO Block Size: %8d KB", F2FS_IO_SIZE_KB(sbi));
	return 0;
}

static int f2fs_fill_super(struct super_block *sb, void *data, int silent)
{
	struct f2fs_sb_info *sbi;
	struct f2fs_super_block *raw_super;
	struct inode *root;
	int err;
	bool retry = true, need_fsck = false;
	char *options = NULL;
	int recovery, i, valid_super_block;
	struct curseg_info *seg_i;

try_onemore:
	err = -EINVAL;
	raw_super = NULL;
	valid_super_block = -1;
	recovery = 0;

	//gc allocate memory for f2fs-specific super block info 
	sbi = kzalloc(sizeof(struct f2fs_sb_info), GFP_KERNEL);
	if (!sbi)
		return -ENOMEM;

	sbi->sb = sb;

	//gc Load the checksum driver 
	sbi->s_chksum_driver = crypto_alloc_shash("crc32", 0, 0);
	if (IS_ERR(sbi->s_chksum_driver)) {
		f2fs_msg(sb, KERN_ERR, "Cannot load crc32 driver.");
		err = PTR_ERR(sbi->s_chksum_driver);
		sbi->s_chksum_driver = NULL;
		goto free_sbi;
	}

	//gc set a block size 
	if (unlikely(!sb_set_blocksize(sb, F2FS_BLKSIZE))) {
		f2fs_msg(sb, KERN_ERR, "unable to set blocksize");
		goto free_sbi;
	}

	err = read_raw_super_block(sbi, &raw_super, &valid_super_block,
								&recovery);
	if (err)
		goto free_sbi;

	sb->s_fs_info = sbi;
	sbi->raw_super = raw_super;

	//gc
	// * The BLKZONED feature indicates that the drive was formatted with
	// * zone alignment optimization. This is optional for host-aware
	// * devices, but mandatory for host-managed zoned block devices.
	 
#ifndef CONFIG_BLK_DEV_ZONED
	if (f2fs_sb_mounted_blkzoned(sb)) {
		f2fs_msg(sb, KERN_ERR,
			 "Zoned block device support is not enabled\n");
		goto free_sb_buf;
	}
#endif
	default_options(sbi);
	//gc parse mount options 
	options = kstrdup((const char *)data, GFP_KERNEL);
	if (data && !options) {
		err = -ENOMEM;
		goto free_sb_buf;
	}

	err = parse_options(sb, options);
	if (err)
		goto free_options;

	sbi->max_file_blocks = max_file_blocks();
	sb->s_maxbytes = sbi->max_file_blocks <<
				le32_to_cpu(raw_super->log_blocksize);
	sb->s_max_links = F2FS_LINK_MAX;
	get_random_bytes(&sbi->s_next_generation, sizeof(u32));

	sb->s_op = &f2fs_sops;
	sb->s_cop = &f2fs_cryptops;
	sb->s_xattr = f2fs_xattr_handlers;
	sb->s_export_op = &f2fs_export_ops;
	sb->s_magic = F2FS_SUPER_MAGIC;
	sb->s_time_gran = 1;
	sb->s_flags = (sb->s_flags & ~MS_POSIXACL) |
		(test_opt(sbi, POSIX_ACL) ? MS_POSIXACL : 0);
	memcpy(sb->s_uuid, raw_super->uuid, sizeof(raw_super->uuid));

	//gc init f2fs-specific super block info 
	sbi->valid_super_block = valid_super_block;
	mutex_init(&sbi->gc_mutex);
	mutex_init(&sbi->cp_mutex);
	init_rwsem(&sbi->node_write);
	init_rwsem(&sbi->node_change);

	//gc disallow all the data/node/meta page writes 
	set_sbi_flag(sbi, SBI_POR_DOING);
	spin_lock_init(&sbi->stat_lock);

	init_rwsem(&sbi->read_io.io_rwsem);
	sbi->read_io.sbi = sbi;
	sbi->read_io.bio = NULL;
	for (i = 0; i < NR_PAGE_TYPE; i++) {
		init_rwsem(&sbi->write_io[i].io_rwsem);
		sbi->write_io[i].sbi = sbi;
		sbi->write_io[i].bio = NULL;
	}

	init_rwsem(&sbi->cp_rwsem);
	init_waitqueue_head(&sbi->cp_wait);
	init_sb_info(sbi);

	err = init_percpu_info(sbi);
	if (err)
		goto free_options;

	if (F2FS_IO_SIZE(sbi) > 1) {
		sbi->write_io_dummy =
			mempool_create_page_pool(2 * (F2FS_IO_SIZE(sbi) - 1), 0);
		if (!sbi->write_io_dummy)
			goto free_options;
	}

	//gc get an inode for meta space 
	sbi->meta_inode = f2fs_iget(sb, F2FS_META_INO(sbi));
	if (IS_ERR(sbi->meta_inode)) {
		f2fs_msg(sb, KERN_ERR, "Failed to read F2FS meta data inode");
		err = PTR_ERR(sbi->meta_inode);
		goto free_io_dummy;
	}

	err = get_valid_checkpoint(sbi);
	if (err) {
		f2fs_msg(sb, KERN_ERR, "Failed to get valid F2FS checkpoint");
		goto free_meta_inode;
	}

	//gc Initialize device list 
	err = f2fs_scan_devices(sbi);
	if (err) {
		f2fs_msg(sb, KERN_ERR, "Failed to find devices");
		goto free_devices;
	}

	sbi->total_valid_node_count =
				le32_to_cpu(sbi->ckpt->valid_node_count);
	percpu_counter_set(&sbi->total_valid_inode_count,
				le32_to_cpu(sbi->ckpt->valid_inode_count));
	sbi->user_block_count = le64_to_cpu(sbi->ckpt->user_block_count);
	sbi->total_valid_block_count =
				le64_to_cpu(sbi->ckpt->valid_block_count);
	sbi->last_valid_block_count = sbi->total_valid_block_count;

	for (i = 0; i < NR_INODE_TYPE; i++) {
		INIT_LIST_HEAD(&sbi->inode_list[i]);
		spin_lock_init(&sbi->inode_lock[i]);
	}

	init_extent_cache_info(sbi);

	init_ino_entry_info(sbi);

	//gc setup f2fs internal modules 
	err = build_segment_manager(sbi);
	if (err) {
		f2fs_msg(sb, KERN_ERR,
			"Failed to initialize F2FS segment manager");
		goto free_sm;
	}
	err = build_node_manager(sbi);
	if (err) {
		f2fs_msg(sb, KERN_ERR,
			"Failed to initialize F2FS node manager");
		goto free_nm;
	}

	//gc For write statistics 
	if (sb->s_bdev->bd_part)
		sbi->sectors_written_start =
			(u64)part_stat_read(sb->s_bdev->bd_part, sectors[1]);

	//gc Read accumulated write IO statistics if exists 
	seg_i = CURSEG_I(sbi, CURSEG_HOT_NODE);
	if (__exist_node_summaries(sbi))
		sbi->kbytes_written =
			le64_to_cpu(seg_i->journal->info.kbytes_written);

	build_gc_manager(sbi);

	// get an inode for node space //
	sbi->node_inode = f2fs_iget(sb, F2FS_NODE_INO(sbi));
	if (IS_ERR(sbi->node_inode)) {
		f2fs_msg(sb, KERN_ERR, "Failed to read node inode");
		err = PTR_ERR(sbi->node_inode);
		goto free_nm;
	}

	f2fs_join_shrinker(sbi);

	err = f2fs_build_stats(sbi);
	if (err)
		goto free_nm;

	// if there are nt orphan nodes free them //
	err = recover_orphan_inodes(sbi);
	if (err)
		goto free_node_inode;

	//gc read root inode and dentry 
	root = f2fs_iget(sb, F2FS_ROOT_INO(sbi));
	if (IS_ERR(root)) {
		f2fs_msg(sb, KERN_ERR, "Failed to read root inode");
		err = PTR_ERR(root);
		goto free_node_inode;
	}
	if (!S_ISDIR(root->i_mode) || !root->i_blocks || !root->i_size) {
		iput(root);
		err = -EINVAL;
		goto free_node_inode;
	}

	sb->s_root = d_make_root(root); // allocate root dentry 
	if (!sb->s_root) {
		err = -ENOMEM;
		goto free_root_inode;
	}

	if (f2fs_proc_root)
		sbi->s_proc = proc_mkdir(sb->s_id, f2fs_proc_root);
/*
	if (sbi->s_proc) {
		proc_create_data("segment_info", S_IRUGO, sbi->s_proc,
				 &f2fs_seq_segment_info_fops, sb);
		proc_create_data("segment_bits", S_IRUGO, sbi->s_proc,
				 &f2fs_seq_segment_bits_fops, sb);
	}
*/
	sbi->s_kobj.kset = f2fs_kset;
	init_completion(&sbi->s_kobj_unregister);
	//err = kobject_init_and_add(&sbi->s_kobj, &f2fs_ktype, NULL,
		//					"%s", sb->s_id);
	if (err)
		goto free_proc;

	// recover fsynced data
	if (!test_opt(sbi, DISABLE_ROLL_FORWARD)) {
		///
		//  mount should be failed, when device has readonly mode, and
		//  previous checkpoint was not done by clean system shutdown.
		// /
		if (bdev_read_only(sb->s_bdev) &&
				!is_set_ckpt_flags(sbi, CP_UMOUNT_FLAG)) {
			err = -EROFS;
			goto free_kobj;
		}

		if (need_fsck)
			set_sbi_flag(sbi, SBI_NEED_FSCK);

		if (!retry)
			goto skip_recovery;

		err = recover_fsync_data(sbi, false);
		if (err < 0) {
			need_fsck = true;
			f2fs_msg(sb, KERN_ERR,
				"Cannot recover all fsync data errno=%d", err);
			goto free_kobj;
		}
	} else {
		err = recover_fsync_data(sbi, true);

		if (!f2fs_readonly(sb) && err > 0) {
			err = -EINVAL;
			f2fs_msg(sb, KERN_ERR,
				"Need to recover fsync data");
			goto free_kobj;
		}
	}
skip_recovery:
	// recover_fsync_data() cleared this already 
	clear_sbi_flag(sbi, SBI_POR_DOING);

	///
	//  If filesystem is not mounted as read-only then
	//  do start the gc_thread.
	// /
	if (test_opt(sbi, BG_GC) && !f2fs_readonly(sb)) {
		// After POR, we can run background GC thread.
		err = start_gc_thread(sbi);
		if (err)
			goto free_kobj;
	}
	kfree(options);

	// recover broken superblock
	if (recovery) {
		err = f2fs_commit_super(sbi, true);
		f2fs_msg(sb, KERN_INFO,
			"Try to recover %dth superblock, ret: %d",
			sbi->valid_super_block ? 1 : 2, err);
	}

	f2fs_msg(sbi->sb, KERN_NOTICE, "Mounted with checkpoint version = %llx",
				cur_cp_version(F2FS_CKPT(sbi)));
	f2fs_update_time(sbi, CP_TIME);
	f2fs_update_time(sbi, REQ_TIME);
	return 0;

free_kobj:
	f2fs_sync_inode_meta(sbi);
	kobject_del(&sbi->s_kobj);
	kobject_put(&sbi->s_kobj);
	wait_for_completion(&sbi->s_kobj_unregister);
free_proc:
	if (sbi->s_proc) {
		remove_proc_entry("segment_info", sbi->s_proc);
		remove_proc_entry("segment_bits", sbi->s_proc);
		remove_proc_entry(sb->s_id, f2fs_proc_root);
	}
free_root_inode:
	dput(sb->s_root);
	sb->s_root = NULL;
free_node_inode:
	truncate_inode_pages_final(NODE_MAPPING(sbi));
	mutex_lock(&sbi->umount_mutex);
	release_ino_entry(sbi, true);
	f2fs_leave_shrinker(sbi);
	///
	//  Some dirty meta pages can be produced by recover_orphan_inodes()
	//  failed by EIO. Then, iput(node_inode) can trigger balance_fs_bg()
	//  followed by write_checkpoint() through f2fs_write_node_pages(), which
	//  falls into an infinite loop in sync_meta_pages().
	// /
	truncate_inode_pages_final(META_MAPPING(sbi));
	iput(sbi->node_inode);
	mutex_unlock(&sbi->umount_mutex);
	f2fs_destroy_stats(sbi);
free_nm:
	destroy_node_manager(sbi);
free_sm:
	destroy_segment_manager(sbi);
free_devices:
	destroy_device_list(sbi);
	kfree(sbi->ckpt);
free_meta_inode:
	make_bad_inode(sbi->meta_inode);
	iput(sbi->meta_inode);
free_io_dummy:
	mempool_destroy(sbi->write_io_dummy);
free_options:
	destroy_percpu_info(sbi);
	kfree(options);
free_sb_buf:
	kfree(raw_super);
free_sbi:
	if (sbi->s_chksum_driver)
		crypto_free_shash(sbi->s_chksum_driver);
	kfree(sbi);

	// give only one another chance 
	if (retry) {
		retry = false;
		shrink_dcache_sb(sb);
		goto try_onemore;
	}
	return err;
}
