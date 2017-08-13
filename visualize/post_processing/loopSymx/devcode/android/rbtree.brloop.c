#include<stdio.h>
#include<stdbool.h>
#include<unistd.h>
#include<stdint.h>

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

#define _IOC_NRBITS     8
#define _IOC_TYPEBITS   8
#define _IOC_SIZEBITS   13
#define _IOC_DIRBITS    3

#define _IOC_NRMASK     ((1 << _IOC_NRBITS)-1)
#define _IOC_TYPEMASK   ((1 << _IOC_TYPEBITS)-1)
#define _IOC_SIZEMASK   ((1 << _IOC_SIZEBITS)-1)
#define _IOC_DIRMASK    ((1 << _IOC_DIRBITS)-1)

#define _IOC_NRSHIFT    0
#define _IOC_TYPESHIFT  (_IOC_NRSHIFT+_IOC_NRBITS)
#define _IOC_SIZESHIFT  (_IOC_TYPESHIFT+_IOC_TYPEBITS)
#define _IOC_DIRSHIFT   (_IOC_SIZESHIFT+_IOC_SIZEBITS)

/*
 *  * Direction bits _IOC_NONE could be 0, but OSF/1 gives it a bit.
 *   * And this turns out useful to catch old ioctl numbers in header
 *    * files for us.
 *     */
#define _IOC_NONE       1U 
#define _IOC_READ       2U
#define _IOC_WRITE      4U

#define _IOC(dir,type,nr,size)                  \
        ((unsigned int)                         \
         (((dir)  << _IOC_DIRSHIFT) |           \
          ((type) << _IOC_TYPESHIFT) |          \
          ((nr)   << _IOC_NRSHIFT) |            \
          ((size) << _IOC_SIZESHIFT)))

/* used to create numbers */
#define _IO(type,nr)            _IOC(_IOC_NONE,(type),(nr),0)
#define _IOR(type,nr,size)      _IOC(_IOC_READ,(type),(nr),sizeof(size))
#define _IOW(type,nr,size)      _IOC(_IOC_WRITE,(type),(nr),sizeof(size))
#define _IOWR(type,nr,size)     _IOC(_IOC_READ|_IOC_WRITE,(type),(nr),sizeof(size))

/* used to decode them.. */
#define _IOC_DIR(nr)            (((nr) >> _IOC_DIRSHIFT) & _IOC_DIRMASK)
#define _IOC_TYPE(nr)           (((nr) >> _IOC_TYPESHIFT) & _IOC_TYPEMASK)
#define _IOC_NR(nr)             (((nr) >> _IOC_NRSHIFT) & _IOC_NRMASK)

#define BR_FAILED_REPLY 17
#define BC_REPLY_SG 18

#ifndef container_of
#define container_of(ptr, type, member) \
    (type *)((char *)(ptr) - (char *) &((type *)0)->member)
#endif

#define rb_entry(ptr, type, member) container_of(ptr, type, member)

enum binder_stat_types {
        BINDER_STAT_PROC,
        BINDER_STAT_THREAD,
        BINDER_STAT_NODE,
        BINDER_STAT_REF,
        BINDER_STAT_DEATH,
        BINDER_STAT_TRANSACTION,
        BINDER_STAT_TRANSACTION_COMPLETE,
        BINDER_STAT_COUNT
};

struct binder_stats {
        int br[_IOC_NR(BR_FAILED_REPLY) + 1];
        int bc[_IOC_NR(BC_REPLY_SG) + 1];
        int obj_created[BINDER_STAT_COUNT];
        int obj_deleted[BINDER_STAT_COUNT];
};

struct list_head {
    struct list_head *next, *prev;
};

struct __wait_queue_head {
        spinlock_t              lock;
        struct list_head        task_list;
};
typedef struct __wait_queue_head wait_queue_head_t;


struct rb_node {
        unsigned long  __rb_parent_color;
        struct rb_node *rb_right;
        struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
    /* The alignment might seem pointless, but allegedly CRIS needs it */

struct rb_root {
        struct rb_node *rb_node;
};

struct hlist_node {
        struct hlist_node *next, **pprev;
};

struct binder_proc {
        struct hlist_node proc_node;
        struct rb_root threads;
        struct rb_root nodes;
        struct rb_root refs_by_desc;
        struct rb_root refs_by_node;
        int pid;
        struct vm_area_struct *vma;
        struct mm_struct *vma_vm_mm;
        struct task_struct *tsk;
        struct files_struct *files;
        struct hlist_node deferred_work_node;
        int deferred_work;
        void *buffer;
        int user_buffer_offset;

        struct list_head buffers;
        struct rb_root free_buffers;
        struct rb_root allocated_buffers;
        size_t free_async_space;

        struct page **pages;
        size_t buffer_size;
        uint32_t buffer_free;
        struct list_head todo;
        wait_queue_head_t wait;
        struct binder_stats stats;
        struct list_head delivered_death;
        int max_threads;
        int requested_threads;
        int requested_threads_started;
        int ready_threads;
        long default_priority;
        struct dentry *debugfs_entry;
        struct binder_context *context;
};

#define PAGE_SHIFT      13
#define PAGE_SIZE       (1 << PAGE_SHIFT)
#define PAGE_MASK       (~(PAGE_SIZE-1))

struct binder_buffer {
        struct list_head entry; /* free and allocated entries by address */
        struct rb_node rb_node; /* free entry by size or allocated entry */
                                /* by address */
        unsigned free:1;
        unsigned allow_user_free:1;
        unsigned async_transaction:1;
        unsigned debug_id:29;

//        struct binder_transaction *transaction;

        struct binder_node *target_node;
        size_t data_size;
        size_t offsets_size;
        size_t extra_buffers_size;
        uint8_t data[0];
};

struct binder_work {
        struct list_head entry;
        enum {  
                BINDER_WORK_TRANSACTION = 1,
                BINDER_WORK_TRANSACTION_COMPLETE,
                BINDER_WORK_NODE,
                BINDER_WORK_DEAD_BINDER,
                BINDER_WORK_DEAD_BINDER_AND_CLEAR,
                BINDER_WORK_CLEAR_DEATH_NOTIFICATION,
        } type;
};

typedef uint32_t binder_uintptr_t;

struct binder_ref_death {
        struct binder_work work;
        binder_uintptr_t cookie;
};

struct binder_ref {
        /* Lookups needed: */
        /*   node + proc => ref (transaction) */
        /*   desc + proc => ref (transaction, inc/dec ref) */
        /*   node => refs + procs (proc exit) */
        int debug_id;
        struct rb_node rb_node_desc;
        struct rb_node rb_node_node;
        struct hlist_node node_entry;
        struct binder_proc *proc;
        struct binder_node *node;
        uint32_t desc;
        int strong;
        int weak;
        struct binder_ref_death *death;
};



struct binder_context {
        struct binder_node *binder_context_mgr_node;
//        kuid_t binder_context_mgr_uid;
  //      const char *name;
};



extern struct rb_node *rb_first(const struct rb_root *);
struct rb_node *rb_next(const struct rb_node *node);

struct binder_ref *binder_get_ref_for_node(struct binder_proc *proc,
						  struct binder_node *node)
{
	struct rb_node *n;
	struct rb_node **p = &proc->refs_by_node.rb_node;
	struct rb_node *parent = NULL;
	struct binder_ref *ref, *new_ref;
	struct binder_context *context = proc->context;

        new_ref->desc = (node == context->binder_context_mgr_node) ? 0 : 1;
	for (n = rb_first(&proc->refs_by_desc); n != NULL; n = rb_next(n)) {
		ref = rb_entry(n, struct binder_ref, rb_node_desc);
		if (ref->desc > new_ref->desc){
		// found a reference descriptor that is not immediately
		// greater than the previous descriptor. 
		// i.e. 1,1,*,3
			break;
		}
		new_ref->desc = ref->desc + 1;
	}

	// TEST 0 : [2] , 1 if-> break.
	// TEST 1 : [1] , 1 if -> loop -> if -> break.

	/*
	p = &proc->refs_by_desc.rb_node;
	
	while (*p) {
		parent = *p;
		ref = rb_entry(parent, struct binder_ref, rb_node_desc);

		if (new_ref->desc < ref->desc)
			p = &(*p)->rb_left;
		else if (new_ref->desc > ref->desc)
			p = &(*p)->rb_right;
		else	// two reference descriptors found
			BUG();
	}
	*/
	return new_ref;	
}
