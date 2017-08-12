//#include "header.h"

#ifndef __kernel_pid_t
typedef int             __kernel_pid_t;
#endif

typedef __kernel_pid_t          pid_t;

#define PIDVEC_SIZE     128

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



static spinlock_t pids_lock;

unsigned long *pids;

void f2fs_destroy_trace_ios(void)
{
	pid_t pid[PIDVEC_SIZE];
	pid_t next_pid = 0;
	unsigned int found;

	spin_lock(&pids_lock);
	while ((found = gang_lookup_pids(pid, next_pid, PIDVEC_SIZE))) {
		unsigned idx;

		next_pid = pid[found - 1] + 1;
		for (idx = 0; idx < found; idx++)
			radix_tree_delete(&pids, pid[idx]);
	}
	spin_unlock(&pids_lock);
}
