#include<sys/types.h>

#include<stddef.h>

#include<stdint.h>

#define EINVAL 10
#define ENOMEM 11
#define __GFP_BITS_SHIFT 26
#define __GFP_BITS_MASK ((gfp_t)((1 << __GFP_BITS_SHIFT) - 1))

#define __GFP_HIGH              0x20u
#define __GFP_IO                0x40u
#define __GFP_FS                0x80u
#define __GFP_NOWARN            0x200u
#define __GFP_ATOMIC            0x80000u
#define __GFP_ACCOUNT           0x100000u
#define __GFP_DIRECT_RECLAIM    0x400000u
#define __GFP_KSWAPD_RECLAIM    0x2000000u

#define __GFP_RECLAIM   (__GFP_DIRECT_RECLAIM|__GFP_KSWAPD_RECLAIM)

#define GFP_ATOMIC      (__GFP_HIGH|__GFP_ATOMIC|__GFP_KSWAPD_RECLAIM)
#define GFP_KERNEL      (__GFP_RECLAIM | __GFP_IO | __GFP_FS)
#define GFP_NOWAIT      (__GFP_KSWAPD_RECLAIM)




#define GFP_NOFS        10//(__GFP_RECLAIM | __GFP_IO)
#define __GFP_REPEAT    ((__force gfp_t)___GFP_REPEAT)
#define __GFP_NOFAIL    ((__force gfp_t)___GFP_NOFAIL)
#define __GFP_NORETRY   ((__force gfp_t)___GFP_NORETRY)

#define cpu_to_le32(val) (val)
#define EXT4_ACL_VERSION        0x0001

typedef struct {
        uint16_t          e_tag;
        uint16_t         e_perm;
        uint32_t         e_id;
} ext4_acl_entry;

typedef struct {
        uint16_t          e_tag;
        uint16_t         e_perm;
} ext4_acl_entry_short;

typedef struct {
        uid_t val;
} kuid_t;

typedef struct {
        gid_t val;
} kgid_t;

typedef struct {
        int counter;
} atomic_t;



struct posix_acl_entry {
        short                   e_tag;
        unsigned short          e_perm;
        union { 
                kuid_t          e_uid;
                kgid_t          e_gid;
        };
};

extern kgid_t make_kgid(struct user_namespace *from, gid_t gid);

/* e_tag entry in struct posix_acl_entry */
#define ACL_USER_OBJ            (0x01)
#define ACL_USER                (0x02)
#define ACL_GROUP_OBJ           (0x04)
#define ACL_GROUP               (0x08)
#define ACL_MASK                (0x10)
#define ACL_OTHER               (0x20)

#define ATOMIC_INIT(i) { (i) }
#define GLOBAL_ROOT_UID KUIDT_INIT(0)
#define GLOBAL_ROOT_GID KUIDT_INIT(0)
#define KUIDT_INIT(value) (kuid_t){ value }

#define UID_GID_MAP_MAX_EXTENTS 5

struct proc_ns_operations;

typedef atomic_t atomic_long_t;

struct list_head {
    struct list_head *next, *prev;
};


typedef struct {
        uint64_t counter;
} atomic64_t;

struct work_struct;

#define UCOUNT_COUNTS 10

typedef void (*work_func_t)(struct work_struct *work);

struct work_struct {
        atomic_long_t data;
        struct list_head entry;
        work_func_t func;
#ifdef CONFIG_LOCKDEP
        struct lockdep_map lockdep_map;
#endif
};


struct ns_common {
        atomic_long_t stashed;
        const struct proc_ns_operations *ops;
        unsigned int inum;
};


struct uid_gid_map {    /* 64 bytes -- 1 cache line */
        uint32_t nr_extents;
        struct uid_gid_extent {
                uint32_t first;
                uint32_t lower_first;
                uint32_t count;
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


#define PROC_USER_INIT_INO 0xEFFFFFFDU



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
        .group = 10,
        .ns.inum = PROC_USER_INIT_INO,
#ifdef CONFIG_USER_NS
        .ns.ops = &userns_operations,
#endif
        .flags = 1UL,
#ifdef CONFIG_PERSISTENT_KEYRINGS
        .persistent_keyring_register_sem =
        __RWSEM_INITIALIZER(init_user_ns.persistent_keyring_register_sem),
#endif
};



struct callback_head {
        struct callback_head *next;
        void (*func)(struct callback_head *head);
} __attribute__((aligned(sizeof(void *))));
#define rcu_head callback_head



struct posix_acl {
        atomic_t                a_refcount;
        struct rcu_head         a_rcu;
        unsigned int            a_count;
        struct posix_acl_entry  a_entries[0];
};



/* alterations done - only adding structure definitions, not the entire header.
 * changing ERR_PTR function call
 * */
/*
static posix_aclstruct {
        __le32          a_version;
} posix_aclext4_acl_header;
*/

typedef struct {
        uint32_t          a_version;
} ext4_acl_header;


int ext4_acl_from_disk(const void *value, size_t size)
{
	const char *end = (char *)value + size;
	int n, count;
	struct posix_acl *acl;

	if (!value)
		return 0;
	if (size < sizeof(ext4_acl_header))
		 return -EINVAL;
	if (((ext4_acl_header *)value)->a_version !=
	    cpu_to_le32(EXT4_ACL_VERSION))
		return -EINVAL;
	value = (char *)value + sizeof(ext4_acl_header);
	count = ext4_acl_count(size);
	if (count < 0)
		return -EINVAL;
	if (count == 0)
		return 0;
	acl = posix_acl_alloc(count, GFP_NOFS);
	if (!acl)
		return -ENOMEM;
	for (n = 0; n < count; n++) {
		ext4_acl_entry *entry =
			(ext4_acl_entry *)value;
		if ((char *)value + sizeof(ext4_acl_entry_short) > end)
			goto fail;
		acl->a_entries[n].e_tag  = le16_to_cpu(entry->e_tag);
		acl->a_entries[n].e_perm = le16_to_cpu(entry->e_perm);

		switch (acl->a_entries[n].e_tag) {
		case ACL_USER_OBJ:
		case ACL_GROUP_OBJ:
		case ACL_MASK:
		case ACL_OTHER:
			value = (char *)value +
				sizeof(ext4_acl_entry_short);
			break;

		case ACL_USER:
			value = (char *)value + sizeof(ext4_acl_entry);
			if ((char *)value > end)
				goto fail;
			//acl->a_entries[n].e_uid =
			//	make_kuid(&init_user_ns,
			//		  le32_to_cpu(entry->e_id));
			break;
		case ACL_GROUP:
			value = (char *)value + sizeof(ext4_acl_entry);
			if ((char *)value > end)
				goto fail;
			acl->a_entries[n].e_gid =
				make_kgid(&init_user_ns,
					  le32_to_cpu(entry->e_id));
			break;

		default:
			goto fail;
		}
	}
	if (value != end)
		goto fail;
	return acl;

fail:
	posix_acl_release(acl);
	return -EINVAL;
}

int
ext4_acl_to_disk(const struct posix_acl *acl, size_t *size)
{
        ext4_acl_header *ext_acl;
        char *e;
        size_t n;

        *size = ext4_acl_size(acl->a_count);
        ext_acl = kmalloc(sizeof(ext4_acl_header) + acl->a_count *
                        sizeof(ext4_acl_entry), GFP_NOFS);
        if (!ext_acl)
                return -ENOMEM;
        ext_acl->a_version = cpu_to_le32(EXT4_ACL_VERSION);
        e = (char *)ext_acl + sizeof(ext4_acl_header);
        for (n = 0; n < acl->a_count; n++) {
                const struct posix_acl_entry *acl_e = &acl->a_entries[n];
                ext4_acl_entry *entry = (ext4_acl_entry *)e;
                entry->e_tag  = cpu_to_le16(acl_e->e_tag);
                entry->e_perm = cpu_to_le16(acl_e->e_perm);
                switch (acl_e->e_tag) {
                case ACL_USER:
                        entry->e_id = cpu_to_le32(
                                from_kuid(&init_user_ns, acl_e->e_uid));
                        e += sizeof(ext4_acl_entry);
                        break;
                case ACL_GROUP:
                        entry->e_id = cpu_to_le32(
                                from_kgid(&init_user_ns, acl_e->e_gid));
                        e += sizeof(ext4_acl_entry);
                        break;

                case ACL_USER_OBJ:
                case ACL_GROUP_OBJ:
                case ACL_MASK:
                case ACL_OTHER:
                        e += sizeof(ext4_acl_entry_short);
                        break;

                default:
                        goto fail;
                }
        }
        return (char *)ext_acl;

fail:   
        kfree(ext_acl);
        return -EINVAL;
}
