#include<stdint.h>
#include <stdbool.h>

#define __le32 uint32_t

#define DEF_ADDRS_PER_INODE     923     /* Address Pointers in an Inode */

#define F2FS_INLINE_XATTR_ADDRS 50      /* 200 bytes for inline xattrs */

#define MAX_INLINE_DATA         (sizeof(__le32) * (DEF_ADDRS_PER_INODE - \
                                                F2FS_INLINE_XATTR_ADDRS - 1))

/* used for f2fs_inode_info->flags */
enum {  
        FI_NEW_INODE,           /* indicate newly allocated inode */
        FI_DIRTY_INODE,         /* indicate inode is dirty or not */
        FI_AUTO_RECOVER,        /* indicate inode is recoverable */
        FI_DIRTY_DIR,           /* indicate directory has dirty pages */
        FI_INC_LINK,            /* need to increment i_nlink */
        FI_ACL_MODE,            /* indicate acl mode */
        FI_NO_ALLOC,            /* should not allocate any blocks */
        FI_FREE_NID,            /* free allocated nide */
        FI_NO_EXTENT,           /* not to use the extent cache */
        FI_INLINE_XATTR,        /* used for inline xattr */
        FI_INLINE_DATA,         /* used for inline data*/
        FI_INLINE_DENTRY,       /* used for inline dentry */
        FI_APPEND_WRITE,        /* inode has appended data */
        FI_UPDATE_WRITE,        /* inode has in-place-update data */
        FI_NEED_IPU,            /* used for ipu per file */
        FI_ATOMIC_FILE,         /* indicate atomic file */
        FI_ATOMIC_COMMIT,       /* indicate the state of atomical committing */
        FI_VOLATILE_FILE,       /* indicate volatile file */
        FI_FIRST_BLOCK_WRITTEN, /* indicate #0 data block was written */
        FI_DROP_CACHE,          /* drop dirty page cache */
        FI_DATA_EXIST,          /* indicate data exists */
        FI_INLINE_DOTS,         /* indicate inline dot dentries */
        FI_DO_DEFRAG,           /* indicate defragment is running */
        FI_DIRTY_FILE,          /* indicate regular/symlink has dirty pages */
        FI_NO_PREALLOC,         /* indicate skipped preallocated blocks */
        FI_HOT_DATA,            /* indicate file is hot */
};

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



static void __recover_inline_status(struct inode *inode, struct page *ipage)
{
	void *inline_data = inline_data_addr(ipage);
	__le32 *start = inline_data;
	__le32 *end = start + MAX_INLINE_DATA / sizeof(__le32);

	while (start < end) {
		if (*start++) {
			f2fs_wait_on_page_writeback(ipage, NODE, true);

			set_inode_flag(inode, FI_DATA_EXIST);
			set_raw_inline(inode, F2FS_INODE(ipage));
			set_page_dirty(ipage);
			return;
		}
	}
	return;
}
