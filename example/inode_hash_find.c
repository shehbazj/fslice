
#define hlist_for_each_entry(tpos, pos, head, member)                    \
        for (pos = (head)->first;                                        \
             pos &&                                                      \
                ({ tpos = hlist_entry(pos, typeof(*tpos), member); 1;}); \
             pos = pos->next)

struct super_block {
        struct dsuper_block sb;
        FILE *dev;
        struct bitmap *inode_freemap;
        struct bitmap *block_freemap;
        tx_type tx_in_progress;

        // TODO: add your code here
                int *csum_table;
                };
        
        


static struct inode *
inode_hash_find(struct super_block *sb, int inode_nr) {
        struct hlist_node *elem;
        struct inode *in;

        hlist_for_each_entry(in, elem,
                        &inode_hash_table[inode_hashfn(inode_nr)], hnode)
        {
                if ((in->sb == sb) && (in->i_nr == inode_nr)) {
                        return in;
                }
        }
        return NULL;
}

