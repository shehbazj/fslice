static struct btrfs_delayed_ref_head *htree_insert(struct rb_root *root,
						   struct rb_node *node)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent_node = NULL;
	struct btrfs_delayed_ref_head *entry;
	struct btrfs_delayed_ref_head *ins;
	u64 bytenr;

	ins = rb_entry(node, struct btrfs_delayed_ref_head, href_node);
	bytenr = ins->node.bytenr;
	while (*p) {
		parent_node = *p;
		entry = rb_entry(parent_node, struct btrfs_delayed_ref_head,
				 href_node);

		if (bytenr < entry->node.bytenr)
			p = &(*p)->rb_left;
		else if (bytenr > entry->node.bytenr)
			p = &(*p)->rb_right;
		else
			return entry;
	}

	rb_link_node(node, parent_node, p);
	rb_insert_color(node, root);
	return NULL;
}
find_ref_head(struct rb_root *root, u64 bytenr,
	      int return_bigger)
{
	struct rb_node *n;
	struct btrfs_delayed_ref_head *entry;

	n = root->rb_node;
	entry = NULL;
	while (n) {
		entry = rb_entry(n, struct btrfs_delayed_ref_head, href_node);

		if (bytenr < entry->node.bytenr)
			n = n->rb_left;
		else if (bytenr > entry->node.bytenr)
			n = n->rb_right;
		else
			return entry;
	}
	if (entry && return_bigger) {
		if (bytenr > entry->node.bytenr) {
			n = rb_next(&entry->href_node);
			if (!n)
				n = rb_first(root);
			entry = rb_entry(n, struct btrfs_delayed_ref_head,
					 href_node);
			return entry;
		}
		return entry;
	}
	return NULL;
}
		      struct btrfs_delayed_ref_node *ref,
		      u64 seq)
{
	struct btrfs_delayed_ref_node *next;
	bool done = false;

	next = list_first_entry(&head->ref_list, struct btrfs_delayed_ref_node,
				list);
	while (!done && &next->list != &head->ref_list) {
		int mod;
		struct btrfs_delayed_ref_node *next2;

		next2 = list_next_entry(next, list);

		if (next == ref)
			goto next;

		if (seq && next->seq >= seq)
			goto next;

		if (next->type != ref->type)
			goto next;

		if ((ref->type == BTRFS_TREE_BLOCK_REF_KEY ||
		     ref->type == BTRFS_SHARED_BLOCK_REF_KEY) &&
		    comp_tree_refs(btrfs_delayed_node_to_tree_ref(ref),
				   btrfs_delayed_node_to_tree_ref(next),
				   ref->type))
			goto next;
		if ((ref->type == BTRFS_EXTENT_DATA_REF_KEY ||
		     ref->type == BTRFS_SHARED_DATA_REF_KEY) &&
		    comp_data_refs(btrfs_delayed_node_to_data_ref(ref),
				   btrfs_delayed_node_to_data_ref(next)))
			goto next;

		if (ref->action == next->action) {
			mod = next->ref_mod;
		} else {
			if (ref->ref_mod < next->ref_mod) {
				swap(ref, next);
				done = true;
			}
			mod = -next->ref_mod;
		}

		drop_delayed_ref(trans, delayed_refs, head, next);
		ref->ref_mod += mod;
		if (ref->ref_mod == 0) {
			drop_delayed_ref(trans, delayed_refs, head, ref);
			done = true;
		} else {
			/*
			 * Can't have multiples of the same ref on a tree block.
			 */
			WARN_ON(ref->type == BTRFS_TREE_BLOCK_REF_KEY ||
				ref->type == BTRFS_SHARED_BLOCK_REF_KEY);
		}
next:
		next = next2;
	}

	return done;
}
			      struct btrfs_delayed_ref_root *delayed_refs,
			      struct btrfs_delayed_ref_head *head)
{
	struct btrfs_delayed_ref_node *ref;
	u64 seq = 0;

	assert_spin_locked(&head->lock);

	if (list_empty(&head->ref_list))
		return;

	/* We don't have too many refs to merge for data. */
	if (head->is_data)
		return;

	spin_lock(&fs_info->tree_mod_seq_lock);
	if (!list_empty(&fs_info->tree_mod_seq_list)) {
		struct seq_list *elem;

		elem = list_first_entry(&fs_info->tree_mod_seq_list,
					struct seq_list, list);
		seq = elem->seq;
	}
	spin_unlock(&fs_info->tree_mod_seq_lock);

	ref = list_first_entry(&head->ref_list, struct btrfs_delayed_ref_node,
			       list);
	while (&ref->list != &head->ref_list) {
		if (seq && ref->seq >= seq)
			goto next;

		if (merge_ref(trans, delayed_refs, head, ref, seq)) {
			if (list_empty(&head->ref_list))
				break;
			ref = list_first_entry(&head->ref_list,
					       struct btrfs_delayed_ref_node,
					       list);
			continue;
		}
next:
		ref = list_next_entry(ref, list);
	}
}
struct btrfs_delayed_ref_head *
btrfs_select_ref_head(struct btrfs_trans_handle *trans)
{
	struct btrfs_delayed_ref_root *delayed_refs;
	struct btrfs_delayed_ref_head *head;
	u64 start;
	bool loop = false;

	delayed_refs = &trans->transaction->delayed_refs;

again:
	start = delayed_refs->run_delayed_start;
	head = find_ref_head(&delayed_refs->href_root, start, 1);
	if (!head && !loop) {
		delayed_refs->run_delayed_start = 0;
		start = 0;
		loop = true;
		head = find_ref_head(&delayed_refs->href_root, start, 1);
		if (!head)
			return NULL;
	} else if (!head && loop) {
		return NULL;
	}

	while (head->processing) {
		struct rb_node *node;

		node = rb_next(&head->href_node);
		if (!node) {
			if (loop)
				return NULL;
			delayed_refs->run_delayed_start = 0;
			start = 0;
			loop = true;
			goto again;
		}
		head = rb_entry(node, struct btrfs_delayed_ref_head,
				href_node);
	}

	head->processing = 1;
	WARN_ON(delayed_refs->num_heads_ready == 0);
	delayed_refs->num_heads_ready--;
	delayed_refs->run_delayed_start = head->node.bytenr +
		head->node.num_bytes;
	return head;
}
