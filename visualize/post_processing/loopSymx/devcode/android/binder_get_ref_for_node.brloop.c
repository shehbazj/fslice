
static struct binder_ref *binder_get_ref_for_node(struct binder_proc *proc,
						  struct binder_node *node)
{
	struct rb_node *n;
	struct rb_node **p = &proc->refs_by_node.rb_node;
	struct rb_node *parent = NULL;
	struct binder_ref *ref, *new_ref;
	struct binder_context *context = proc->context;

	// node is the node whose reference we need to get
	// parent is the iterator
	// ref = reference for the iterator

	while (*p) {
		parent = *p;
		ref = rb_entry(parent, struct binder_ref, rb_node_node);

		if (node < ref->node)
			p = &(*p)->rb_left;
		else if (node > ref->node)
			p = &(*p)->rb_right;
		else
			return ref;
	}

	// no exact reference found, generate a new reference

	new_ref = kzalloc(sizeof(*ref), GFP_KERNEL);
	if (new_ref == NULL)
		return NULL;
	binder_stats_created(BINDER_STAT_REF);
	new_ref->debug_id = ++binder_last_id;
	new_ref->proc = proc;
	new_ref->node = node;
	rb_link_node(&new_ref->rb_node_node, parent, p);
	rb_insert_color(&new_ref->rb_node_node, &proc->refs_by_node);

	// iterate through the entire rb tree, rb_next picks the next node
	// in the tree that has an immdediate grater prioirty than the previous
	// rb_node.

	new_ref->desc = (node == context->binder_context_mgr_node) ? 0 : 1;
	
	// keep incrementing the ref->desc by 1 each time we move to the next
	// node.

	// XXX BEGIN 
	// new_ref->desc = 0 or 1

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

	// TEST 0. if : [2] , 1 break.
	// TEST 0 : else if :  []

	/*
	rb_link_node(&new_ref->rb_node_desc, parent, p);
	rb_insert_color(&new_ref->rb_node_desc, &proc->refs_by_desc);
	if (node) {
		hlist_add_head(&new_ref->node_entry, &node->refs);

		binder_debug(BINDER_DEBUG_INTERNAL_REFS,
			     "%d new ref %d desc %d for node %d\n",
			      proc->pid, new_ref->debug_id, new_ref->desc,
			      node->debug_id);
	} else {
		binder_debug(BINDER_DEBUG_INTERNAL_REFS,
			     "%d new ref %d desc %d for dead node\n",
			      proc->pid, new_ref->debug_id, new_ref->desc);
	}
	*/

	return new_ref;
}
