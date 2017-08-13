
static int tree_insert(struct rb_root *root, struct extent_map *em)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent = NULL;
	struct extent_map *entry = NULL;
	struct rb_node *orig_parent = NULL;
	u64 end = range_end(em->start, em->len);

	while (*p) {
		parent = *p;
		entry = rb_entry(parent, struct extent_map, rb_node);

		if (em->start < entry->start)
			p = &(*p)->rb_left;
		else if (em->start >= extent_map_end(entry))
			p = &(*p)->rb_right;
		else
			return -EEXIST;
	}

	orig_parent = parent;
	while (parent && em->start >= extent_map_end(entry)) {
		parent = rb_next(parent);
		entry = rb_entry(parent, struct extent_map, rb_node);
	}
	if (parent)
		if (end > entry->start && em->start < extent_map_end(entry))
			return -EEXIST;

	parent = orig_parent;
	entry = rb_entry(parent, struct extent_map, rb_node);
	while (parent && em->start < entry->start) {
		parent = rb_prev(parent);
		entry = rb_entry(parent, struct extent_map, rb_node);
	}
	if (parent)
		if (end > entry->start && em->start < extent_map_end(entry))
			return -EEXIST;

	rb_link_node(&em->rb_node, orig_parent, p);
	rb_insert_color(&em->rb_node, root);
	return 0;
}
				     struct rb_node **prev_ret,
				     struct rb_node **next_ret)
{
	struct rb_node *n = root->rb_node;
	struct rb_node *prev = NULL;
	struct rb_node *orig_prev = NULL;
	struct extent_map *entry;
	struct extent_map *prev_entry = NULL;

	while (n) {
		entry = rb_entry(n, struct extent_map, rb_node);
		prev = n;
		prev_entry = entry;

		if (offset < entry->start)
			n = n->rb_left;
		else if (offset >= extent_map_end(entry))
			n = n->rb_right;
		else
			return n;
	}

	if (prev_ret) {
		orig_prev = prev;
		while (prev && offset >= extent_map_end(prev_entry)) {
			prev = rb_next(prev);
			prev_entry = rb_entry(prev, struct extent_map, rb_node);
		}
		*prev_ret = prev;
		prev = orig_prev;
	}

	if (next_ret) {
		prev_entry = rb_entry(prev, struct extent_map, rb_node);
		while (prev && offset < prev_entry->start) {
			prev = rb_prev(prev);
			prev_entry = rb_entry(prev, struct extent_map, rb_node);
		}
		*next_ret = prev;
	}
	return NULL;
}
