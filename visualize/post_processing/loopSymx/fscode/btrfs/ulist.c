 */
void ulist_init(struct ulist *ulist)
{
	INIT_LIST_HEAD(&ulist->nodes);
	ulist->root = RB_ROOT;
	ulist->nnodes = 0;
}

static struct ulist_node *ulist_rbtree_search(struct ulist *ulist, u64 val)
{
	struct rb_node *n = ulist->root.rb_node;
	struct ulist_node *u = NULL;

	while (n) {
		u = rb_entry(n, struct ulist_node, rb_node);
		if (u->val < val)
			n = n->rb_right;
		else if (u->val > val)
			n = n->rb_left;
		else
			return u;
	}
	return NULL;
}

static int ulist_rbtree_insert(struct ulist *ulist, struct ulist_node *ins)
{
	struct rb_node **p = &ulist->root.rb_node;
	struct rb_node *parent = NULL;
	struct ulist_node *cur = NULL;

	while (*p) {
		parent = *p;
		cur = rb_entry(parent, struct ulist_node, rb_node);

		if (cur->val < ins->val)
			p = &(*p)->rb_right;
		else if (cur->val > ins->val)
			p = &(*p)->rb_left;
		else
			return -EEXIST;
	}
	rb_link_node(&ins->rb_node, parent, p);
	rb_insert_color(&ins->rb_node, &ulist->root);
	return 0;
}
