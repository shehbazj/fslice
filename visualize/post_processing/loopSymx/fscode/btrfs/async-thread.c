
static void run_ordered_work(struct __btrfs_workqueue *wq)
{
	struct list_head *list = &wq->ordered_list;
	struct btrfs_work *work;
	spinlock_t *lock = &wq->list_lock;
	unsigned long flags;

	while (1) {
		void *wtag;

		spin_lock_irqsave(lock, flags);
		if (list_empty(list))
			break;
		work = list_entry(list->next, struct btrfs_work,
				  ordered_list);
		if (!test_bit(WORK_DONE_BIT, &work->flags))
			break;

		/*
		 * we are going to call the ordered done function, but
		 * we leave the work item on the list as a barrier so
		 * that later work items that are done don't have their
		 * functions called before this one returns
		 */
		if (test_and_set_bit(WORK_ORDER_DONE_BIT, &work->flags))
			break;
		trace_btrfs_ordered_sched(work);
		spin_unlock_irqrestore(lock, flags);
		work->ordered_func(work);

		/* now take the lock again and drop our item from the list */
		spin_lock_irqsave(lock, flags);
		list_del(&work->ordered_list);
		spin_unlock_irqrestore(lock, flags);

		/*
		 * We don't want to call the ordered free functions with the
		 * lock held though. Save the work as tag for the trace event,
		 * because the callback could free the structure.
		 */
		wtag = work;
		work->ordered_free(work);
		trace_btrfs_all_work_done(wq->fs_info, wtag);
	}
	spin_unlock_irqrestore(lock, flags);
}
