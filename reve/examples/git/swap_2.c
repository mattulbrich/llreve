typedef int (*prio_queue_compare_fn)(const void *one, const void *two, void *cb_data);

struct prio_queue_entry {
	unsigned ctr;
	void *data;
};

struct prio_queue {
	prio_queue_compare_fn compare;
	unsigned insertion_ctr;
	void *cb_data;
	int alloc, nr;
	struct prio_queue_entry *array;
};

void swap(struct prio_queue *queue, int i, int j)
{
	struct prio_queue_entry tmp = queue->array[i];
	queue->array[i] = queue->array[j];
	queue->array[j] = tmp;
}
