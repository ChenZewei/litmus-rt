/*
 * kernel/rt_domain.c
 *
 * LITMUS real-time infrastructure. This file contains the
 * functions that manipulate RT domains. RT domains are an abstraction
 * of a ready queue and a release queue.
 */

#include <linux/percpu.h>
#include <linux/sched.h>
#include <linux/list.h>

#include <litmus/litmus.h>
#include <litmus/sched_plugin.h>
#include <litmus/sched_trace.h>

#include <litmus/rt_domain.h>

#include <litmus/trace.h>

#include <litmus/heap.h>

static int dummy_resched(rt_domain_t *rt)
{
	return 0;
}

static int dummy_order(struct heap_node* a, struct heap_node* b)
{
	return 0;
}

/* default implementation: use default lock */
static void default_release_jobs(rt_domain_t* rt, struct heap* tasks)
{
	merge_ready(rt, tasks);
}

static unsigned int time2slot(lt_t time)
{
	return (unsigned int) time2quanta(time, FLOOR) % RELEASE_QUEUE_SLOTS;
}

static enum hrtimer_restart on_release_timer(struct hrtimer *timer)
{
	long flags;
	struct release_heap* rh;

	TS_RELEASE_START;

	rh = container_of(timer, struct release_heap, timer);

	spin_lock_irqsave(&rh->dom->release_lock, flags);
	/* remove from release queue */
	list_del(&rh->list);
	spin_unlock_irqrestore(&rh->dom->release_lock, flags);

	/* call release callback */
	rh->dom->release_jobs(rh->dom, &rh->heap);

	TS_RELEASE_END;

	return  HRTIMER_NORESTART;
}

/* Caller most hold release lock.
 * Will return heap for given time. If no such heap exists prior to the invocation
 * it will be created.
 */
static struct release_heap* get_release_heap(rt_domain_t *rt, struct task_struct* t)
{
	struct list_head* pos;
	struct release_heap* heap = NULL;
	struct release_heap* rh;
	lt_t release_time = get_release(t);
	unsigned int slot = time2slot(release_time);

	/* initialize pos for the case that the list is empty */
	pos = rt->release_queue.slot[slot].next;
	list_for_each(pos, &rt->release_queue.slot[slot]) {
		rh = list_entry(pos, struct release_heap, list);
		if (release_time == rh->release_time) {
			/* perfect match -- this happens on hyperperiod
			 * boundaries
			 */
			heap = rh;
			break;
		} else if (lt_before(release_time, rh->release_time)) {
			/* we need to insert a new node since rh is
			 * already in the future
			 */
			break;
		}
	}
	if (!heap) {
		/* use pre-allocated release heap */
		rh = tsk_rt(t)->rel_heap;
		
		/* initialize */
		rh->release_time = release_time;
		rh->dom = rt;
		heap_init(&rh->heap);
		
		/* initialize timer */
		hrtimer_init(&rh->timer, CLOCK_MONOTONIC, HRTIMER_MODE_ABS);
		rh->timer.function = on_release_timer;
#ifdef CONFIG_HIGH_RES_TIMERS
		rh->timer.cb_mode = HRTIMER_CB_IRQSAFE;
#endif

		/* add to release queue */
		list_add(&rh->list, pos->prev);
		heap = rh;
	}
	return heap;
}

static void arm_release_timer(unsigned long _rt)
{
	rt_domain_t *rt = (rt_domain_t*) _rt;
	unsigned long flags;
	struct list_head list;
	struct list_head *pos, *safe;
	struct task_struct* t;
	struct release_heap* rh;
	int armed;
	lt_t release = 0;

	local_irq_save(flags);
	TRACE("arm_release_timer() at %llu\n", litmus_clock());
	spin_lock(&rt->tobe_lock);
	list_replace_init(&rt->tobe_released, &list);
	spin_unlock(&rt->tobe_lock);

	/* We only have to defend against the ISR since norq callbacks
	 * are serialized.
	 */
	list_for_each_safe(pos, safe, &list) {
		/* pick task of work list */
		t = list_entry(pos, struct task_struct, rt_param.list);
		sched_trace_task_release(t);
		list_del(pos);

		/* put into release heap while holding release_lock */
		spin_lock(&rt->release_lock);
		rh = get_release_heap(rt, t);
		heap_insert(rt->order, &rh->heap, tsk_rt(t)->heap_node);
		TRACE_TASK(t, "arm_release_timer(): added to release heap\n");
		armed   = hrtimer_active(&rh->timer);
		release = rh->release_time;
		spin_unlock(&rt->release_lock);

		/* activate timer if necessary */
		if (!armed) {
			TRACE_TASK(t, "arming timer 0x%p\n", &rh->timer);
			hrtimer_start(&rh->timer,
				      ns_to_ktime(release),
				      HRTIMER_MODE_ABS);
		} else
			TRACE_TASK(t, "timer already armed.\n");
	}

	local_irq_restore(flags);
}

void rt_domain_init(rt_domain_t *rt,
		    heap_prio_t order,
		    check_resched_needed_t check,
		    release_jobs_t release
		   )
{
	int i;

	BUG_ON(!rt);
	if (!check)
		check = dummy_resched;
	if (!release)
		release = default_release_jobs;
	if (!order)
		order = dummy_order;

	heap_init(&rt->ready_queue);
	INIT_LIST_HEAD(&rt->tobe_released);
	for (i = 0; i < RELEASE_QUEUE_SLOTS; i++)
		INIT_LIST_HEAD(&rt->release_queue.slot[i]);

	spin_lock_init(&rt->ready_lock);
	spin_lock_init(&rt->release_lock);
	spin_lock_init(&rt->tobe_lock);

	rt->check_resched 	= check;
	rt->release_jobs	= release;
	rt->order		= order;
	init_no_rqlock_work(&rt->arm_timer, arm_release_timer, (unsigned long) rt);
}

/* add_ready - add a real-time task to the rt ready queue. It must be runnable.
 * @new:       the newly released task
 */
void __add_ready(rt_domain_t* rt, struct task_struct *new)
{
	TRACE("rt: adding %s/%d (%llu, %llu) rel=%llu to ready queue at %llu\n",
	      new->comm, new->pid, get_exec_cost(new), get_rt_period(new),
	      get_release(new), litmus_clock());

	BUG_ON(heap_node_in_heap(tsk_rt(new)->heap_node));

	heap_insert(rt->order, &rt->ready_queue, tsk_rt(new)->heap_node);
	rt->check_resched(rt);
}

/* merge_ready - Add a sorted set of tasks to the rt ready queue. They must be runnable.
 * @tasks      - the newly released tasks
 */
void __merge_ready(rt_domain_t* rt, struct heap* tasks)
{
	heap_union(rt->order, &rt->ready_queue, tasks);
	rt->check_resched(rt);
}

/* add_release - add a real-time task to the rt release queue.
 * @task:        the sleeping task
 */
void __add_release(rt_domain_t* rt, struct task_struct *task)
{
	TRACE_TASK(task, "add_release(), rel=%llu\n", get_release(task));
	list_add(&tsk_rt(task)->list, &rt->tobe_released);
	task->rt_param.domain = rt;
	do_without_rqlock(&rt->arm_timer);
}

