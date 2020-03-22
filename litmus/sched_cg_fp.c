/*
 * litmus/sched_cg_fp.c
 *
 * Implementation of the CG-FP scheduling algorithm.
 *
 * This version uses the simple approach and serializes all scheduling
 * decisions by the use of a queue lock. This is probably not the
 * best way to do it, but it should suffice for now.
 */

#include <linux/spinlock.h>
#include <linux/percpu.h>
#include <linux/sched.h>
#include <linux/slab.h>

#include <litmus/debug_trace.h>
#include <litmus/litmus.h>
#include <litmus/jobs.h>
#include <litmus/sched_plugin.h>
#include <litmus/fp_common.h>
#include <litmus/sched_trace.h>
#include <litmus/trace.h>
#include <litmus/parallel_degree.h>

#include <litmus/preempt.h>
#include <litmus/budget.h>
#include <litmus/np.h>

#include <litmus/bheap.h>

#ifdef CONFIG_SCHED_CPU_AFFINITY
#include <litmus/affinity.h>
#endif

/* to set up domain/cpu mappings */
#include <litmus/litmus_proc.h>

#include <linux/module.h>

/* Overview of CG-FP operations.
 *
 * For a detailed explanation of CG-FP have a look at the FMLP paper. This
 * description only covers how the individual operations are implemented in
 * LITMUS.
 *
 * link_task_to_cpu(T, cpu) 	- Low-level operation to update the linkage
 *                                structure (NOT the actually scheduled
 *                                task). If there is another linked task To
 *                                already it will set To->linked_on = NO_CPU
 *                                (thereby removing its association with this
 *                                CPU). However, it will not requeue the
 *                                previously linked task (if any). It will set
 *                                T's state to not completed and check whether
 *                                it is already running somewhere else. If T
 *                                is scheduled somewhere else it will link
 *                                it to that CPU instead (and pull the linked
 *                                task to cpu). T may be NULL.
 *
 * unlink(T)			- Unlink removes T from all scheduler data
 *                                structures. If it is linked to some CPU it
 *                                will link NULL to that CPU. If it is
 *                                currently queued in the cgfp queue it will
 *                                be removed from the rt_domain. It is safe to
 *                                call unlink(T) if T is not linked. T may not
 *                                be NULL.
 *
 * requeue(T)			- Requeue will insert T into the appropriate
 *                                queue. If the system is in real-time mode and
 *                                the T is released already, it will go into the
 *                                ready queue. If the system is not in
 *                                real-time mode is T, then T will go into the
 *                                release queue. If T's release time is in the
 *                                future, it will go into the release
 *                                queue. That means that T's release time/job
 *                                no/etc. has to be updated before requeu(T) is
 *                                called. It is not safe to call requeue(T)
 *                                when T is already queued. T may not be NULL.
 *
 * cgfp_job_arrival(T)	- This is the catch all function when T enters
 *                                the system after either a suspension or at a
 *                                job release. It will queue T (which means it
 *                                is not safe to call cgfp_job_arrival(T) if
 *                                T is already queued) and then check whether a
 *                                preemption is necessary. If a preemption is
 *                                necessary it will update the linkage
 *                                accordingly and cause scheduled to be called
 *                                (either with an IPI or need_resched). It is
 *                                safe to call cgfp_job_arrival(T) if T's
 *                                next job has not been actually released yet
 *                                (releast time in the future). T will be put
 *                                on the release queue in that case.
 *
 * curr_job_completion()	- Take care of everything that needs to be done
 *                                to prepare the current task for its next
 *                                release and place it in the right queue with
 *                                cgfp_job_arrival().
 *
 *
 * When we now that T is linked to CPU then link_task_to_cpu(NULL, CPU) is
 * equivalent to unlink(T). Note that if you unlink a task from a CPU none of
 * the functions will automatically propagate pending task from the ready queue
 * to a linked task. This is the job of the calling function ( by means of
 * fp_prio_take).
 */


/* cpu_entry_t - maintain the linked and scheduled state
 */
typedef struct  {
	int 			cpu;
	struct task_struct*	linked;		/* only RT tasks */
	struct task_struct*	scheduled;	/* only RT tasks */
	struct bheap_node*	hn;
} cpu_entry_t;
DEFINE_PER_CPU(cpu_entry_t, cgfp_cpu_entries);


typedef struct {
	rt_domain_t 		domain;
	struct fp_prio_queue	ready_queue;
/*
 * scheduling lock slock
 * protects the domain and serializes scheduling decisions
 */
#define slock domain.ready_lock

} cgfp_domain_t;

cpu_entry_t* cgfp_cpus[NR_CPUS];

/* the cpus queue themselves according to priority in here */
static struct bheap_node cgfp_heap_node[NR_CPUS];
static struct bheap      cgfp_cpu_heap;

// static rt_domain_t cgfp;
static cgfp_domain_t cgfp;
#define cgfp_lock (cgfp.slock)

static pd_node cgfp_pd_stack[MAX_STACK_NUM];

static pd_list cgfp_pd_list;


/* Uncomment this if you want to see all scheduling decisions in the
 * TRACE() log.
#define WANT_ALL_SCHED_EVENTS
 */

static int cpu_lower_prio(struct bheap_node *_a, struct bheap_node *_b)
{
	cpu_entry_t *a, *b;
	a = _a->value;
	b = _b->value;
	/* Note that a and b are inverted: we want the lowest-priority CPU at
	 * the top of the heap.
	 */
	return fp_higher_prio(b->linked, a->linked);
}

/* update_cpu_position - Move the cpu entry to the correct place to maintain
 *                       order in the cpu queue. Caller must hold cgfp lock.
 */
static void update_cpu_position(cpu_entry_t *entry)
{
	if (likely(bheap_node_in_heap(entry->hn)))
		bheap_delete(cpu_lower_prio, &cgfp_cpu_heap, entry->hn);
	bheap_insert(cpu_lower_prio, &cgfp_cpu_heap, entry->hn);
}

/* caller must hold cgfp lock */
static cpu_entry_t* lowest_prio_cpu(void)
{
	struct bheap_node* hn;
	hn = bheap_peek(cpu_lower_prio, &cgfp_cpu_heap);
	return hn->value;
}


/* link_task_to_cpu - Update the link of a CPU.
 *                    Handles the case where the to-be-linked task is already
 *                    scheduled on a different CPU.
 */
static noinline void link_task_to_cpu(struct task_struct* linked,
				      cpu_entry_t *entry)
{
	cpu_entry_t *sched;
	struct task_struct* tmp;
	int on_cpu;

	BUG_ON(linked && !is_realtime(linked));

	/* Currently linked task is set to be unlinked. */
	if (entry->linked) {
		entry->linked->rt_param.linked_on = NO_CPU;
	}

	/* Link new task to CPU. */
	if (linked) {
		/* handle task is already scheduled somewhere! */
		on_cpu = linked->rt_param.scheduled_on;
		if (on_cpu != NO_CPU) {
			sched = &per_cpu(cgfp_cpu_entries, on_cpu);
			/* this should only happen if not linked already */
			BUG_ON(sched->linked == linked);

			/* If we are already scheduled on the CPU to which we
			 * wanted to link, we don't need to do the swap --
			 * we just link ourselves to the CPU and depend on
			 * the caller to get things right.
			 */
			if (entry != sched) {
				TRACE_TASK(linked,
					   "already scheduled on %d, updating link.\n",
					   sched->cpu);
				tmp = sched->linked;
				linked->rt_param.linked_on = sched->cpu;
				sched->linked = linked;
				update_cpu_position(sched);
				linked = tmp;
			}
		}
		if (linked) /* might be NULL due to swap */
			linked->rt_param.linked_on = entry->cpu;
	}
	entry->linked = linked;
#ifdef WANT_ALL_SCHED_EVENTS
	if (linked)
		TRACE_TASK(linked, "linked to %d.\n", entry->cpu);
	else
		TRACE("NULL linked to %d.\n", entry->cpu);
#endif
	update_cpu_position(entry);
}

/* unlink - Make sure a task is not linked any longer to an entry
 *          where it was linked before. Must hold cgfp_lock.
 */
static noinline void unlink(struct task_struct* t)
{
	cpu_entry_t *entry;

	if (t->rt_param.linked_on != NO_CPU) {
		/* unlink */
		entry = &per_cpu(cgfp_cpu_entries, t->rt_param.linked_on);
		t->rt_param.linked_on = NO_CPU;
		link_task_to_cpu(NULL, entry);
	} else if (is_queued(t)) {
		/* This is an interesting situation: t is scheduled,
		 * but was just recently unlinked.  It cannot be
		 * linked anywhere else (because then it would have
		 * been relinked to this CPU), thus it must be in some
		 * queue. We must remove it from the list in this
		 * case.
		 */
		remove(&cgfp.domain, t);
	}
}

static noinline int is_constrained(struct task_struct *task) {
	int tgid;
	int parallel_degree = 0;
	if(!task)
		return 0;
	BUG_ON(!task);
	tgid = task->tgid;

	parallel_degree = get_active_num(&cgfp_pd_list, tgid);
	TRACE_TASK(task, "parallel degree: %d\n", parallel_degree);
	
	return (parallel_degree >= task->rt_param.task_params.constrained_parallel_degree);
}

/* preempt - force a CPU to reschedule
 */
static void preempt(cpu_entry_t *entry)
{
	preempt_if_preemptable(entry->scheduled, entry->cpu);
}

/* requeue - Put an unlinked task into CG-FP domain.
 *           Caller must hold cgfp_lock.
 */
static noinline void requeue(struct task_struct* task)
{
	int curr_tgid;
	pd_node* node;
	BUG_ON(!task);
	/* sanity check before insertion */
	BUG_ON(is_queued(task));
	curr_tgid = task->tgid;

	if (is_early_releasing(task) || is_released(task, litmus_clock())) {
		fp_prio_add(&cgfp.ready_queue, task, get_priority(task));
	} else {
		/* it has got to wait */
		if (is_constrained(task)) {
			node = find_pd_node_in_list(&cgfp_pd_list, curr_tgid);
			// BUG_ON(!node);
			if (!is_cq_exist(&(node->queue), task)) {
				cq_enqueue(&(node->queue), task);
			}
		} else {
			pd_add(&cgfp_pd_list, curr_tgid);
			add_release(&cgfp.domain, task);
		}
	}
}

#ifdef CONFIG_SCHED_CPU_AFFINITY
static cpu_entry_t* cgfp_get_nearest_available_cpu(cpu_entry_t *start)
{
	cpu_entry_t *affinity;

	get_nearest_available_cpu(affinity, start, cgfp_cpu_entries,
#ifdef CONFIG_RELEASE_MASTER
			cgfp.domain.release_master,
#else
			NO_CPU,
#endif
			cpu_online_mask);

	return(affinity);
}
#endif

/* check for any necessary preemptions */
static void check_for_preemptions(void)
{
	struct task_struct *task;
	cpu_entry_t *last;


#ifdef CONFIG_PREFER_LOCAL_LINKING
	cpu_entry_t *local;

	/* Before linking to other CPUs, check first whether the local CPU is
	 * idle. */
	local = this_cpu_ptr(&cgfp_cpu_entries);
	task  = fp_prio_peek(&cgfp.ready_queue);

	if (task && !local->linked
#ifdef CONFIG_RELEASE_MASTER
	    && likely(local->cpu != cgfp.domain.release_master)
#endif
		) {
		task = fp_prio_take(&cgfp.ready_queue);
		TRACE_TASK(task, "linking to local CPU %d to avoid IPI\n", local->cpu);
		link_task_to_cpu(task, local);
		preempt(local);
	}
#endif

	for (last = lowest_prio_cpu();
	     fp_preemption_needed(&cgfp.ready_queue, last->linked);
	     last = lowest_prio_cpu()) {
		/* preemption necessary */
		task = fp_prio_take(&cgfp.ready_queue);
		TRACE("check_for_preemptions: attempting to link task %d to %d\n",
		      task->pid, last->cpu);

#ifdef CONFIG_SCHED_CPU_AFFINITY
		{
			cpu_entry_t *affinity =
					cgfp_get_nearest_available_cpu(
						&per_cpu(cgfp_cpu_entries, task_cpu(task)));
			if (affinity)
				last = affinity;
			else if (requeue_preempted_job(last->linked))
				requeue(last->linked);
		}
#else
		if (requeue_preempted_job(last->linked))
			requeue(last->linked);
#endif

		link_task_to_cpu(task, last);
		preempt(last);
	}
}

/* cgfp_job_arrival: task is either resumed or released */
static noinline void cgfp_job_arrival(struct task_struct* task)
{
	BUG_ON(!task);
	requeue(task);
	check_for_preemptions();
}

static void cgfp_release_jobs(rt_domain_t* rt, struct bheap* tasks)
{
	unsigned long flags;
	struct bheap_node* bh_node;
	struct task_struct* task;

	raw_spin_lock_irqsave(&cgfp_lock, flags);

	while (!bheap_empty(tasks)) {
		bh_node = bheap_take(fp_ready_order, tasks);
		task = bheap2task(bh_node);
    fp_prio_add(&cgfp.ready_queue, task, get_priority(task));
	}
	check_for_preemptions();
	
	raw_spin_unlock_irqrestore(&cgfp_lock, flags);
}

/* caller holds cgfp_lock */
static noinline void curr_job_completion(int forced)
{
	int tgid;
	pd_node* node;
	struct task_struct *t = current;
	struct task_struct *resumed_task;
	BUG_ON(!t);
	tgid = t->tgid;	
	sched_trace_task_completion(t, forced);

	TRACE_TASK(t, "job_completion(forced=%d).\n", forced);


	/* set flags */
	tsk_rt(t)->completed = 0;
	/* prepare for next period */
	prepare_for_next_period(t);
	if (is_early_releasing(t) || is_released(t, litmus_clock()))
		sched_trace_task_release(t);
	else {
		pd_sub(&cgfp_pd_list, tgid);
		if (!is_constrained(t)) {
			node = find_pd_node_in_list(&cgfp_pd_list, tgid);
			BUG_ON(!node);
			resumed_task = cq_dequeue(&(node->queue));
			if (resumed_task) {
				pd_add(&cgfp_pd_list, resumed_task->tgid);
				if (is_early_releasing(resumed_task) || is_released(resumed_task, litmus_clock())) {
					sched_trace_task_release(resumed_task);
					fp_prio_add(&cgfp.ready_queue, resumed_task, get_priority(resumed_task));
				}
				else {
					add_release(&cgfp.domain, resumed_task);
				}
			}
		}
	}
		
	/* unlink */
	unlink(t);
	/* requeue
	 * But don't requeue a blocking task. */
	if (is_current_running())
		cgfp_job_arrival(t);
}


/* Getting schedule() right is a bit tricky. schedule() may not make any
 * assumptions on the state of the current task since it may be called for a
 * number of reasons. The reasons include a scheduler_tick() determined that it
 * was necessary, because sys_exit_np() was called, because some Linux
 * subsystem determined so, or even (in the worst case) because there is a bug
 * hidden somewhere. Thus, we must take extreme care to determine what the
 * current state is.
 *
 * The CPU could currently be scheduling a task (or not), be linked (or not).
 *
 * The following assertions for the scheduled task could hold:
 *
 *      - !is_running(scheduled)        // the job blocks
 *	- scheduled->timeslice == 0	// the job completed (forcefully)
 *	- is_completed()		// the job completed (by syscall)
 * 	- linked != scheduled		// we need to reschedule (for any reason)
 * 	- is_np(scheduled)		// rescheduling must be delayed,
 *					   sys_exit_np must be requested
 *
 * Any of these can occur together.
 */
static struct task_struct* cgfp_schedule(struct task_struct * prev)
{
	cpu_entry_t* entry = this_cpu_ptr(&cgfp_cpu_entries);
	int out_of_time, sleep, preempt, np, exists, blocks;
	// int out_of_time, sleep, preempt, np, exists, blocks, constrained;
	struct task_struct* next = NULL;

#ifdef CONFIG_RELEASE_MASTER
	/* Bail out early if we are the release master.
	 * The release master never schedules any real-time tasks.
	 */
	if (unlikely(cgfp.domain.release_master == entry->cpu)) {
		sched_state_task_picked();
		return NULL;
	}
#endif

	raw_spin_lock(&cgfp_lock);

	/* sanity checking */
	BUG_ON(entry->scheduled && entry->scheduled != prev);
	BUG_ON(entry->scheduled && !is_realtime(prev));
	BUG_ON(is_realtime(prev) && !entry->scheduled);

	/* (0) Determine state */
	exists      = entry->scheduled != NULL;
	blocks      = exists && !is_current_running();
	out_of_time = exists && budget_enforced(entry->scheduled)
		&& budget_exhausted(entry->scheduled);
	np 	    = exists && is_np(entry->scheduled);
	sleep	    = exists && is_completed(entry->scheduled);
	preempt     = entry->scheduled != entry->linked;

#ifdef WANT_ALL_SCHED_EVENTS
	TRACE_TASK(prev, "invoked cgfp_schedule.\n");
#endif

	if (exists)
		TRACE_TASK(prev,
			   "blocks:%d out_of_time:%d np:%d sleep:%d preempt:%d "
			   "state:%d sig:%d\n",
			   blocks, out_of_time, np, sleep, preempt,
			   prev->state, signal_pending(prev));
	// if (entry->linked && preempt)
	// 	TRACE_TASK(prev, "will be preempted by %s/%d\n",
	// 		   entry->linked->comm, entry->linked->pid);


	/* If a task blocks we have no choice but to reschedule.
	 */
	if (blocks)
		unlink(entry->scheduled);

	/* Request a sys_exit_np() call if we would like to preempt but cannot.
	 * We need to make sure to update the link structure anyway in case
	 * that we are still linked. Multiple calls to request_exit_np() don't
	 * hurt.
	 */
	if (np && (out_of_time || preempt || sleep)) {
		unlink(entry->scheduled);
		request_exit_np(entry->scheduled);
	}

	/* Any task that is preemptable and either exhausts its execution
	 * budget or wants to sleep completes. We may have to reschedule after
	 * this. Don't do a job completion if we block (can't have timers running
	 * for blocked jobs).
	 */
	if (!np && (out_of_time || sleep))
		curr_job_completion(!sleep);

	/* Link pending task if we became unlinked.
	 */
	if (!entry->linked)
		link_task_to_cpu(fp_prio_take(&cgfp.ready_queue), entry);

	/* The final scheduling decision. Do we need to switch for some reason?
	 * If linked is different from scheduled, then select linked as next.
	 */
	if ((!np || blocks) && 
	    entry->linked != entry->scheduled) {
		/* Schedule a linked job? */
		if (entry->linked) {
			entry->linked->rt_param.scheduled_on = entry->cpu;
			next = entry->linked;
			TRACE_TASK(next, "scheduled_on = P%d\n", smp_processor_id());
		}
		if (entry->scheduled) {
			/* not gonna be scheduled soon */
			entry->scheduled->rt_param.scheduled_on = NO_CPU;
			TRACE_TASK(entry->scheduled, "scheduled_on = NO_CPU\n");
		}
	} else
		/* Only override Linux scheduler if we have a real-time task
		 * scheduled that needs to continue.
		 */
		if (exists)
			next = prev;

	sched_state_task_picked();

	raw_spin_unlock(&cgfp_lock);

#ifdef WANT_ALL_SCHED_EVENTS
	TRACE("cgfp_lock released, next=0x%p\n", next);

	if (next)
		TRACE_TASK(next, "scheduled at %llu\n", litmus_clock());
	else if (exists && !next)
		TRACE("becomes idle at %llu.\n", litmus_clock());
#endif


	return next;
}


/* _finish_switch - we just finished the switch away from prev
 */
static void cgfp_finish_switch(struct task_struct *prev)
{
	cpu_entry_t* 	entry = this_cpu_ptr(&cgfp_cpu_entries);

	entry->scheduled = is_realtime(current) ? current : NULL;
#ifdef WANT_ALL_SCHED_EVENTS
	TRACE_TASK(prev, "switched away from\n");
#endif
}


/*	Prepare a task for running in RT mode
 */
static void cgfp_task_new(struct task_struct* t, int on_rq, int is_scheduled)
{
	unsigned long 		flags;
	cpu_entry_t* 		entry;
	int tgid = t->tgid;

	raw_spin_lock_irqsave(&cgfp_lock, flags);

	/* setup job params */
	release_at(t, litmus_clock());

	pd_task_release(&cgfp_pd_list, cgfp_pd_stack, tgid);

	if (is_scheduled) {
		pd_add(&cgfp_pd_list, tgid);
		entry = &per_cpu(cgfp_cpu_entries, task_cpu(t));
		BUG_ON(entry->scheduled);

#ifdef CONFIG_RELEASE_MASTER
		if (entry->cpu != cgfp.domain.release_master) {
#endif
			entry->scheduled = t;
			tsk_rt(t)->scheduled_on = task_cpu(t);
#ifdef CONFIG_RELEASE_MASTER
		} else {
			/* do not schedule on release master */
			preempt(entry); /* force resched */
			tsk_rt(t)->scheduled_on = NO_CPU;
		}
#endif
	} else {
		t->rt_param.scheduled_on = NO_CPU;
	}
	t->rt_param.linked_on = NO_CPU;

	if (on_rq || is_scheduled)
		cgfp_job_arrival(t);
	raw_spin_unlock_irqrestore(&cgfp_lock, flags);
}

static void cgfp_task_wake_up(struct task_struct *task)
{
	unsigned long flags;
	lt_t now;

	TRACE_TASK(task, "wake_up at %llu\n", litmus_clock());

	raw_spin_lock_irqsave(&cgfp_lock, flags);
	now = litmus_clock();
	if (is_sporadic(task) && is_tardy(task, now)) {
		inferred_sporadic_job_release_at(task, now);
	}
	cgfp_job_arrival(task);
	raw_spin_unlock_irqrestore(&cgfp_lock, flags);
}

static void cgfp_task_block(struct task_struct *t)
{
	unsigned long flags;

	TRACE_TASK(t, "block at %llu\n", litmus_clock());

	/* unlink if necessary */
	raw_spin_lock_irqsave(&cgfp_lock, flags);
	unlink(t);
	raw_spin_unlock_irqrestore(&cgfp_lock, flags);

	BUG_ON(!is_realtime(t));
}


static void cgfp_task_exit(struct task_struct * t)
{
	unsigned long flags;
	int tgid = t->tgid;
	pd_node* node;
	struct task_struct* resumed_task;

	/* unlink if necessary */
	raw_spin_lock_irqsave(&cgfp_lock, flags);

	if (tsk_rt(t)->scheduled_on != NO_CPU) {
		cgfp_cpus[tsk_rt(t)->scheduled_on]->scheduled = NULL;
		tsk_rt(t)->scheduled_on = NO_CPU;
		
		pd_sub(&cgfp_pd_list, tgid);
		if (!is_constrained(t)) {
			node = find_pd_node_in_list(&cgfp_pd_list, tgid);
			// BUG_ON(!node);
			resumed_task = cq_dequeue(&(node->queue));
			if (resumed_task) {
				pd_add(&cgfp_pd_list, resumed_task->tgid);
				if (is_early_releasing(resumed_task) || is_released(resumed_task, litmus_clock())) {
					fp_prio_add(&cgfp.ready_queue, resumed_task, get_priority(resumed_task));
				} else {
					add_release(&cgfp.domain, resumed_task);
				}
			}
		}
	}
	
	unlink(t);
	pd_task_exit(&cgfp_pd_list, tgid);
	raw_spin_unlock_irqrestore(&cgfp_lock, flags);

	BUG_ON(!is_realtime(t));
        TRACE_TASK(t, "RIP\n");
}

static long cgfp_admit_task(struct task_struct* tsk)
{
	TRACE_TASK(tsk, "Admitting task[%d].\n", tsk->pid);
	return 0;
}

static struct domain_proc_info cgfp_domain_proc_info;
static long cgfp_get_domain_proc_info(struct domain_proc_info **ret)
{
	*ret = &cgfp_domain_proc_info;
	return 0;
}

static void cgfp_setup_domain_proc(void)
{
	int i, cpu;
	int release_master =
#ifdef CONFIG_RELEASE_MASTER
			atomic_read(&release_master_cpu);
#else
		NO_CPU;
#endif
	int num_rt_cpus = num_online_cpus() - (release_master != NO_CPU);
	struct cd_mapping *map;

	memset(&cgfp_domain_proc_info, 0, sizeof(cgfp_domain_proc_info));
	init_domain_proc_info(&cgfp_domain_proc_info, num_rt_cpus, 1);
	cgfp_domain_proc_info.num_cpus = num_rt_cpus;
	cgfp_domain_proc_info.num_domains = 1;

	cgfp_domain_proc_info.domain_to_cpus[0].id = 0;
	for (cpu = 0, i = 0; cpu < num_online_cpus(); ++cpu) {
		if (cpu == release_master)
			continue;
		map = &cgfp_domain_proc_info.cpu_to_domains[i];
		map->id = cpu;
		cpumask_set_cpu(0, map->mask);
		++i;

		/* add cpu to the domain */
		cpumask_set_cpu(cpu,
			cgfp_domain_proc_info.domain_to_cpus[0].mask);
	}
}

static long cgfp_activate_plugin(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&cgfp_cpu_heap);
	pd_stack_init(cgfp_pd_stack);
	pd_list_init(&cgfp_pd_list);
#ifdef CONFIG_RELEASE_MASTER
	cgfp.domain.release_master = atomic_read(&release_master_cpu);
#endif

	for_each_online_cpu(cpu) {
		entry = &per_cpu(cgfp_cpu_entries, cpu);
		bheap_node_init(&entry->hn, entry);
		entry->linked    = NULL;
		entry->scheduled = NULL;
#ifdef CONFIG_RELEASE_MASTER
		if (cpu != cgfp.domain.release_master) {
#endif
			TRACE("CG-FP: Initializing CPU #%d.\n", cpu);
			update_cpu_position(entry);
#ifdef CONFIG_RELEASE_MASTER
		} else {
			TRACE("CG-FP: CPU %d is release master.\n", cpu);
		}
#endif
	}

	cgfp_setup_domain_proc();

	return 0;
}

static long cgfp_deactivate_plugin(void)
{
	destroy_domain_proc_info(&cgfp_domain_proc_info);
	return 0;
}

/*	Plugin object	*/
static struct sched_plugin cg_fp_plugin __cacheline_aligned_in_smp = {
	.plugin_name		= "CG-FP",
	.finish_switch		= cgfp_finish_switch,
	.task_new		= cgfp_task_new,
	.complete_job		= complete_job,
	.task_exit		= cgfp_task_exit,
	.schedule		= cgfp_schedule,
	.task_wake_up		= cgfp_task_wake_up,
	.task_block		= cgfp_task_block,
	.admit_task		= cgfp_admit_task,
	.activate_plugin	= cgfp_activate_plugin,
	.deactivate_plugin	= cgfp_deactivate_plugin,
	.get_domain_proc_info	= cgfp_get_domain_proc_info,
};


static int __init init_cg_fp(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&cgfp_cpu_heap);
	// pd_stack_init(cgfp_pd_stack);
	// pd_list_init(&cgfp_pd_list);
	/* initialize CPU state */
	for (cpu = 0; cpu < NR_CPUS; cpu++)  {
		entry = &per_cpu(cgfp_cpu_entries, cpu);
		cgfp_cpus[cpu] = entry;
		entry->cpu 	 = cpu;
		entry->hn        = &cgfp_heap_node[cpu];
		bheap_node_init(&entry->hn, entry);
	}
	fp_domain_init(&cgfp.domain, NULL, cgfp_release_jobs);
	return register_sched_plugin(&cg_fp_plugin);
}


module_init(init_cg_fp);
