/*
 * litmus/sched_cg_edf.c
 *
 * Implementation of the CG-EDF scheduling algorithm.
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
#include <litmus/edf_common.h>
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

/* Overview of CG-EDF operations.
 *
 * For a detailed explanation of CG-EDF have a look at the FMLP paper. This
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
 *                                currently queued in the cgedf queue it will
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
 * cgedf_job_arrival(T)	- This is the catch all function when T enters
 *                                the system after either a suspension or at a
 *                                job release. It will queue T (which means it
 *                                is not safe to call cgedf_job_arrival(T) if
 *                                T is already queued) and then check whether a
 *                                preemption is necessary. If a preemption is
 *                                necessary it will update the linkage
 *                                accordingly and cause scheduled to be called
 *                                (either with an IPI or need_resched). It is
 *                                safe to call cgedf_job_arrival(T) if T's
 *                                next job has not been actually released yet
 *                                (releast time in the future). T will be put
 *                                on the release queue in that case.
 *
 * curr_job_completion()	- Take care of everything that needs to be done
 *                                to prepare the current task for its next
 *                                release and place it in the right queue with
 *                                cgedf_job_arrival().
 *
 *
 * When we now that T is linked to CPU then link_task_to_cpu(NULL, CPU) is
 * equivalent to unlink(T). Note that if you unlink a task from a CPU none of
 * the functions will automatically propagate pending task from the ready queue
 * to a linked task. This is the job of the calling function ( by means of
 * __take_ready).
 */


/* cpu_entry_t - maintain the linked and scheduled state
 */
typedef struct  {
	int 			cpu;
	struct task_struct*	linked;		/* only RT tasks */
	struct task_struct*	scheduled;	/* only RT tasks */
	struct bheap_node*	hn;
} cpu_entry_t;
DEFINE_PER_CPU(cpu_entry_t, cgedf_cpu_entries);

cpu_entry_t* cgedf_cpus[NR_CPUS];

/* the cpus queue themselves according to priority in here */
static struct bheap_node cgedf_heap_node[NR_CPUS];
static struct bheap      cgedf_cpu_heap;

static rt_domain_t cgedf;
#define cgedf_lock (cgedf.ready_lock)

static pd_node cgedf_pd_stack[MAX_STACK_NUM];

static pd_list cgedf_pd_list;


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
	return edf_higher_prio(b->linked, a->linked);
}

/* update_cpu_position - Move the cpu entry to the correct place to maintain
 *                       order in the cpu queue. Caller must hold cgedf lock.
 */
static void update_cpu_position(cpu_entry_t *entry)
{
	if (likely(bheap_node_in_heap(entry->hn)))
		bheap_delete(cpu_lower_prio, &cgedf_cpu_heap, entry->hn);
	bheap_insert(cpu_lower_prio, &cgedf_cpu_heap, entry->hn);
}

/* caller must hold cgedf lock */
static cpu_entry_t* lowest_prio_cpu(void)
{
	struct bheap_node* hn;
	hn = bheap_peek(cpu_lower_prio, &cgedf_cpu_heap);
	return hn->value;
}


/* link_task_to_cpu - Update the link of a CPU.
 *                    Handles the case where the to-be-linked task is already
 *                    scheduled on a different CPU.
 */
static noinline void link_task_to_cpu(struct task_struct* linked,
				      cpu_entry_t *entry)
{
	// TRACE("link_task_to_cpu()\n");
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
			sched = &per_cpu(cgedf_cpu_entries, on_cpu);
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
 *          where it was linked before. Must hold cgedf_lock.
 */
static noinline void unlink(struct task_struct* t)
{
	TRACE("unlink()\n");
	cpu_entry_t *entry;

	if (t->rt_param.linked_on != NO_CPU) {
		/* unlink */
		entry = &per_cpu(cgedf_cpu_entries, t->rt_param.linked_on);
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
		remove(&cgedf, t);
	}
}

static noinline int is_constrained(struct task_struct *task) {
	TRACE("is_constrained()\n");
	// cpu_entry_t *entry;
	// int tgid, cpu;
	int tgid;
	uint parallel_degree = 0;
	if(!task)
		return 0;
	BUG_ON(!task);
	tgid = task->tgid;

	// TRACE_TASK(task, "Checking constraint...\n");

	parallel_degree = get_active_num(&cgedf_pd_list, tgid);

	// for (cpu = 0; cpu < NR_CPUS; cpu++) {
	// for_each_online_cpu(cpu) {
	// 	entry = &per_cpu(cgedf_cpu_entries, cpu);
	// 	TRACE_TASK(task, "CPU[%d] is executing:", cpu);
	// 	if (entry->scheduled != NULL) {
	// 	TRACE_TASK(task, "task[PID %d TGID %d]\n", entry->scheduled->pid, entry->scheduled->tgid);
	// 		if (tgid == entry->scheduled->tgid)
	// 			parallel_degree++;
	// 	} else {
	// 	TRACE_TASK(task, "none.\n");
	// 	}
	// }
	TRACE_TASK(task, "task PID:%d\n",task->pid);
	TRACE_TASK(task, "task TGID:%d\n", task->tgid);
	TRACE_TASK(task, "task PD:%d\n", parallel_degree);
	TRACE_TASK(task, "task CPD:%d\n",task->rt_param.task_params.constrained_parallel_degree);
	if (parallel_degree >= task->rt_param.task_params.constrained_parallel_degree)
			TRACE_TASK(task, "Constrained!\n");	
	return (parallel_degree >= task->rt_param.task_params.constrained_parallel_degree);
	// return 0;
}

/* preempt - force a CPU to reschedule
 */
static void preempt(cpu_entry_t *entry)
{
	TRACE("preempt()\n");
	preempt_if_preemptable(entry->scheduled, entry->cpu);
}

/* requeue - Put an unlinked task into cg-edf domain.
 *           Caller must hold cgedf_lock.
 */
static noinline void requeue(struct task_struct* task)
{
	TRACE("requeue()\n");
	int tgid = task->tgid;
	pd_node* node;
	BUG_ON(!task);
	/* sanity check before insertion */
	BUG_ON(is_queued(task));

	// TRACE("Requeuing.\n");
	// if ((is_early_releasing(task) || is_released(task, litmus_clock())) && (!is_constrained(task)))
	if (is_early_releasing(task) || is_released(task, litmus_clock())) {
	// 	if (is_constrained(task)) {
	// 		node = find_pd_node_in_list(&cgedf_pd_list, tgid);
	// 		// BUG_ON(!node);
	// // TRACE("Constrained. Task enqueues to the constrained queue.\n");
	// 		if (!is_cq_exist(&(node->queue), task)) {
	// 			cq_enqueue(&(node->queue), task);
	// 		}
	// 	} else {
	// 		pd_add(&cgedf_pd_list, tgid);
	// 		__add_ready(&cgedf, task);
	// 	}
	  // pd_add(&cgedf_pd_list, tgid);
		__add_ready(&cgedf, task);
	}
	else {
		/* it has got to wait */
		// pd_sub(&cgedf_pd_list, tgid);
		add_release(&cgedf, task);
	}
}

#ifdef CONFIG_SCHED_CPU_AFFINITY
static cpu_entry_t* cgedf_get_nearest_available_cpu(cpu_entry_t *start)
{
	cpu_entry_t *affinity;

	get_nearest_available_cpu(affinity, start, cgedf_cpu_entries,
#ifdef CONFIG_RELEASE_MASTER
			cgedf.release_master,
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
	TRACE("check_for_preemptions()\n");
	struct task_struct *task;
	cpu_entry_t *last;


#ifdef CONFIG_PREFER_LOCAL_LINKING
	cpu_entry_t *local;

	/* Before linking to other CPUs, check first whether the local CPU is
	 * idle. */
	local = this_cpu_ptr(&cgedf_cpu_entries);
	task  = __peek_ready(&cgedf);

	if (task && !local->linked
#ifdef CONFIG_RELEASE_MASTER
	    && likely(local->cpu != cgedf.release_master)
#endif
		) {
		task = __take_ready(&cgedf);
		TRACE_TASK(task, "linking to local CPU %d to avoid IPI\n", local->cpu);
		link_task_to_cpu(task, local);
		preempt(local);
	}
#endif

	for (last = lowest_prio_cpu();
	     edf_preemption_needed(&cgedf, last->linked);
	     last = lowest_prio_cpu()) {
		/* preemption necessary */
		task = __take_ready(&cgedf);
		TRACE("check_for_preemptions: attempting to link task %d to %d\n",
		      task->pid, last->cpu);

#ifdef CONFIG_SCHED_CPU_AFFINITY
		{
			cpu_entry_t *affinity =
					cgedf_get_nearest_available_cpu(
						&per_cpu(cgedf_cpu_entries, task_cpu(task)));
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

static void check_for_preemption(struct task_struct* task)
{
	TRACE("check_for_preemptions()\n");
	cpu_entry_t *last;


#ifdef CONFIG_PREFER_LOCAL_LINKING
	cpu_entry_t *local;

	/* Before linking to other CPUs, check first whether the local CPU is
	 * idle. */
	local = this_cpu_ptr(&cgedf_cpu_entries);
	// if (!task)
	// task  = __peek_ready(&cgedf);

	if (task && !local->linked
#ifdef CONFIG_RELEASE_MASTER
	    && likely(local->cpu != cgedf.release_master)
#endif
		) {
		TRACE_TASK(task, "linking to local CPU %d to avoid IPI\n", local->cpu);
		link_task_to_cpu(task, local);
		preempt(local);
	} else
#endif
  {
		last = lowest_prio_cpu();
		/* preemption necessary */
 
		if (last->linked) {
			if (task && (!is_realtime(last->linked) || edf_higher_prio(task, last->linked))) {
				TRACE("check_for_preemptions: attempting to link task %d to %d\n",
							task->pid, last->cpu);

#ifdef CONFIG_SCHED_CPU_AFFINITY
				{
					cpu_entry_t *affinity =
							cgedf_get_nearest_available_cpu(
								&per_cpu(cgedf_cpu_entries, task_cpu(task)));
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
		} else {
			if (task && (!is_realtime(last->scheduled) || edf_higher_prio(task, last->scheduled))) {
				link_task_to_cpu(task, last);
				preempt(last);
			}
		}
	}
}

/* cgedf_job_arrival: task is either resumed or released */
static noinline void cgedf_job_arrival(struct task_struct* task)
{
	TRACE("cgedf_job_arrival()\n");
	BUG_ON(!task);
	requeue(task);
	check_for_preemptions();
}

static void POT(struct bheap_node* root) {
	struct task_struct* task;
	pd_node* node;
	int curr_tgid;
	if (!root)
		return;
	else {
		if (root->child)
			POT(root->child);
		if (root->next)
			POT(root->next);
		task = bheap2task(root);
		// TRACE("Task [%d] in heap.\n", task->pid);
		curr_tgid = task->tgid;
		TRACE("Task [%d] in heap. Degree: %d ", task->pid, root->degree);
		if (root->parent) 
			TRACE("  parent task [%d]", bheap2task(root->parent)->pid);
		if (root->next) 
			TRACE("  brother task [%d]", bheap2task(root->next)->pid);
		if (root->child) 
			TRACE("  child task [%d]", bheap2task(root->child)->pid);
		TRACE("\n");
		// if (is_constrained(task)) {
		// 	node = find_pd_node_in_list(&cgedf_pd_list, curr_tgid);
		// 	// BUG_ON(!node);
		// 	if (!is_cq_exist(&(node->queue), task)) {
		// 		cq_enqueue(&(node->queue), task);
		// 	}
		// 	root->is_constrained = 1;
		// } else {
		// 	pd_add(&cgedf_pd_list, curr_tgid);
		// 	root->is_constrained = 0;
		// }
	}
}

// static void POT_constrained(struct bheap_node* root) {
// 	struct task_struct* task;
// 	if (!root)
// 		return NULL;
// 	else {
// 		task = bheap2task(root);
// 		TRACE("Task [%d] in heap.\n", task->pid);
// 		if (root->child) {
// 			POT(root->child);
// 		}
// 		if (root->next) {
// 			POT(root->next);
// 		}
// 	}
// }

static void cgedf_release_jobs(rt_domain_t* rt, struct bheap* tasks)
{
	TRACE("cgedf_release_jobs()\n");
	unsigned long flags;
	struct bheap_node* bh_node;
	// struct bheap_node* bh_node = bheap_take(rt->order, tasks);
	struct bheap_node* temp;
	struct task_struct* task;
	struct task_struct* temp_task;
	pd_node* node;
	int last_constrained_tgid = MAX_INT, curr_tgid;
	// cons_queue* c_queue;
	TRACE("Tasks release.\n");

	raw_spin_lock_irqsave(&cgedf_lock, flags);

	temp = tasks->head;
	POT(temp);
	// while (temp) {
	// 	temp_task = bheap2task(temp);
	// 	TRACE("Task [%d] in heap.\n", temp_task->pid);
	// 	if (temp->parent) 
	// 		TRACE("Task [%d]'s parent task [%d].\n", temp_task->pid, bheap2task(temp->parent)->pid);
	// 	if (temp->child) 
	// 		TRACE("Task [%d]'s child task [%d].\n", temp_task->pid, bheap2task(temp->child)->pid);
	// 	temp = temp->next;
	// }

	bh_node = bheap_take(rt->order, tasks);
	
  // TRACE("Deal with released tasks: %llu.\n", litmus_clock());
	while (bh_node) {
		task = bheap2task(bh_node);
		curr_tgid = task->tgid;
		// if (bh_node->parent) 
		// 	TRACE("Task [%d]'s parent task [%d].\n", task->pid, bheap2task(bh_node->parent)->pid);
		// if (bh_node->next) 
		// 	TRACE("Task [%d]'s brother task [%d].\n", task->pid, bheap2task(bh_node->next)->pid);
		// if (bh_node->child) 
		// 	TRACE("Task [%d]'s child task [%d].\n", task->pid, bheap2task(bh_node->child)->pid);
		// BUG_ON(!task);
	TRACE_TASK(task, "Task [%d] [%d] releases.\n", task->pid, curr_tgid);
  // TRACE("Get a released task: %llu.\n", litmus_clock());
		if (last_constrained_tgid == curr_tgid || is_constrained(task)) {
	TRACE_TASK(task, "Task enqueues to the constrained queue.\n");
  // TRACE("Add task to constrained queue: %llu.\n", litmus_clock());
			node = find_pd_node_in_list(&cgedf_pd_list, curr_tgid);
			// BUG_ON(!node);
			if (!is_cq_exist(&(node->queue), task)) {
				cq_enqueue(&(node->queue), task);
			}
			last_constrained_tgid = curr_tgid;
		} else {
  // TRACE("Add task to ready queue: %llu.\n", litmus_clock());
			pd_add(&cgedf_pd_list, curr_tgid);
			__add_ready(&cgedf, task);
			// check_for_preemption(task);
		}
  // TRACE("Finish adding at: %llu.\n", litmus_clock());
		bh_node = bheap_take(rt->order, tasks);
	}

  // TRACE("Finish releasing: %llu.\n", litmus_clock());
	// bheap_init(tasks);
	// __merge_ready(rt, tasks);
  // TRACE("Check for preemptions: %llu.\n", litmus_clock());
	check_for_preemptions();
  // TRACE("Finish preemption checking: %llu.\n", litmus_clock());
	
	raw_spin_unlock_irqrestore(&cgedf_lock, flags);
}

/* caller holds cgedf_lock */
static noinline void curr_job_completion(int forced)
{
	TRACE("curr_job_completion()\n");
	struct task_struct *t = current;
	// int tgid;
	pd_node* node;
	struct task_struct* resumed_task;
	BUG_ON(!t);
	sched_trace_task_completion(t, forced);

	// tgid = t->tgid;	
	TRACE_TASK(t, "job_completion(forced=%d).\n", forced);

	pd_sub(&cgedf_pd_list, t->tgid);
	if (!is_constrained(t)) {
		node = find_pd_node_in_list(&cgedf_pd_list, t->tgid);
		BUG_ON(!node);
		resumed_task = cq_dequeue(&(node->queue));
		if (resumed_task) {
			pd_add(&cgedf_pd_list, resumed_task->tgid);
			__add_ready(&cgedf, resumed_task);
		}
// 		 else {
// TRACE("No constrained task.\n");
// 		}
	}

	/* set flags */
	tsk_rt(t)->completed = 0;
	/* prepare for next period */
	prepare_for_next_period(t);
	if (is_early_releasing(t) || is_released(t, litmus_clock()))
		sched_trace_task_release(t);
	/* unlink */
	unlink(t);
	/* requeue
	 * But don't requeue a blocking task. */
	if (is_current_running())
		cgedf_job_arrival(t);
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
static struct task_struct* cgedf_schedule(struct task_struct * prev)
{
	// TRACE("cgedf_schedule()\n");
	cpu_entry_t* entry = this_cpu_ptr(&cgedf_cpu_entries);
	int out_of_time, sleep, preempt, np, exists, blocks;
	// int out_of_time, sleep, preempt, np, exists, blocks, constrained;
	struct task_struct* next = NULL;
	struct task_struct* temp = NULL;
	pd_node* node;
	struct task_struct* resumed_task;

#ifdef CONFIG_RELEASE_MASTER
	/* Bail out early if we are the release master.
	 * The release master never schedules any real-time tasks.
	 */
	if (unlikely(cgedf.release_master == entry->cpu)) {
		sched_state_task_picked();
		return NULL;
	}
#endif

	raw_spin_lock(&cgedf_lock);

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
	TRACE_TASK(prev, "invoked cgedf_schedule.\n");
#endif

	if (exists)
		TRACE_TASK(prev,
			   "blocks:%d out_of_time:%d np:%d sleep:%d preempt:%d "
			   "state:%d sig:%d\n",
			   blocks, out_of_time, np, sleep, preempt,
			   prev->state, signal_pending(prev));
	if (entry->linked && preempt)
		TRACE_TASK(prev, "will be preempted by %s/%d\n",
			   entry->linked->comm, entry->linked->pid);


	/* If a task blocks we have no choice but to reschedule.
	 */
	if (blocks) {

		// pd_sub(&cgedf_pd_list, entry->scheduled->tgid);
		// if (!is_constrained(entry->scheduled)) {
		// 	node = find_pd_node_in_list(&cgedf_pd_list, entry->scheduled->tgid);
		// 	BUG_ON(!node);
		// 	resumed_task = cq_dequeue(&(node->queue));
		// 	if (resumed_task) {
		// 		pd_add(&cgedf_pd_list, resumed_task->tgid);
		// 		__add_ready(&cgedf, resumed_task);
		// 	}
		// }

		unlink(entry->scheduled);
	}

	/* Request a sys_exit_np() call if we would like to preempt but cannot.
	 * We need to make sure to update the link structure anyway in case
	 * that we are still linked. Multiple calls to request_exit_np() don't
	 * hurt.
	 */
	if (np && (out_of_time || preempt || sleep)) {

		// pd_sub(&cgedf_pd_list, entry->scheduled->tgid);
		// if (!is_constrained(entry->scheduled)) {
		// 	node = find_pd_node_in_list(&cgedf_pd_list, entry->scheduled->tgid);
		// 	BUG_ON(!node);
		// 	resumed_task = cq_dequeue(&(node->queue));
		// 	if (resumed_task) {
		// 		pd_add(&cgedf_pd_list, resumed_task->tgid);
		// 		__add_ready(&cgedf, resumed_task);
		// 	}
		// }

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
	if (!entry->linked){
		link_task_to_cpu(__take_ready(&cgedf), entry);
	}

	/* The final scheduling decision. Do we need to switch for some reason?
	 * If linked is different from scheduled, then select linked as next.
	 */
  // NULL != entry->linked &&
	if ((!np || blocks) && 
	    entry->linked != entry->scheduled ) {
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

	raw_spin_unlock(&cgedf_lock);

#ifdef WANT_ALL_SCHED_EVENTS
	TRACE("cgedf_lock released, next=0x%p\n", next);

	if (next)
		TRACE_TASK(next, "scheduled at %llu\n", litmus_clock());
	else if (exists && !next)
		TRACE("becomes idle at %llu.\n", litmus_clock());
#endif


	return next;
	// return NULL;
}


/* _finish_switch - we just finished the switch away from prev
 */
static void cgedf_finish_switch(struct task_struct *prev)
{
	// TRACE("cgedf_finish_switch()\n");
	cpu_entry_t* 	entry = this_cpu_ptr(&cgedf_cpu_entries);

	entry->scheduled = is_realtime(current) ? current : NULL;
#ifdef WANT_ALL_SCHED_EVENTS
	TRACE_TASK(prev, "switched away from\n");
#endif
}


/*	Prepare a task for running in RT mode
 */
static void cgedf_task_new(struct task_struct* t, int on_rq, int is_scheduled)
{
	TRACE("cgedf_task_new()\n");
	unsigned long 		flags;
	cpu_entry_t* 		entry;
	int tgid = t->tgid;

	raw_spin_lock_irqsave(&cgedf_lock, flags);

	/* setup job params */
	release_at(t, litmus_clock());

	pd_task_release(&cgedf_pd_list, cgedf_pd_stack, tgid);

	if (is_scheduled) {
		entry = &per_cpu(cgedf_cpu_entries, task_cpu(t));
		BUG_ON(entry->scheduled);

#ifdef CONFIG_RELEASE_MASTER
		if (entry->cpu != cgedf.release_master) {
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
		cgedf_job_arrival(t);
	
	raw_spin_unlock_irqrestore(&cgedf_lock, flags);
}

static void cgedf_task_wake_up(struct task_struct *task)
{
	TRACE("cgedf_task_wake_up()\n");
	unsigned long flags;
	lt_t now;

	TRACE_TASK(task, "wake_up at %llu\n", litmus_clock());

	raw_spin_lock_irqsave(&cgedf_lock, flags);
	now = litmus_clock();
	if (is_sporadic(task) && is_tardy(task, now)) {
		inferred_sporadic_job_release_at(task, now);
	}
	cgedf_job_arrival(task);
	raw_spin_unlock_irqrestore(&cgedf_lock, flags);
}

static void cgedf_task_block(struct task_struct *t)
{
	TRACE("cgedf_task_block()\n");
	unsigned long flags;

	TRACE_TASK(t, "block at %llu\n", litmus_clock());

	/* unlink if necessary */
	raw_spin_lock_irqsave(&cgedf_lock, flags);
	unlink(t);
	raw_spin_unlock_irqrestore(&cgedf_lock, flags);

	BUG_ON(!is_realtime(t));
}


static void cgedf_task_exit(struct task_struct * t)
{
	TRACE("cgedf_task_exit()\n");
	unsigned long flags;
	int tgid = t->tgid;
	pd_node* node;
	struct task_struct* resumed_task;

	/* unlink if necessary */
	raw_spin_lock_irqsave(&cgedf_lock, flags);

	if (tsk_rt(t)->scheduled_on != NO_CPU) {
		cgedf_cpus[tsk_rt(t)->scheduled_on]->scheduled = NULL;
		tsk_rt(t)->scheduled_on = NO_CPU;
		
		pd_sub(&cgedf_pd_list, tgid);
		if (!is_constrained(t)) {
			node = find_pd_node_in_list(&cgedf_pd_list, tgid);
			// BUG_ON(!node);
			resumed_task = cq_dequeue(&(node->queue));
			if (resumed_task) {
				pd_add(&cgedf_pd_list, resumed_task->tgid);
				__add_ready(&cgedf, resumed_task);
			}
			else {
	TRACE("No constrained task.\n");
			}
		}
		TRACE_TASK(t, "Active num::%d\n", get_active_num(&cgedf_pd_list, tgid));
		TRACE_TASK(t, "thread num:%d\n", find_pd_node_in_list(&cgedf_pd_list, tgid)->t_num);
		TRACE_TASK(t, "Constrained queue size:%d\n", find_pd_node_in_list(&cgedf_pd_list, tgid)->queue.length);
	}
	
	unlink(t);
	pd_task_exit(&cgedf_pd_list, tgid);
	raw_spin_unlock_irqrestore(&cgedf_lock, flags);

	BUG_ON(!is_realtime(t));
        TRACE_TASK(t, "RIP\n");
}

static long cgedf_admit_task(struct task_struct* tsk)
{
	TRACE("cgedf_admit_task()\n");
	TRACE_TASK(tsk, "Admitting task[%d].\n", tsk->pid);
	return 0;
}

#ifdef CONFIG_LITMUS_LOCKING

#include <litmus/fdso.h>

/* called with IRQs off */
static void set_priority_inheritance(struct task_struct* t, struct task_struct* prio_inh)
{
	int linked_on;
	int check_preempt = 0;

	raw_spin_lock(&cgedf_lock);

	TRACE_TASK(t, "inherits priority from %s/%d\n", prio_inh->comm, prio_inh->pid);
	tsk_rt(t)->inh_task = prio_inh;

	linked_on  = tsk_rt(t)->linked_on;

	/* If it is scheduled, then we need to reorder the CPU heap. */
	if (linked_on != NO_CPU) {
		TRACE_TASK(t, "%s: linked  on %d\n",
			   __FUNCTION__, linked_on);
		/* Holder is scheduled; need to re-order CPUs.
		 * We can't use heap_decrease() here since
		 * the cpu_heap is ordered in reverse direction, so
		 * it is actually an increase. */
		bheap_delete(cpu_lower_prio, &cgedf_cpu_heap,
			    cgedf_cpus[linked_on]->hn);
		bheap_insert(cpu_lower_prio, &cgedf_cpu_heap,
			    cgedf_cpus[linked_on]->hn);
	} else {
		/* holder may be queued: first stop queue changes */
		raw_spin_lock(&cgedf.release_lock);
		if (is_queued(t)) {
			TRACE_TASK(t, "%s: is queued\n",
				   __FUNCTION__);
			/* We need to update the position of holder in some
			 * heap. Note that this could be a release heap if we
			 * budget enforcement is used and this job overran. */
			check_preempt =
				!bheap_decrease(edf_ready_order,
					       tsk_rt(t)->heap_node);
		} else {
			/* Nothing to do: if it is not queued and not linked
			 * then it is either sleeping or currently being moved
			 * by other code (e.g., a timer interrupt handler) that
			 * will use the correct priority when enqueuing the
			 * task. */
			TRACE_TASK(t, "%s: is NOT queued => Done.\n",
				   __FUNCTION__);
		}
		raw_spin_unlock(&cgedf.release_lock);

		/* If holder was enqueued in a release heap, then the following
		 * preemption check is pointless, but we can't easily detect
		 * that case. If you want to fix this, then consider that
		 * simply adding a state flag requires O(n) time to update when
		 * releasing n tasks, which conflicts with the goal to have
		 * O(log n) merges. */
		if (check_preempt) {
			/* heap_decrease() hit the top level of the heap: make
			 * sure preemption checks get the right task, not the
			 * potentially stale cache. */
			bheap_uncache_min(edf_ready_order,
					 &cgedf.ready_queue);
			check_for_preemptions();
		}
	}

	raw_spin_unlock(&cgedf_lock);
}

/* called with IRQs off */
static void clear_priority_inheritance(struct task_struct* t)
{
	raw_spin_lock(&cgedf_lock);

	/* A job only stops inheriting a priority when it releases a
	 * resource. Thus we can make the following assumption.*/
	BUG_ON(tsk_rt(t)->scheduled_on == NO_CPU);

	TRACE_TASK(t, "priority restored\n");
	tsk_rt(t)->inh_task = NULL;

	/* Check if rescheduling is necessary. We can't use heap_decrease()
	 * since the priority was effectively lowered. */
	unlink(t);
	cgedf_job_arrival(t);

	raw_spin_unlock(&cgedf_lock);
}


/* ******************** FMLP support ********************** */

/* struct for semaphore with priority inheritance */
struct fmlp_semaphore {
	struct litmus_lock litmus_lock;

	/* current resource holder */
	struct task_struct *owner;

	/* highest-priority waiter */
	struct task_struct *hp_waiter;

	/* FIFO queue of waiting tasks */
	wait_queue_head_t wait;
};

static inline struct fmlp_semaphore* fmlp_from_lock(struct litmus_lock* lock)
{
	return container_of(lock, struct fmlp_semaphore, litmus_lock);
}

/* caller is responsible for locking */
struct task_struct* cgedf_find_hp_waiter(struct fmlp_semaphore *sem,
				   struct task_struct* skip)
{
	struct list_head	*pos;
	struct task_struct 	*queued, *found = NULL;

	list_for_each(pos, &sem->wait.task_list) {
		queued  = (struct task_struct*) list_entry(pos, wait_queue_t,
							   task_list)->private;

		/* Compare task prios, find high prio task. */
		if (queued != skip && edf_higher_prio(queued, found))
			found = queued;
	}
	return found;
}

int cgedf_fmlp_lock(struct litmus_lock* l)
{
	struct task_struct* t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	wait_queue_t wait;
	unsigned long flags;

	if (!is_realtime(t))
		return -EPERM;

	/* prevent nested lock acquisition --- not supported by FMLP */
	if (tsk_rt(t)->num_locks_held)
		return -EBUSY;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner) {
		/* resource is not free => must suspend and wait */

		init_waitqueue_entry(&wait, t);

		/* FIXME: interruptible would be nice some day */
		set_task_state(t, TASK_UNINTERRUPTIBLE);

		__add_wait_queue_tail_exclusive(&sem->wait, &wait);

		/* check if we need to activate priority inheritance */
		if (edf_higher_prio(t, sem->hp_waiter)) {
			sem->hp_waiter = t;
			if (edf_higher_prio(t, sem->owner))
				set_priority_inheritance(sem->owner, sem->hp_waiter);
		}

		TS_LOCK_SUSPEND;

		/* release lock before sleeping */
		spin_unlock_irqrestore(&sem->wait.lock, flags);

		/* We depend on the FIFO order.  Thus, we don't need to recheck
		 * when we wake up; we are guaranteed to have the lock since
		 * there is only one wake up per release.
		 */

		schedule();

		TS_LOCK_RESUME;

		/* Since we hold the lock, no other task will change
		 * ->owner. We can thus check it without acquiring the spin
		 * lock. */
		BUG_ON(sem->owner != t);
	} else {
		/* it's ours now */
		sem->owner = t;

		spin_unlock_irqrestore(&sem->wait.lock, flags);
	}

	tsk_rt(t)->num_locks_held++;

	return 0;
}

int cgedf_fmlp_unlock(struct litmus_lock* l)
{
	struct task_struct *t = current, *next;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;
	int err = 0;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner != t) {
		err = -EINVAL;
		goto out;
	}

	tsk_rt(t)->num_locks_held--;

	/* check if there are jobs waiting for this resource */
	next = __waitqueue_remove_first(&sem->wait);
	if (next) {
		/* next becomes the resouce holder */
		sem->owner = next;
		TRACE_CUR("lock ownership passed to %s/%d\n", next->comm, next->pid);

		/* determine new hp_waiter if necessary */
		if (next == sem->hp_waiter) {
			TRACE_TASK(next, "was highest-prio waiter\n");
			/* next has the highest priority --- it doesn't need to
			 * inherit.  However, we need to make sure that the
			 * next-highest priority in the queue is reflected in
			 * hp_waiter. */
			sem->hp_waiter = cgedf_find_hp_waiter(sem, next);
			if (sem->hp_waiter)
				TRACE_TASK(sem->hp_waiter, "is new highest-prio waiter\n");
			else
				TRACE("no further waiters\n");
		} else {
			/* Well, if next is not the highest-priority waiter,
			 * then it ought to inherit the highest-priority
			 * waiter's priority. */
			set_priority_inheritance(next, sem->hp_waiter);
		}

		/* wake up next */
		wake_up_process(next);
	} else
		/* becomes available */
		sem->owner = NULL;

	/* we lose the benefit of priority inheritance (if any) */
	if (tsk_rt(t)->inh_task)
		clear_priority_inheritance(t);

out:
	spin_unlock_irqrestore(&sem->wait.lock, flags);

	return err;
}

int cgedf_fmlp_close(struct litmus_lock* l)
{
	struct task_struct *t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;

	int owner;

	spin_lock_irqsave(&sem->wait.lock, flags);

	owner = sem->owner == t;

	spin_unlock_irqrestore(&sem->wait.lock, flags);

	if (owner)
		cgedf_fmlp_unlock(l);

	return 0;
}

void cgedf_fmlp_free(struct litmus_lock* lock)
{
	kfree(fmlp_from_lock(lock));
}

static struct litmus_lock_ops cgedf_fmlp_lock_ops = {
	.close  = cgedf_fmlp_close,
	.lock   = cgedf_fmlp_lock,
	.unlock = cgedf_fmlp_unlock,
	.deallocate = cgedf_fmlp_free,
};

static struct litmus_lock* cgedf_new_fmlp(void)
{
	struct fmlp_semaphore* sem;

	sem = kmalloc(sizeof(*sem), GFP_KERNEL);
	if (!sem)
		return NULL;

	sem->owner   = NULL;
	sem->hp_waiter = NULL;
	init_waitqueue_head(&sem->wait);
	sem->litmus_lock.ops = &cgedf_fmlp_lock_ops;

	return &sem->litmus_lock;
}

/* **** lock constructor **** */


static long cgedf_allocate_lock(struct litmus_lock **lock, int type,
				 void* __user unused)
{
	int err = -ENXIO;

	/* CG-EDF currently only supports the FMLP for global resources. */
	switch (type) {

	case FMLP_SEM:
		/* Flexible Multiprocessor Locking Protocol */
		*lock = cgedf_new_fmlp();
		if (*lock)
			err = 0;
		else
			err = -ENOMEM;
		break;

	};

	return err;
}

#endif

static struct domain_proc_info cgedf_domain_proc_info;
static long cgedf_get_domain_proc_info(struct domain_proc_info **ret)
{
	*ret = &cgedf_domain_proc_info;
	return 0;
}

static void cgedf_setup_domain_proc(void)
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

	memset(&cgedf_domain_proc_info, 0, sizeof(cgedf_domain_proc_info));
	init_domain_proc_info(&cgedf_domain_proc_info, num_rt_cpus, 1);
	cgedf_domain_proc_info.num_cpus = num_rt_cpus;
	cgedf_domain_proc_info.num_domains = 1;

	cgedf_domain_proc_info.domain_to_cpus[0].id = 0;
	for (cpu = 0, i = 0; cpu < num_online_cpus(); ++cpu) {
		if (cpu == release_master)
			continue;
		map = &cgedf_domain_proc_info.cpu_to_domains[i];
		map->id = cpu;
		cpumask_set_cpu(0, map->mask);
		++i;

		/* add cpu to the domain */
		cpumask_set_cpu(cpu,
			cgedf_domain_proc_info.domain_to_cpus[0].mask);
	}
}

static long cgedf_activate_plugin(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&cgedf_cpu_heap);
	pd_stack_init(cgedf_pd_stack);
	pd_list_init(&cgedf_pd_list);
#ifdef CONFIG_RELEASE_MASTER
	cgedf.release_master = atomic_read(&release_master_cpu);
#endif

	for_each_online_cpu(cpu) {
		entry = &per_cpu(cgedf_cpu_entries, cpu);
		bheap_node_init(&entry->hn, entry);
		entry->linked    = NULL;
		entry->scheduled = NULL;
#ifdef CONFIG_RELEASE_MASTER
		if (cpu != cgedf.release_master) {
#endif
			TRACE("CG-EDF: Initializing CPU #%d.\n", cpu);
			update_cpu_position(entry);
#ifdef CONFIG_RELEASE_MASTER
		} else {
			TRACE("CG-EDF: CPU %d is release master.\n", cpu);
		}
#endif
	}

	cgedf_setup_domain_proc();

	return 0;
}

static long cgedf_deactivate_plugin(void)
{
	destroy_domain_proc_info(&cgedf_domain_proc_info);
	return 0;
}

/*	Plugin object	*/
static struct sched_plugin cg_edf_plugin __cacheline_aligned_in_smp = {
	.plugin_name		= "CG-EDF",
	.finish_switch		= cgedf_finish_switch,
	.task_new		= cgedf_task_new,
	.complete_job		= complete_job,
	.task_exit		= cgedf_task_exit,
	.schedule		= cgedf_schedule,
	.task_wake_up		= cgedf_task_wake_up,
	.task_block		= cgedf_task_block,
	.admit_task		= cgedf_admit_task,
	.activate_plugin	= cgedf_activate_plugin,
	.deactivate_plugin	= cgedf_deactivate_plugin,
	.get_domain_proc_info	= cgedf_get_domain_proc_info,
#ifdef CONFIG_LITMUS_LOCKING
	.allocate_lock		= cgedf_allocate_lock,
#endif
};


static int __init init_cg_edf(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&cgedf_cpu_heap);
	// pd_stack_init(cgedf_pd_stack);
	// pd_list_init(&cgedf_pd_list);
	/* initialize CPU state */
	for (cpu = 0; cpu < NR_CPUS; cpu++)  {
		entry = &per_cpu(cgedf_cpu_entries, cpu);
		cgedf_cpus[cpu] = entry;
		entry->cpu 	 = cpu;
		entry->hn        = &cgedf_heap_node[cpu];
		bheap_node_init(&entry->hn, entry);
	}
	edf_domain_init(&cgedf, NULL, cgedf_release_jobs);
	return register_sched_plugin(&cg_edf_plugin);
}


module_init(init_cg_edf);
