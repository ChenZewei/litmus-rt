/* This file is included from kernel/sched.c */

#include <litmus/litmus.h>
#include <litmus/sched_plugin.h>

static void update_time_litmus(struct rq *rq, struct task_struct *p)
{
	u64 delta = rq->clock - p->se.exec_start;
	if (unlikely((s64)delta < 0))
		delta = 0;
	/* per job counter */
	p->rt_param.job_params.exec_time += delta;
	/* task counter */
	p->se.sum_exec_runtime += delta;
	/* sched_clock() */
	p->se.exec_start = rq->clock;
	cpuacct_charge(p, delta);
}

static void double_rq_lock(struct rq *rq1, struct rq *rq2);
static void double_rq_unlock(struct rq *rq1, struct rq *rq2);

static void litmus_tick(struct rq *rq, struct task_struct *p)
{
	if (is_realtime(p))
		update_time_litmus(rq, p);
	litmus->tick(p);
}

static void litmus_schedule(struct rq *rq, struct task_struct *prev)
{
	struct rq* other_rq;
	long was_running;
	lt_t _maybe_deadlock = 0;
	/* WARNING: rq is _not_ locked! */
	if (is_realtime(prev)) {
		update_time_litmus(rq, prev);
		if (!is_running(prev))
			tsk_rt(prev)->present = 0;
	}

	/* let the plugin schedule */
	rq->litmus_next = litmus->schedule(prev);

	/* check if a global plugin pulled a task from a different RQ */
	if (rq->litmus_next && task_rq(rq->litmus_next) != rq) {
		/* we need to migrate the task */
		other_rq = task_rq(rq->litmus_next);
		TRACE_TASK(rq->litmus_next, "migrate from %d\n", other_rq->cpu);

		/* while we drop the lock, the prev task could change its
		 * state
		 */
		was_running = is_running(prev);
		mb();
		spin_unlock(&rq->lock);

		/* Don't race with a concurrent switch.  This could deadlock in
		 * the case of cross or circular migrations.  It's the job of
		 * the plugin to make sure that doesn't happen.
		 */
		TRACE_TASK(rq->litmus_next, "stack_in_use=%d\n",
			   rq->litmus_next->rt_param.stack_in_use);
		if (rq->litmus_next->rt_param.stack_in_use != NO_CPU) {
			TRACE_TASK(rq->litmus_next, "waiting to deschedule\n");
			_maybe_deadlock = litmus_clock();
		}
		while (rq->litmus_next->rt_param.stack_in_use != NO_CPU) {
			cpu_relax();
			mb();
			if (rq->litmus_next->rt_param.stack_in_use == NO_CPU)
				TRACE_TASK(rq->litmus_next,
					   "descheduled. Proceeding.\n");
			if (lt_before(_maybe_deadlock + 10000000,
				      litmus_clock())) {
				/* We've been spinning for 10ms.
				 * Something can't be right!
				 * Let's abandon the task and bail out; at least
				 * we will have debug info instead of a hard
				 * deadlock.
				 */
				TRACE_TASK(rq->litmus_next,
					   "stack too long in use. "
					   "Deadlock?\n");
				rq->litmus_next = NULL;

				/* bail out */
				spin_lock(&rq->lock);
				return;
			}
		}
#ifdef  __ARCH_WANT_UNLOCKED_CTXSW
		if (rq->litmus_next->oncpu)
			TRACE_TASK(rq->litmus_next, "waiting for !oncpu");
		while (rq->litmus_next->oncpu) {
			cpu_relax();
			mb();
		}
#endif
		double_rq_lock(rq, other_rq);
		mb();
		if (is_realtime(prev) && is_running(prev) != was_running) {
			TRACE_TASK(prev,
				   "state changed while we dropped"
				   " the lock: is_running=%d, was_running=%d\n",
				   is_running(prev), was_running);
			if (is_running(prev) && !was_running) {
				/* prev task became unblocked
				 * we need to simulate normal sequence of events
				 * to scheduler plugins.
				 */
				litmus->task_block(prev);
				litmus->task_wake_up(prev);
			}
		}

		set_task_cpu(rq->litmus_next, smp_processor_id());

		/* DEBUG: now that we have the lock we need to make sure a
		 *  couple of things still hold:
		 *  - it is still a real-time task
		 *  - it is still runnable (could have been stopped)
		 * If either is violated, then the active plugin is
		 * doing something wrong.
		 */
		if (!is_realtime(rq->litmus_next) ||
		    !is_running(rq->litmus_next)) {
			/* BAD BAD BAD */
			TRACE_TASK(rq->litmus_next,
				   "BAD: migration invariant FAILED: "
				   "rt=%d running=%d\n",
				   is_realtime(rq->litmus_next),
				   is_running(rq->litmus_next));
			/* drop the task */
			rq->litmus_next = NULL;
		}
		/* release the other CPU's runqueue, but keep ours */
		spin_unlock(&other_rq->lock);
	}
	if (rq->litmus_next)
		rq->litmus_next->rt_param.stack_in_use = rq->cpu;
}

static void enqueue_task_litmus(struct rq *rq, struct task_struct *p,
				int wakeup)
{
	if (wakeup) {
		sched_trace_task_resume(p);
		tsk_rt(p)->present = 1;
		litmus->task_wake_up(p);
	} else
		TRACE_TASK(p, "ignoring an enqueue, not a wake up.\n");
}

static void dequeue_task_litmus(struct rq *rq, struct task_struct *p, int sleep)
{
	if (sleep) {
		litmus->task_block(p);
		tsk_rt(p)->present = 0;
		sched_trace_task_block(p);
	} else
		TRACE_TASK(p, "ignoring a dequeue, not going to sleep.\n");
}

static void yield_task_litmus(struct rq *rq)
{
	BUG_ON(rq->curr != current);
	litmus->complete_job();
}

/* Plugins are responsible for this.
 */
static void check_preempt_curr_litmus(struct rq *rq, struct task_struct *p, int flags)
{
}

/* has already been taken care of */
static void put_prev_task_litmus(struct rq *rq, struct task_struct *p)
{
}

static struct task_struct *pick_next_task_litmus(struct rq *rq)
{
	struct task_struct* picked = rq->litmus_next;
	rq->litmus_next = NULL;
	if (picked)
		picked->se.exec_start = rq->clock;
	return picked;
}

static void task_tick_litmus(struct rq *rq, struct task_struct *p, int queued)
{
}

static void switched_to_litmus(struct rq *rq, struct task_struct *p, int running)
{
}

static void prio_changed_litmus(struct rq *rq, struct task_struct *p,
				int oldprio, int running)
{
}

unsigned int get_rr_interval_litmus(struct task_struct *p)
{
	/* return infinity */
	return 0;
}

/* This is called when a task became a real-time task, either due to a SCHED_*
 * class transition or due to PI mutex inheritance. We don't handle Linux PI
 * mutex inheritance yet (and probably never will). Use LITMUS provided
 * synchronization primitives instead.
 */
static void set_curr_task_litmus(struct rq *rq)
{
	rq->curr->se.exec_start = rq->clock;
}


#ifdef CONFIG_SMP
/* execve tries to rebalance task in this scheduling domain */
static int select_task_rq_litmus(struct task_struct *p, int sd_flag, int flags)
{
	/* preemption is already disabled.
	 * We don't want to change cpu here
	 */
	return smp_processor_id();
}

/* we don't repartition at runtime */

static unsigned long
load_balance_litmus(struct rq *this_rq, int this_cpu, struct rq *busiest,
		unsigned long max_load_move,
		struct sched_domain *sd, enum cpu_idle_type idle,
		int *all_pinned, int *this_best_prio)
{
	return 0;
}

static int
move_one_task_litmus(struct rq *this_rq, int this_cpu, struct rq *busiest,
		 struct sched_domain *sd, enum cpu_idle_type idle)
{
	return 0;
}
#endif

const struct sched_class litmus_sched_class = {
	.next			= &rt_sched_class,
	.enqueue_task		= enqueue_task_litmus,
	.dequeue_task		= dequeue_task_litmus,
	.yield_task		= yield_task_litmus,

	.check_preempt_curr	= check_preempt_curr_litmus,

	.pick_next_task		= pick_next_task_litmus,
	.put_prev_task		= put_prev_task_litmus,

#ifdef CONFIG_SMP
	.select_task_rq		= select_task_rq_litmus,

	.load_balance		= load_balance_litmus,
	.move_one_task		= move_one_task_litmus,
#endif

	.set_curr_task          = set_curr_task_litmus,
	.task_tick		= task_tick_litmus,

	.get_rr_interval	= get_rr_interval_litmus,

	.prio_changed		= prio_changed_litmus,
	.switched_to		= switched_to_litmus,
};
