/* This file is included from kernel/sched.c */

#include <litmus/litmus.h>
#include <litmus/sched_plugin.h>

static void update_time_litmus(struct rq *rq, struct task_struct *p)
{
	lt_t now = litmus_clock();
	p->rt_param.job_params.exec_time +=
		now - p->rt_param.job_params.exec_start;
	p->rt_param.job_params.exec_start = now;
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
	long prev_state;
	/* WARNING: rq is _not_ locked! */
	if (is_realtime(prev))
		update_time_litmus(rq, prev);

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
		prev_state = prev->state;
		spin_unlock(&rq->lock);
		double_rq_lock(rq, other_rq);
		if (prev->state != prev_state) {
			TRACE_TASK(prev, 
				   "state changed while we dropped"
				   " the lock: now=%d, old=%d",
				   prev->state, prev_state);
			if (prev_state && !prev->state) {
				/* prev task became unblocked
				 * we need to simulate normal sequence of events 
				 * to scheduler plugins.
				 */
				litmus->task_block(prev);
				litmus->task_wake_up(prev);
			}
		}

		set_task_cpu(rq->litmus_next, smp_processor_id());

		/* now that we have the lock we need to make sure a
		 *  couple of things still hold:
		 *  - it is still a real-time task
		 *  - it is still runnable (could have been stopped)
		 */
		if (!is_realtime(rq->litmus_next) ||
		    !is_running(rq->litmus_next)) {
			/* BAD BAD BAD */
			TRACE_TASK(rq->litmus_next, 
				   "migration invariant FAILED: rt=%d running=%d\n",
				   is_realtime(rq->litmus_next),
				   is_running(rq->litmus_next));
		}
		/* release the other CPU's runqueue, but keep ours */
		spin_unlock(&other_rq->lock);
	} 
}

static void enqueue_task_litmus(struct rq *rq, struct task_struct *p, int wakeup)
{
	if (wakeup)
		litmus->task_wake_up(p);
	else
		TRACE_TASK(p, "ignoring an enqueue, not a wake up.\n");
}

static void dequeue_task_litmus(struct rq *rq, struct task_struct *p, int sleep)
{
	if (sleep)
		litmus->task_block(p);
	else
		TRACE_TASK(p, "ignoring a dequeue, not going to sleep.\n");
}

static void yield_task_litmus(struct rq *rq)
{
	BUG_ON(rq->curr != current);
	litmus->complete_job();
}

/* Plugins are responsible for this.
 */
static void check_preempt_curr_litmus(struct rq *rq, struct task_struct *p)
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
		picked->rt_param.job_params.exec_start = litmus_clock();
	return picked;
}

static void task_tick_litmus(struct rq *rq, struct task_struct *p)
{
}

/* This is called when a task became a real-time task, either due
 * to a SCHED_* class transition or due to PI mutex inheritance.\
 * We don't handle Linux PI mutex inheritance yet. Use LITMUS provided
 * synchronization primitives instead.
 */
static void set_curr_task_litmus(struct rq *rq)
{
	rq->curr->rt_param.job_params.exec_start = litmus_clock();
}


#ifdef CONFIG_SMP

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
	.load_balance		= load_balance_litmus,
	.move_one_task		= move_one_task_litmus,
#endif

	.set_curr_task          = set_curr_task_litmus,
	.task_tick		= task_tick_litmus,
};
