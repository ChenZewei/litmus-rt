/* litmus/jobs.c - common job control code
 */

#include <linux/sched.h>

#include <litmus/litmus.h>
#include <litmus/jobs.h>

static inline void setup_release(struct task_struct *t, lt_t release)
{
	tsk_rt(t)->tot_exec_time += tsk_rt(t)->job_params.exec_time;

	/* prepare next release */
	tsk_rt(t)->job_params.release   = tsk_rt(t)->job_params.deadline;
	tsk_rt(t)->job_params.deadline += get_rt_period(t);
	tsk_rt(t)->job_params.exec_time = 0;
	/* update job sequence number */
	tsk_rt(t)->job_params.job_no++;

	/* don't confuse Linux */
	t->rt.time_slice = 1;
}

void prepare_for_next_period(struct task_struct *t)
{
	BUG_ON(!t);

	/* Record lateness before we set up the next job's
	 * release and deadline. Lateness may be negative.
	 */
	t->rt_param.job_params.lateness =
		(long long)litmus_clock() - 
		(long long)t->rt_param.job_params.deadline;

	setup_release(t, get_release(t) + get_rt_period(t));
}

void release_at(struct task_struct *t, lt_t start)
{
	BUG_ON(!t);
	setup_release(t, start);
	set_rt_flags(t, RT_F_RUNNING);
}


/*
 *	Deactivate current task until the beginning of the next period.
 */
long complete_job(void)
{
	/* Mark that we do not excute anymore */
	set_rt_flags(current, RT_F_SLEEP);
	/* call schedule, this will return when a new job arrives
	 * it also takes care of preparing for the next release
	 */
	schedule();
	return 0;
}
