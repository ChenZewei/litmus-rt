#include <linux/module.h>
#include <litmus/preempt.h>
#include <litmus/sched_plugin.h>

#include <litmus/debug_trace.h>
#include <linux/sched.h>
#include <litmus/edf_common.h>
#include <litmus/rt_domain.h>


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

static struct task_struct* cgedf_schedule(struct task_struct * prev)
{
        /* This mandatory. It triggers a transition in the LITMUS^RT remote
         * preemption state machine. Call this AFTER the plugin has made a local
         * scheduling decision.
         */
        sched_state_task_picked();

        /* We don't schedule anything for now. NULL means "schedule background work". */
        return NULL;
}

static long cgedf_admit_task(struct task_struct *tsk)
{
  TRACE_TASK(tsk, "The task was rejected by the cg-edf scheduling plugin.\n");
  /* Reject every task. */
  return -EINVAL;
}

static long cgedf_activate_plugin(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&cgedf_cpu_heap);
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

static struct sched_plugin cgedf_plugin = {
  .plugin_name            = "CG-EDF",
  .schedule               = cgedf_schedule,
  .admit_task             = cgedf_admit_task,
};

static int __init init_cgedf(void)
{
  return register_sched_plugin(&cgedf_plugin);
}

module_init(init_cgedf);
