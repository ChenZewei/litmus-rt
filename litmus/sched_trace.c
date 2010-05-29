/*
 * sched_trace.c -- record scheduling events to a byte stream.
 *
 * TODO: Move ring buffer to a lockfree implementation.
 */

#include <linux/spinlock.h>
#include <linux/fs.h>
#include <linux/cdev.h>
#include <linux/semaphore.h>
#include <asm/uaccess.h>
#include <linux/module.h>
#include <linux/sysrq.h>

#include <litmus/sched_trace.h>
#include <litmus/litmus.h>

typedef struct {
        /*	guard read and write pointers			*/
	spinlock_t 	lock;
	/*	guard against concurrent freeing of buffer 	*/
	rwlock_t	del_lock;

	/*	memory allocated for ring buffer		*/
	unsigned long	order;
	char*  		buf;
	char*		end;

	/*	Read/write pointer. May not cross.
	 *	They point to the position of next write and
	 *	last read.
	 */
	char* 		writep;
	char*		readp;

} ring_buffer_t;

#define EMPTY_RING_BUFFER {	\
	.lock     = SPIN_LOCK_UNLOCKED,		\
	.del_lock = RW_LOCK_UNLOCKED,  		\
	.buf      = NULL,      			\
	.end      = NULL,			\
	.writep   = NULL,			\
	.readp    = NULL			\
}

void rb_init(ring_buffer_t* buf)
{
	*buf = (ring_buffer_t) EMPTY_RING_BUFFER;
}

int rb_alloc_buf(ring_buffer_t* buf, unsigned long order)
{
	unsigned long flags;
	int error = 0;
	char *mem;

	/* do memory allocation while not atomic */
	mem = (char *) __get_free_pages(GFP_KERNEL, order);
	if (!mem)
		return -ENOMEM;
	write_lock_irqsave(&buf->del_lock, flags);
	BUG_ON(buf->buf);
	buf->buf = mem;
	buf->end = buf->buf + PAGE_SIZE * (1 << order) - 1;
	memset(buf->buf, 0xff, buf->end - buf->buf);
	buf->order = order;
	buf->writep = buf->buf + 1;
	buf->readp  = buf->buf;
	write_unlock_irqrestore(&buf->del_lock, flags);
	return error;
}

int rb_free_buf(ring_buffer_t* buf)
{
	unsigned long flags;
	int error = 0;
	write_lock_irqsave(&buf->del_lock, flags);
	BUG_ON(!buf->buf);
	free_pages((unsigned long) buf->buf, buf->order);
	buf->buf    = NULL;
	buf->end    = NULL;
	buf->writep = NULL;
	buf->readp  = NULL;
	write_unlock_irqrestore(&buf->del_lock, flags);
	return error;
}

/* Assumption: concurrent writes are serialized externally
 *
 * Will only succeed if there is enough space for all len bytes.
 */
int rb_put(ring_buffer_t* buf, char* mem, size_t len)
{
	unsigned long flags;
	char* r , *w;
	int error = 0;
	read_lock_irqsave(&buf->del_lock, flags);
	if (!buf->buf) {
		error = -ENODEV;
		goto out;
	}
	spin_lock(&buf->lock);
	r = buf->readp;
	w = buf->writep;
	spin_unlock(&buf->lock);
	if (r < w && buf->end - w >= len - 1) {
		/* easy case: there is enough space in the buffer
		 * to write it in one continous chunk*/
		memcpy(w, mem, len);
		w += len;
		if (w > buf->end)
			/* special case: fit exactly into buffer
			 * w is now buf->end + 1
			 */
			w = buf->buf;
	} else if (w < r && r - w >= len) { /* >= len because  may not cross */
		/* we are constrained by the read pointer but we there
		 * is enough space
		 */
		memcpy(w, mem, len);
		w += len;
	} else if (r <= w && buf->end - w < len - 1) {
		/* the wrap around case: there may or may not be space */
		if ((buf->end - w) + (r - buf->buf) >= len - 1) {
			/* copy chunk that fits at the end */
			memcpy(w, mem, buf->end - w + 1);
			mem += buf->end - w + 1;
			len -= (buf->end - w + 1);
			w = buf->buf;
			/* copy the rest */
			memcpy(w, mem, len);
			w += len;
		}
		else
			error = -ENOMEM;
	} else {
		error = -ENOMEM;
	}
	if (!error) {
		spin_lock(&buf->lock);
		buf->writep = w;
		spin_unlock(&buf->lock);
	}
 out:
	read_unlock_irqrestore(&buf->del_lock, flags);
	return error;
}

/* Assumption: concurrent reads are serialized externally */
int rb_get(ring_buffer_t* buf, char* mem, size_t len)
{
	unsigned long flags;
	char* r , *w;
	int error = 0;
	read_lock_irqsave(&buf->del_lock, flags);
	if (!buf->buf) {
		error = -ENODEV;
		goto out;
	}
	spin_lock(&buf->lock);
	r = buf->readp;
	w = buf->writep;
	spin_unlock(&buf->lock);

	if (w <= r && buf->end - r >= len) {
		/* easy case: there is enough data in the buffer
		 * to get it in one  chunk*/
		memcpy(mem, r + 1, len);
		r += len;
		error = len;

	} else if (r + 1 < w && w - r - 1 >= len) {
		/* we are constrained by the write pointer but
		 * there is enough data
		 */
		memcpy(mem, r + 1, len);
		r += len;
		error = len;

	} else if (r + 1 < w && w - r - 1 < len) {
		/* we are constrained by the write pointer and there
		 * there is not enough data
		 */
		memcpy(mem, r + 1, w - r - 1);
		error = w - r - 1;
		r    += w - r - 1;

	} else if (w <= r && buf->end - r < len) {
		/* the wrap around case: there may or may not be enough data
		 * first let's get what is available
		 */
		memcpy(mem, r + 1, buf->end - r);
		error += (buf->end - r);
		mem   += (buf->end - r);
		len   -= (buf->end - r);
		r     += (buf->end - r);

		if (w > buf->buf) {
			/* there is more to get */
			r = buf->buf - 1;
			if (w - r >= len) {
				/* plenty */
				memcpy(mem, r + 1, len);
				error += len;
				r     += len;
			} else {
				memcpy(mem, r + 1, w - r - 1);
				error += w - r - 1;
				r     += w - r - 1;
			}
		}
	} /* nothing available */

	if (error > 0) {
		spin_lock(&buf->lock);
		buf->readp = r;
		spin_unlock(&buf->lock);
	}
 out:
	read_unlock_irqrestore(&buf->del_lock, flags);
	return error;
}



/******************************************************************************/
/*                        DEVICE FILE DRIVER                                  */
/******************************************************************************/



/* Allocate a buffer of about 1 MB per CPU.
 *
 */
#define BUFFER_ORDER 8

typedef struct {
	ring_buffer_t 		buf;
	atomic_t		reader_cnt;
	struct semaphore	reader_mutex;
} trace_buffer_t;


/* This does not initialize the semaphore!! */

#define EMPTY_TRACE_BUFFER \
	{ .buf = EMPTY_RING_BUFFER, .reader_cnt = ATOMIC_INIT(0)}

static spinlock_t		log_buffer_lock = SPIN_LOCK_UNLOCKED;
static trace_buffer_t 		log_buffer = EMPTY_TRACE_BUFFER;

static void init_log_buffer(void)
{
	/* only initialize the mutex, the rest was initialized as part
	 * of the static initialization macro
	 */
	init_MUTEX(&log_buffer.reader_mutex);
}

static ssize_t log_read(struct file *filp, char __user *to, size_t len,
		      loff_t *f_pos)
{
	/* 	we ignore f_pos, this is strictly sequential */

	ssize_t error = -EINVAL;
	char*   mem;
	trace_buffer_t *buf = filp->private_data;

	if (down_interruptible(&buf->reader_mutex)) {
		error = -ERESTARTSYS;
		goto out;
	}

	if (len > 64 * 1024)
		len = 64 * 1024;
	mem = kmalloc(len, GFP_KERNEL);
	if (!mem) {
		error = -ENOMEM;
		goto out_unlock;
	}

	error = rb_get(&buf->buf, mem, len);
	while (!error) {
		set_current_state(TASK_INTERRUPTIBLE);
		schedule_timeout(110);
		if (signal_pending(current))
			error = -ERESTARTSYS;
		else
			error = rb_get(&buf->buf, mem, len);
	}

	if (error > 0 && copy_to_user(to, mem, error))
		error = -EFAULT;

	kfree(mem);
 out_unlock:
	up(&buf->reader_mutex);
 out:
	return error;
}

/* defined in kernel/printk.c */
extern int trace_override;
extern int trace_recurse;

/* log_open - open the global log message ring buffer.
 */
static int log_open(struct inode *in, struct file *filp)
{
	int error 		= -EINVAL;
	trace_buffer_t* buf;

	buf = &log_buffer;

	if (down_interruptible(&buf->reader_mutex)) {
		error = -ERESTARTSYS;
		goto out;
	}

	/*	first open must allocate buffers 	*/
	if (atomic_inc_return(&buf->reader_cnt) == 1) {
		if ((error = rb_alloc_buf(&buf->buf, BUFFER_ORDER)))
		{
			atomic_dec(&buf->reader_cnt);
			goto out_unlock;
		}
	}

	error = 0;
	filp->private_data = buf;
	printk(KERN_DEBUG "sched_trace buf: from 0x%p to 0x%p  length: %x\n",
	       buf->buf.buf, buf->buf.end,
	       (unsigned int) (buf->buf.end - buf->buf.buf));

	/* override printk() */
	trace_override++;

 out_unlock:
	up(&buf->reader_mutex);
 out:
	return error;
}

static int log_release(struct inode *in, struct file *filp)
{
	int error 		= -EINVAL;
	trace_buffer_t* buf 	= filp->private_data;

	BUG_ON(!filp->private_data);

	if (down_interruptible(&buf->reader_mutex)) {
		error = -ERESTARTSYS;
		goto out;
	}

	/*	last release must deallocate buffers 	*/
	if (atomic_dec_return(&buf->reader_cnt) == 0) {
		error = rb_free_buf(&buf->buf);
	}

	/* release printk() overriding */
	trace_override--;

	up(&buf->reader_mutex);
 out:
	return error;
}

/******************************************************************************/
/*                          Device Registration                               */
/******************************************************************************/

/* the major numbes are from the unassigned/local use block
 *
 * This should be converted to dynamic allocation at some point...
 */
#define LOG_MAJOR	251

/* log_fops  - The file operations for accessing the global LITMUS log message
 *             buffer.
 *
 * Except for opening the device file it uses the same operations as trace_fops.
 */
struct file_operations log_fops = {
	.owner   = THIS_MODULE,
	.open    = log_open,
	.release = log_release,
	.read    = log_read,
};

static int __init register_buffer_dev(const char* name,
				      struct file_operations* fops,
				      int major, int count)
{
	dev_t  trace_dev;
	struct cdev *cdev;
	int error = 0;

	trace_dev = MKDEV(major, 0);
	error     = register_chrdev_region(trace_dev, count, name);
	if (error)
	{
		printk(KERN_WARNING "sched trace: "
		       "Could not register major/minor number %d\n", major);
		return error;
	}
	cdev = cdev_alloc();
	if (!cdev) {
		printk(KERN_WARNING "sched trace: "
			"Could not get a cdev for %s.\n", name);
		return -ENOMEM;
	}
	cdev->owner = THIS_MODULE;
	cdev->ops   = fops;
	error = cdev_add(cdev, trace_dev, count);
	if (error) {
		printk(KERN_WARNING "sched trace: "
			"add_cdev failed for %s.\n", name);
		return -ENOMEM;
	}
	return error;

}

#ifdef CONFIG_MAGIC_SYSRQ

static void sysrq_dump_trace_buffer(int key, struct tty_struct *tty)
{
	dump_trace_buffer(100);
}

static struct sysrq_key_op sysrq_dump_trace_buffer_op = {
	.handler	= sysrq_dump_trace_buffer,
	.help_msg	= "dump-trace-buffer(Y)",
	.action_msg	= "writing content of TRACE() buffer",
};

#endif

static int __init init_sched_trace(void)
{
	printk("Initializing TRACE() device\n");
	init_log_buffer();

#ifdef CONFIG_MAGIC_SYSRQ
	/* offer some debugging help */
	if (!register_sysrq_key('y', &sysrq_dump_trace_buffer_op))
		printk("Registered dump-trace-buffer(Y) magic sysrq.\n");
	else
		printk("Could not register dump-trace-buffer(Y) magic sysrq.\n");
#endif


	return register_buffer_dev("litmus_log", &log_fops,
				   LOG_MAJOR, 1);
}

module_init(init_sched_trace);

#define MSG_SIZE 255
static DEFINE_PER_CPU(char[MSG_SIZE], fmt_buffer);

/* sched_trace_log_message - This is the only function that accesses the the
 *                           log buffer inside the kernel for writing.
 *                           Concurrent access to it is serialized via the
 *                           log_buffer_lock.
 *
 *                           The maximum length of a formatted message is 255.
 */
void sched_trace_log_message(const char* fmt, ...)
{
	unsigned long 	flags;
	va_list 	args;
	size_t		len;
	char*		buf;

	va_start(args, fmt);
	local_irq_save(flags);

	/* format message */
	buf = __get_cpu_var(fmt_buffer);
	len = vscnprintf(buf, MSG_SIZE, fmt, args);

	spin_lock(&log_buffer_lock);
	/* Don't copy the trailing null byte, we don't want null bytes
	 * in a text file.
	 */
	rb_put(&log_buffer.buf, buf, len);
	spin_unlock(&log_buffer_lock);

	local_irq_restore(flags);
	va_end(args);
}

void dump_trace_buffer(int max)
{
	char line[80];
	int len;
	int count = 0;

	/* potentially, but very unlikely race... */
	trace_recurse = 1;
	while ((max == 0 || count++ < max) &&
	       (len = rb_get(&log_buffer.buf, line, sizeof(line) - 1)) > 0) {
		line[len] = '\0';
		printk("%s", line);
	}
	trace_recurse = 0;
}
