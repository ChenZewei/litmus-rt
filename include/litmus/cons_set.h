#ifndef CONS_SET_H
#define CONS_SET_H

#include <linux/sched.h>
#include <litmus/debug_trace.h>

#define MAX_CT_BUFFER 32

typedef struct cons_queue {
  int length;
  struct task_struct* head;
  struct task_struct* tail;
} cons_queue;

static void cq_init(cons_queue* list) {
  list->length = 0;
  list->head = NULL;
  list->tail = NULL;
}

static int is_cq_exist(cons_queue* list, struct task_struct* task) {
  struct task_struct* curr = list->head;
  while (curr) {
    if (task == curr)
        return 1;
    curr = curr->cq_next;
  }
  return 0;
}

static void cq_enqueue(cons_queue* list, struct task_struct* task) {
  if (!task)
    return NULL;
  TRACE_TASK(task, "cq enqueue");
  if (!list->head) {
    task->cq_prev = NULL;
    task->cq_next = NULL;
    list->head = task;
    list->tail = task;
  } else {
    task->cq_next = NULL;
    task->cq_prev = list->tail;
    list->tail->cq_next = task;
    list->tail = task;
  }
  list->length++;
}

static struct task_struct* cq_dequeue(cons_queue* list) {
  struct task_struct* task = NULL;
  if (list->head) {
    task = list->head;
    list->length--;
    if (list->tail == list->head) {
      list->head = NULL;
      list->tail = NULL;
      task->cq_prev = NULL;
      task->cq_next = NULL;
      return task;
    } else {
      list->head = task->cq_next;
      task->cq_prev = NULL;
      task->cq_next = NULL;
      return task;
    }
  }
  TRACE_TASK(task, "cq dequeue");
  return task;
}

#endif