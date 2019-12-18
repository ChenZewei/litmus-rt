#ifndef PARALLEL_DEGREE_H
#define PARALLEL_DEGREE_H

#define MAX_INT 0xffffffff
#define MAX_STACK_NUM 256

typedef struct pd_node {
  int tgid;
  int t_num;
  int active_num;
  struct pd_node* prev;
  struct pd_node* next;
} pd_node;

typedef struct pd_list {
  pd_node* head;
  pd_node* tail;
  int length;
} pd_list;

static void pd_node_init(pd_node* node) {
  node->tgid = MAX_INT;
  node->t_num = 0;
  node->active_num = 0;
  node->prev = NULL;
  node->next = NULL;
}

static void pd_stack_init(pd_node* pd_stack) {
  int i;
  for (i = 0; i < MAX_STACK_NUM; i++) {
    pd_node_init(&pd_stack[i]);
  }
}

static void pd_list_init(pd_list* list) {
  list->head = NULL;
  list->tail = NULL;
  list->length = 0;
}


static pd_node* get_node_in_stack(pd_node* pd_stack) {
  int i;
  for (i = 0; i < MAX_STACK_NUM; i++) {
    if (MAX_INT == pd_stack[i].tgid)
      return &pd_stack[i];
  }
  return NULL;
}

static pd_node* find_pd_node_in_stack(pd_node* pd_stack, int tgid) {
  int i;
  for (i = 0; i < MAX_STACK_NUM; i++) {
    if (tgid == pd_stack[i].tgid)
      return &pd_stack[i];
  }
  return NULL;
}


static pd_node* find_pd_node_in_list(pd_list* list, int tgid) {
  pd_node* curr = list->head;
  while (curr) {
    if (tgid == curr->tgid)
        return curr;
    curr = curr->next;
  }
  return NULL;
}

static void pd_list_append(pd_list* list, pd_node* node) {
  if (0 == list->length) {
    node->prev = NULL;
    node->next = NULL;
    list->head = node;
    list->tail = node;
  } else {
    node->next = NULL;
    node->prev = list->tail;
    list->tail->next = node;
    list->tail = node;
  }
  list->length++;
}

static void pd_list_remove(pd_list* list, pd_node* node) {
  if (node) {
    if (node->prev)  // not a head
      node->prev->next = node->next;
    else {  // is head
      list->head = node->next;
    }
    if (node->next)  // not a tail
      node->next->prev = node->prev;
    else {  // is tail
      list->tail = node->prev;
    }
    list->length--;
    pd_node_init(node);
  }
}

static void pd_task_release(pd_list* list, pd_node* pd_stack, int tgid) {
  pd_node* node = find_pd_node_in_list(list, tgid);
  if (node) {
    node->t_num++;
    return NULL;
  }
  node = find_pd_node_in_stack(pd_stack, tgid);
  if (!node) {
    node = get_node_in_stack(pd_stack);
    if (!node)
      return NULL;
    node->tgid = tgid;
    node->t_num++;
  }
  pd_list_append(list, node);
}

static void pd_task_exit(pd_list* list, int tgid) {
  pd_node* node = find_pd_node_in_list(list, tgid);
  if (node) {
    if (1 < node->t_num)
      node->t_num--;
    else
      pd_list_remove(list, node);
  }
}

static void pd_add(pd_list* list, int tgid) {
  pd_node* node = find_pd_node_in_list(list, tgid);
  if (node) {
    node->active_num++;
  }
}

static void pd_sub(pd_list* list, int tgid) {
  pd_node* node = find_pd_node_in_list(list, tgid);
  if (node) {
    node->active_num--;
  }
}

static int get_active_num(pd_list* list, int tgid) {
  pd_node* node = find_pd_node_in_list(list, tgid);
  if (node)
    return node->active_num;
  else
    return 0;
}


#endif