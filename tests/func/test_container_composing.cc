#include "../test.h"

#define POD
#define T int
#include <ctl/deque.h>

#define T deq_int
#include <ctl/list.h>

#define T deq_int
#include <ctl/forward_list.h>

#define T deq_int
#include <ctl/priority_queue.h>

#define T deq_int
#include <ctl/queue.h>

#define T deq_int
#include <ctl/set.h>

#define T deq_int
#include <ctl/stack.h>

#define T deq_int
#include <ctl/vector.h>

static inline size_t
deq_int_hash(deq_int* a)
{
    return (size_t)ctl_int32_hash((uint32_t)*deq_int_front(a));
}

#define T deq_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/list.h>

#define T list_int
#include <ctl/forward_list.h>

#define T list_int
#include <ctl/priority_queue.h>

#define T list_int
#include <ctl/queue.h>

#define T list_int
#include <ctl/set.h>

#define T list_int
#include <ctl/stack.h>

#define T list_int
#include <ctl/vector.h>

#define T list_int
#include <ctl/deque.h>

static inline size_t
list_int_hash(list_int* a)
{
    return a->head ? (size_t)ctl_int32_hash((uint32_t)*list_int_front(a)) : 0;
}
#define T list_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/forward_list.h>

#define T slist_int
#include <ctl/list.h>

#define T slist_int
#include <ctl/priority_queue.h>

#define T slist_int
#include <ctl/queue.h>

#define T slist_int
#include <ctl/set.h>

#define T slist_int
#include <ctl/stack.h>

#define T slist_int
#include <ctl/vector.h>

#define T slist_int
#include <ctl/deque.h>

static inline size_t
slist_int_hash(slist_int* a)
{
    return a->head ? (size_t)ctl_int32_hash((uint32_t)*slist_int_front(a)) : 0;
}
#define T slist_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/priority_queue.h>

#define T pqu_int
#include <ctl/queue.h>

#define T pqu_int
#include <ctl/set.h>

#define T pqu_int
#include <ctl/stack.h>

#define T pqu_int
#include <ctl/vector.h>

#define T pqu_int
#include <ctl/deque.h>

#define T pqu_int
#include <ctl/list.h>

#define T pqu_int
#include <ctl/forward_list.h>

static inline size_t
pqu_int_hash(pqu_int* a)
{
    return a->size ? (size_t)ctl_int32_hash((uint32_t)*pqu_int_top(a)) : 0;
}
#define T pqu_int
#include <ctl/unordered_set.h>

// already defined by test.h
//#define POD
//#define T int
//#include <ctl/queue.h>

#define T queue_int
#include <ctl/set.h>

#define T queue_int
#include <ctl/stack.h>

#define T queue_int
#include <ctl/vector.h>

#define T queue_int
#include <ctl/deque.h>

#define T queue_int
#include <ctl/list.h>

#define T queue_int
#include <ctl/forward_list.h>

#define T queue_int
#include <ctl/priority_queue.h>

static inline size_t
queue_int_hash(queue_int* a)
{
    return a->size ? (size_t)ctl_int32_hash((uint32_t)*queue_int_front(a)) : 0;
}
#define T queue_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/set.h>

#define T set_int
#include <ctl/stack.h>

#define T set_int
#include <ctl/vector.h>

#define T set_int
#include <ctl/deque.h>

#define T set_int
#include <ctl/list.h>

#define T set_int
#include <ctl/forward_list.h>

#define T set_int
#include <ctl/priority_queue.h>

#define T set_int
#include <ctl/queue.h>

static inline size_t
set_int_hash(set_int* a)
{
    set_int_node *node = set_int_first(a);
    return a->size ? (size_t)ctl_int32_hash((uint32_t)node->value) : 0;
}
#define T set_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/stack.h>

#define T stack_int
#include <ctl/vector.h>

#define T stack_int
#include <ctl/deque.h>

#define T stack_int
#include <ctl/list.h>

#define T stack_int
#include <ctl/forward_list.h>

#define T stack_int
#include <ctl/priority_queue.h>

#define T stack_int
#include <ctl/queue.h>

#define T stack_int
#include <ctl/set.h>

static inline size_t
stack_int_hash(stack_int* a)
{
    return a->size ? (size_t)ctl_int32_hash((uint32_t)*stack_int_top(a)) : 0;
}
#define T stack_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/vector.h>

#define T vec_int
#include <ctl/deque.h>

#define T vec_int
#include <ctl/list.h>

#define T vec_int
#include <ctl/forward_list.h>

#define T vec_int
#include <ctl/priority_queue.h>

#define T vec_int
#include <ctl/queue.h>

#define T vec_int
#include <ctl/set.h>

#define T vec_int
#include <ctl/stack.h>

static inline size_t
vec_int_hash(vec_int* a)
{
    return a->size ? (size_t)ctl_int32_hash((uint32_t)*vec_int_front(a)) : 0;
}
#define T vec_int
#include <ctl/unordered_set.h>

static inline size_t int_hash(int *a)
{
    return (size_t)ctl_int32_hash((uint32_t)*a);
}
#define POD
#define T int
#include <ctl/unordered_set.h>

#define T uset_int
#include <ctl/deque.h>

#define T uset_int
#include <ctl/list.h>

#define T uset_int
#include <ctl/forward_list.h>

#define T uset_int
#include <ctl/priority_queue.h>

#define T uset_int
#include <ctl/queue.h>

#define T uset_int
#include <ctl/set.h>

#define T uset_int
#include <ctl/stack.h>

#define POD
#define N 128
#define T int
#include <ctl/array.h>

#define T arr128_int
#include <ctl/stack.h>

#define T arr128_int
#include <ctl/vector.h>

#define T arr128_int
#include <ctl/deque.h>

#define T arr128_int
#include <ctl/list.h>

#define T arr128_int
#include <ctl/forward_list.h>

#define T arr128_int
#include <ctl/priority_queue.h>

#define T arr128_int
#include <ctl/queue.h>

#define T arr128_int
#include <ctl/set.h>

static inline size_t
arr128_int_hash(arr128_int* a)
{
    return (size_t)ctl_int32_hash((uint32_t)*arr128_int_front(a));
}
#define T arr128_int
#include <ctl/unordered_set.h>

int main(void)
{
    TEST_PASS(__FILE__);
}
