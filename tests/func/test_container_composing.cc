#include "../test.h"

#define POD
#define T int
#include <ctl/deque.h>

static inline deq_int deq_int_inc(deq_int* a) { return *a++; }

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

#define T deq_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/list.h>

static inline list_int list_int_inc(list_int* a) { return *a++; }

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

#define T list_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/forward_list.h>

static inline slist_int slist_int_inc(slist_int* a) { return *a++; }

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

#define T stack_int
#include <ctl/unordered_set.h>

#define POD
#define T int
#include <ctl/vector.h>

static inline vec_int vec_int_inc(vec_int* a) { return *a++; }

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

#define T vec_int
#include <ctl/unordered_set.h>

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

static inline arr128_int arr128_int_inc(arr128_int* a) { return *a++; }

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

#define T arr128_int
#include <ctl/unordered_set.h>

int main(void)
{
    TEST_PASS(__FILE__);
}
