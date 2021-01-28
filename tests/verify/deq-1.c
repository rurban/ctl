/*
  cbmc --trace --unwind 12 -I. tests/verify/deq-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/deque.h"

int main () {
    deq_int a = deq_int_init();
    deq_int_push_front(&a, 0);
    deq_int_insert(&a, 0, 1);
    deq_int_insert(&a, 1, 0);
    deq_int_insert(&a, 2, 2);
    assert(a.size == 4);
    assert(*deq_int_at(&a, 0) == 1);
    deq_int_erase(&a, 1);
    deq_int_push_front(&a, 3);
    deq_int_push_back(&a, 4);
    assert(deq_int_count(&a, 0) == 1);
    assert(deq_int_count(&a, 1) == 1);
}
