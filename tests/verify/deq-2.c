/*
  cbmc --trace --unwind 6 -I. tests/verify/deq-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define DEQ_BUCKET_SIZE 4
#define POD
#define T int
#include "ctl/deque.h"

int main () {
    deq_int a = deq_int_init();
    deq_int_push_front(&a, 0);
    deq_int_it it = deq_int_begin(&a);
    deq_int_insert(&it, 1);
    deq_int_it_advance (&it, 1);
    deq_int_insert(&it, 0);
    deq_int_insert_index(&a, 2, 2);
    assert(a.size == 4);
    assert(*deq_int_at(&a, 0) == 1);
    deq_int_erase_index(&a, 1);
    deq_int_push_front(&a, 3);
    deq_int_push_back(&a, 4);
    assert(deq_int_count(&a, 0) == 1);
    assert(deq_int_count(&a, 1) == 1);
    deq_int_free(&a);
}
