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
#define INCLUDE_ALGORITHM
#include "ctl/deque.h"

int main()
{
    deq_int a = deq_int_init();
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
    const int a3 = nondet_int();
    __CPROVER_assume(a1 != 0 && a1 != a2 && a1 != a3 && a2 != 0 && a3 != 0);
#else
    const int a1 = 1;
    const int a2 = 2;
    const int a3 = 3;
#endif
    deq_int_push_front(&a, 0);
    deq_int_it it = deq_int_begin(&a);
    deq_int_insert(&it, a1);
    deq_int_it_advance(&it, 1);
    deq_int_insert(&it, 0);
    deq_int_insert_index(&a, 2, a2);
    assert(a.size == 4);
    assert(*deq_int_at(&a, 0) == a1);
    deq_int_erase_index(&a, 1);
    deq_int_push_front(&a, a3);
    deq_int_push_back(&a, 4);
    assert(deq_int_count(&a, 0) == 1);
    assert(deq_int_count(&a, a1) == 1);
    deq_int_free(&a);
}
