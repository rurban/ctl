/*
  cbmc --trace --unwind 6 -I. tests/verify/deq-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define POD
#define T int
#include "ctl/priority_queue.h"

int main () {
    pqu_int a = pqu_int_init(NULL);
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
    const int a3 = nondet_int();
    const int a4 = nondet_int();
    __CPROVER_assume(a1 != 0 && a2 != 0 && a3 != 0 && a4 != 0);
#else
    const int a1 = 1;
    const int a2 = 2;
    const int a3 = 3;
    const int a4 = 4;
#endif
    pqu_int_push(&a, a3);
    pqu_int_push(&a, 0);
    pqu_int_push(&a, a1);
    pqu_int_push(&a, a2);
    pqu_int_push(&a, a4);
    pqu_int_pop(&a);
    assert(a.size == 4);
    for(int i=0; i<4;i++)
        LOG("pqu[%d]: %d\n", i, a.vector[i]);
    assert(a.vector[0] == a3);
    assert(a.vector[1] == a2);
    assert(a.vector[2] == a1);
    assert(a.vector[3] == 0);
    pqu_int_free(&a);
}
