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
    pqu_int_push(&a, 3);
    pqu_int_push(&a, 0);
    pqu_int_push(&a, 1);
    pqu_int_push(&a, 2);
    pqu_int_push(&a, 4);
    pqu_int_pop(&a);
    assert(a.size == 4);
    for(int i=0; i<4;i++)
        LOG("pqu[%d]: %d\n", i, a.vector[i]);
    assert(a.vector[0] == 3);
    assert(a.vector[1] == 2);
    assert(a.vector[2] == 1);
    assert(a.vector[3] == 0);
    pqu_int_free(&a);
}
