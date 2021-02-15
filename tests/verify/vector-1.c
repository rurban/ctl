/*
  cbmc --trace --unwind 6 -I. tests/verify/vector-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/vector.h"

int main()
{
    vec_int a = vec_int_init();
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
    vec_int_push_back(&a, a1);
    vec_int_push_back(&a, a2);
    vec_int_push_back(&a, a3);
    vec_int_push_back(&a, a4);
    assert(a.size == 4);
    vec_int_pop_back(&a);
    assert(a.size == 3);
    vec_int_it p2 = vec_int_begin(&a);
    vec_int_it_advance(&p2, 2);
    vec_int_insert(&p2, 0);
    vec_int_erase_index(&a, 1);
    vec_int_push_back(&a, a3);
    vec_int_push_back(&a, a4);
    // vec_int_sort(&a); => vector-2.c
    assert(vec_int_count(&a, 0) == 1);
    assert(vec_int_count(&a, a1) >= 1);
    vec_int_free(&a);
}
