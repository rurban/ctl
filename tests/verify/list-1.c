/*
  cbmc --trace --unwind 12 -I. tests/verify/list-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define POD
#define T int
#include "ctl/list.h"

int main()
{
    list_int a = list_int_init();
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
    list_int_push_back(&a, a1);
    list_int_push_back(&a, a2);
    list_int_push_back(&a, a3);
    list_int_push_back(&a, a4);
    list_int_push_front(&a, 0);
    assert(a.size == 5);
    list_int_pop_back(&a);
    list_int_pop_front(&a);
    assert(a.size == 3);
    list_int_reverse(&a);
    list_int_it pos = list_int_begin(&a);
    list_int_erase(&pos);
    list_int_push_front(&a, 3);
    list_int_push_back(&a, 4);

    // foreach(list_int, &a, it)
    //    LOG("%d\n", *it.ref);
    list_int_sort(&a);
    assert(*list_int_front(&a) == a1);
    assert(*list_int_back(&a) == 4);
    // foreach(list_int, &a, it)
    //    LOG("%d\n", *it.ref);
    assert(list_int_count(&a, 0) == 0);
    assert(list_int_count(&a, a1) >= 1);
    list_int_free(&a);
}
