/*
  cbmc --trace --unwind 6 -I. tests/verify/set-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define POD
#define T int
//#define INCLUDE_ALGORITHM
#include "ctl/set.h"

int main()
{
    set_int a = set_int_init(NULL);
    int found;
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
#else
    const int a1 = 1;
    const int a2 = 2;
#endif
    set_int_insert(&a, a1);
    set_int_insert_found(&a, a2, &found);
    assert(a.size == (found ? 1U : 2U));
    set_int_erase(&a, a2);
    assert(a.size == (found ? 0U : 1U));
    set_int_insert(&a, 3);
    set_int_insert(&a, 4);

    foreach(set_int, &a, it)
        LOG("%d\n", *it.ref);
    assert(set_int_count(&a, a1) >= 1);
    set_int_it pos = set_int_begin(&a);
    set_int_find_range(&pos, a1);
#ifdef CBMC
    pos->end = nondet_int();
#endif
    set_int_find_range(&pos, a1);
    set_int_erase_it(&pos);
    set_int_free(&a);
}
