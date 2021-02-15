/*
  cbmc --trace --unwind 4 -I. tests/verify/uset-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/unordered_set.h"

int main()
{
    uset_int a = uset_int_init(NULL, NULL);
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
    const int a3 = nondet_int();
    const int a4 = nondet_int();
    __CPROVER_assume(a1 != 0 && a2 != 0 && a3 != 0 && a4 != 0);
    __CPROVER_assume(a1 != a2 && a2 != a3 && a3 != a4 && a2 != a4 && a1 != a4);
#else
    const int a1 = 1;
    const int a2 = 2;
    const int a3 = 3;
    const int a4 = 4;
#endif
    uset_int_insert(&a, a1);
    uset_int_insert(&a, a2);
    uset_int_insert(&a, a3);
    uset_int_insert(&a, a4);
    assert(a.size == 4);
    uset_int_erase(&a, a2);
    assert(a.size == 3);
    assert(uset_int_count(&a, a2) == 0);
    assert(uset_int_count(&a, a3) == 1);
    uset_int_insert(&a, a2);
    uset_int_erase(&a, a3);
    assert(uset_int_count(&a, 0) == 0);
    assert(uset_int_count(&a, a1) == 1);
    assert(uset_int_count(&a, a2) == 1);
    assert(uset_int_count(&a, a3) == 0);
    assert(uset_int_count(&a, a4) == 1);
    uset_int_free(&a);
}
