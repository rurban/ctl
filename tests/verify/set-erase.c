/*
  cbmc --trace --function main -I. tests/verify/set-erase.c
*/
//#define USE_INTERNAL_VERIFY
#include <assert.h>

#define POD
#define T int
#include "ctl/set.h"

void check(set_int *a)
{
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
    const int a3 = nondet_int();
    __CPROVER_assume(a1 != 0 && a1 != a2 && a1 != a3 && a2 != a3);
#else
    const int a1 = 1;
    const int a2 = 2;
    const int a3 = 3;
#endif
    set_int_insert(a, a1);
    set_int_insert(a, 0);
    set_int_insert(a, a2);
    assert(a->size == 3);
    set_int_erase(a, a1);
    assert(a->size == 2);
    assert(set_int_count(a, 0) == 1);
    assert(set_int_count(a, a1) == 0);
    assert(set_int_count(a, a2) == 1);
    assert(set_int_count(a, a3) == 0);
    set_int_free(a);
}

int main()
{
    set_int a = set_int_init(_set_int__default_integral_compare);
    check(&a);
    a = set_int_init(_set_int__default_integral_compare3);
    check(&a);
}
