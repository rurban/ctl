/*
  cbmc --trace --unwind 6 -I. tests/verify/array-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define POD
#define T int
#define N 4
#define INCLUDE_ALGORITHM
#include "ctl/array.h"

int main()
{
    arr4_int a = arr4_int_init();
#ifdef CBMC
    const int a1 = nondet_int();
    const int a2 = nondet_int();
    const int a3 = nondet_int();
    __CPROVER_assume(a1 != 0 && a2 != 0 && a3 != 0);
#else
    const int a1 = 1;
    const int a2 = 2;
    const int a3 = 3;
#endif
    assert(arr4_int_size(&a) == 4);
    arr4_int_assign(&a, 4, a1);
    assert(*arr4_int_at(&a, 0) == a1);
    arr4_int_fill_n(&a, 3, a2);
    assert(*arr4_int_at(&a, 2) == a2);
    *arr4_int_at(&a, 0) = 0;
    *arr4_int_at(&a, 2) = a3;
    for (int i = 0; i < 4; i++)
        LOG("arr4[%d] %d\n", i, *arr4_int_at(&a, i));
    assert(a.vector[0] == 0);
    assert(a.vector[1] == a2);
    assert(a.vector[2] == a3);
    assert(a.vector[3] == a1);
    LOG("arr4_int_count(&a, 0) %zu\n", arr4_int_count(&a, 0));
    LOG("arr4_int_count(&a, 1) %zu\n", arr4_int_count(&a, a1));
    LOG("arr4_int_count(&a, 2) %zu\n", arr4_int_count(&a, a2));
    LOG("arr4_int_count(&a, 3) %zu\n", arr4_int_count(&a, a3));
    assert(arr4_int_count(&a, -1) == 0);
    assert(arr4_int_count(&a, 0) == 1);
    assert(arr4_int_count(&a, a1) >= 1);
    assert(arr4_int_count(&a, a2) >= 1);
    assert(arr4_int_count(&a, a3) >= 1);
}
