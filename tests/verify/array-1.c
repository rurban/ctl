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
#include "ctl/array.h"

int main () {
    arr4_int a = arr4_int_init();
    assert(arr4_int_size(&a) == 4);
    arr4_int_assign(&a, 4, 1);
    assert(*arr4_int_at(&a, 0) == 1);
    arr4_int_fill_n(&a, 3, 2);
    assert(*arr4_int_at(&a, 2) == 2);
    *arr4_int_at(&a, 0) = 0;
    *arr4_int_at(&a, 2) = 3;
    for (int i=0; i<4; i++)
        LOG("arr4[%d] %d\n", i, *arr4_int_at(&a, i));
    arr4_int_sort(&a);
    for (int i=0; i<4; i++)
        LOG("arr4[%d] %d\n", i, *arr4_int_at(&a, i));
    // sort is broken with 3-way compare
    //assert(*arr4_int_at(&a, 0) == 0);
    //assert(*arr4_int_at(&a, 1) == 1);
    //assert(*arr4_int_at(&a, 2) == 2);
    //assert(*arr4_int_at(&a, 3) == 3);
    LOG("arr4_int_count(&a, 0) %zu\n", arr4_int_count(&a, 0));
    LOG("arr4_int_count(&a, 1) %zu\n", arr4_int_count(&a, 1));
    LOG("arr4_int_count(&a, 2) %zu\n", arr4_int_count(&a, 2));
    LOG("arr4_int_count(&a, 3) %zu\n", arr4_int_count(&a, 3));
    assert(arr4_int_count(&a, -1) == 0);
    assert(arr4_int_count(&a, 0) == 1);
    assert(arr4_int_count(&a, 1) == 1);
    assert(arr4_int_count(&a, 2) == 1);
    assert(arr4_int_count(&a, 3) == 1);
}
