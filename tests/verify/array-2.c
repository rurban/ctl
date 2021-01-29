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
    a.vector[0] = 3;
    a.vector[1] = 0;
    a.vector[2] = 2;
    a.vector[3] = 1;
    arr4_int_sort(&a);
    for (int i=0; i<4; i++)
        LOG("arr4[%d] %d\n", i, *arr4_int_at(&a, i));
    // FIXME sort is broken with default 3-way compare, but works fine with 2-way
    assert(a.vector[0] == 0);
    assert(a.vector[1] == 1);
    assert(a.vector[2] == 2);
    assert(a.vector[3] == 3);
}
