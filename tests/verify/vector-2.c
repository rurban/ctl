/*
  cbmc --trace --unwind 12 -I. tests/verify/vector-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/vector.h"

int main()
{
    vec_int a = vec_int_init();
    vec_int_push_back(&a, 4);
    vec_int_push_back(&a, 1);
    vec_int_push_back(&a, 3);
    vec_int_push_back(&a, 2);
    assert(a.size == 4);
    vec_int_sort(&a);
    assert(a.vector[0] == 1);
    assert(a.vector[1] == 2);
    assert(a.vector[2] == 3);
    assert(a.vector[3] == 4);
    vec_int_free(&a);
}
