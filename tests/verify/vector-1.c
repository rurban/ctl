/*
  cbmc --trace --unwind 12 -I. tests/verify/vector-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/vector.h"

int main () {
    vec_int a = vec_int_init();
    vec_int_push_back(&a, 1);
    vec_int_push_back(&a, 2);
    vec_int_push_back(&a, 3);
    vec_int_push_back(&a, 4);
    assert(a.size == 4);
    vec_int_pop_back(&a);
    assert(a.size == 3);
    vec_int_insert(&a, 2, 0);
    vec_int_erase(&a, 1);
    vec_int_push_back(&a, 3);
    vec_int_push_back(&a, 4);
    //vec_int_sort(&a); => vector-2.c
    assert(vec_int_count(&a, 0) == 1);
    assert(vec_int_count(&a, 1) == 1);
    vec_int_free(&a);
}
