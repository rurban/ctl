/*
  cbmc --trace --unwind 4 -I. tests/verify/uset-1.c
*/
#include <assert.h>

#define POD
#define T int
#include "ctl/unordered_set.h"

int main () {
    uset_int a = uset_int_init(NULL, NULL);
    uset_int_insert(&a, 1);
    uset_int_insert(&a, 2);
    uset_int_insert(&a, 3);
    uset_int_insert(&a, 4);
    assert(a.size == 4);
    uset_int_erase(&a, 2);
    assert(a.size == 3);
    uset_int_insert(&a, 2);
    uset_int_erase(&a, 3);
    assert(uset_int_count(&a, 0) == 0);
    assert(uset_int_count(&a, 1) == 1);
}
