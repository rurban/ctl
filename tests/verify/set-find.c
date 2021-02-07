/* 
  cbmc --compact-trace --depth 6 --unwind 6 --function main -I. tests/verify/set-find.c
*/
//#define USE_INTERNAL_VERIFY
#include <assert.h>

#define POD
#define T int
#include "ctl/set.h"

int main () {
    set_int a = set_int_init(NULL);
    set_int_insert(&a, 0);
    set_int_insert(&a, 1);
    assert(a.size == 2);
    assert(set_int_count(&a, -1) == 0);
    assert(set_int_count(&a, 0) == 1);
    assert(set_int_count(&a, 1) == 1);
    assert(set_int_count(&a, 2) == 0);
    set_int_free(&a);
}

/* See tests/verify/set-find.cbmc* */
