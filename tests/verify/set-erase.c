/* 
  cbmc --trace --function main -I. tests/verify/set-erase.c
*/
//#define USE_INTERNAL_VERIFY
#include <assert.h>

#define POD
#define T int
#include "ctl/set.h"

int main () {
    set_int a = set_int_init(NULL);
    set_int_insert(&a, 1);
    set_int_insert(&a, 0);
    set_int_insert(&a, 2);
    assert(a.size == 3);
    set_int_erase(&a, 1);
    assert(set_int_count(&a, 0) == 1);
    assert(set_int_count(&a, 1) == 0);
}
