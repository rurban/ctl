/*
  cbmc --trace --unwind 12 -I. tests/verify/list-1.c
*/
#ifdef DEBUG
#include <stdio.h>
#endif
#include <assert.h>

#define POD
#define T int
#include "ctl/list.h"

int main () {
    list_int a = list_int_init();
    list_int_push_back(&a, 1);
    list_int_push_back(&a, 2);
    list_int_push_back(&a, 3);
    list_int_push_back(&a, 4);
    list_int_push_front(&a, 0);
    assert(a.size == 5);
    list_int_pop_back(&a);
    list_int_pop_front(&a);
    assert(a.size == 3);
    list_int_reverse(&a);
    list_int_erase(&a, list_int_begin(&a));
    list_int_push_front(&a, 3);
    list_int_push_back(&a, 4);

    //foreach(list_int, &a, it)
    //    LOG("%d\n", *it.ref);
    list_int_sort(&a);
    assert(*list_int_front(&a) == 1);
    assert(*list_int_back(&a) == 4);
    //foreach(list_int, &a, it)
    //    LOG("%d\n", *it.ref);

    assert(list_int_count(&a, 0) == 0);
    assert(list_int_count(&a, 1) == 1);
    list_int_free(&a);
}
