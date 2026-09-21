/* Functional tests for inplace_vector (C++26): a resizable, fixed-capacity,
   inline (no-heap) contiguous array.  Pure C assertion tests.
   SPDX-License-Identifier: MIT */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define POD
#define N 8
#define T int
#include <ctl/inplace_vector.h>

/* non-POD, heap-owning element */
typedef struct
{
    char *s;
} own;
static char *sdup(const char *x)
{
    size_t n = strlen(x) + 1;
    char *p = (char *)malloc(n);
    memcpy(p, x, n);
    return p;
}
static own own_make(const char *x)
{
    own o;
    o.s = sdup(x);
    return o;
}
static void own_free(own *o)
{
    free(o->s);
    o->s = NULL;
}
static own own_copy(own *o)
{
    return own_make(o->s);
}
static int own_cmp(own *a, own *b)
{
    return strcmp(a->s, b->s) < 0;
}

#define N 4
#define T own
#include <ctl/inplace_vector.h>

static int is_even(int *a)
{
    return (*a % 2) == 0;
}

static void test_pod(void)
{
    inplace_vec8_int a = inplace_vec8_int_init();
    assert(inplace_vec8_int_capacity(&a) == 8);
    assert(inplace_vec8_int_max_size() == 8);
    assert(inplace_vec8_int_empty(&a));
    /* inline storage: object carries no heap pointer for the data */
    assert(sizeof(inplace_vec8_int) >= 8 * sizeof(int));
    for (int i = 0; i < 8; i++)
        inplace_vec8_int_push_back(&a, i);
    assert(inplace_vec8_int_size(&a) == 8);
    assert(*inplace_vec8_int_front(&a) == 0 && *inplace_vec8_int_back(&a) == 7);
    /* full: try_push_back fails without corrupting */
    assert(inplace_vec8_int_try_push_back(&a, 99) == NULL);
    assert(inplace_vec8_int_size(&a) == 8);
    /* contiguity */
    int *d = inplace_vec8_int_data(&a);
    for (int i = 0; i < 8; i++)
        assert(d[i] == i);
    /* erase front, insert front */
    inplace_vec8_int_erase_index(&a, 0);
    assert(inplace_vec8_int_size(&a) == 7 && *inplace_vec8_int_front(&a) == 1);
    inplace_vec8_int_insert_index(&a, 0, 42);
    assert(*inplace_vec8_int_front(&a) == 42 && inplace_vec8_int_size(&a) == 8);
    /* remove_if evens: {42,2,4,6} gone -> {1,3,5,7} */
    assert(inplace_vec8_int_remove_if(&a, is_even) == 4);
    assert(inplace_vec8_int_size(&a) == 4);
    /* sort */
    inplace_vec8_int_push_back(&a, 0);
    inplace_vec8_int_sort(&a);
    int prev = -1;
    foreach (inplace_vec8_int, &a, it)
    {
        assert(*it.ref > prev);
        prev = *it.ref;
    }
    inplace_vec8_int_it f = inplace_vec8_int_find(&a, 5);
    assert(!inplace_vec8_int_it_done(&f) && *f.ref == 5);
    /* copy + swap + resize */
    inplace_vec8_int b = inplace_vec8_int_copy(&a);
    assert(inplace_vec8_int_size(&b) == inplace_vec8_int_size(&a));
    inplace_vec8_int c = inplace_vec8_int_init();
    inplace_vec8_int_swap(&b, &c);
    assert(inplace_vec8_int_empty(&b) && inplace_vec8_int_size(&c) == 5);
    inplace_vec8_int_resize(&c, 2, 0);
    assert(inplace_vec8_int_size(&c) == 2);
    inplace_vec8_int_resize(&c, 8, 7);
    assert(inplace_vec8_int_size(&c) == 8 && *inplace_vec8_int_back(&c) == 7);
    inplace_vec8_int_free(&a);
    inplace_vec8_int_free(&b);
    inplace_vec8_int_free(&c);
}

static void test_own(void)
{
    inplace_vec4_own a = inplace_vec4_own_init();
    a.compare = own_cmp;
    const char *w[] = {"pear", "apple", "kiwi", "fig"};
    for (int i = 0; i < 4; i++)
        inplace_vec4_own_push_back(&a, own_make(w[i]));
    assert(inplace_vec4_own_size(&a) == 4);
    /* full */
    assert(inplace_vec4_own_try_push_back(&a, own_make("plum")) == NULL);
    inplace_vec4_own_sort(&a);
    assert(strcmp(inplace_vec4_own_front(&a)->s, "apple") == 0);
    inplace_vec4_own b = inplace_vec4_own_copy(&a);
    inplace_vec4_own_erase_index(&a, 0);
    assert(inplace_vec4_own_size(&a) == 3 && inplace_vec4_own_size(&b) == 4);
    inplace_vec4_own_free(&a);
    inplace_vec4_own_free(&b);
}

int main(void)
{
    test_pod();
    test_own();
    printf("%s: PASS\n", __FILE__);
    return 0;
}
