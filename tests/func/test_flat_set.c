/* Functional tests for flat_set (C++23) and flat_multiset (C++23).
   Pure C assertion tests: the C++23 <flat_set> is not universally available,
   so we verify the documented CTL contract directly.
   SPDX-License-Identifier: MIT */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* POD int instantiations */
#define POD
#define T int
#include <ctl/flat_set.h>

#define POD
#define T int
#include <ctl/flat_multiset.h>

/* non-POD, heap-owning key to exercise free/copy ownership */
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
static int own_eq(own *a, own *b)
{
    return strcmp(a->s, b->s) == 0;
}
static own key(const char *s)
{
    own o;
    o.s = (char *)s; /* borrowed literal, never freed by lookups */
    return o;
}

#define T own
#include <ctl/flat_set.h>

#define T own
#include <ctl/flat_multiset.h>

static void test_flat_set_int(void)
{
    fset_int a = fset_int_init(NULL); /* default integral compare */
    int v[] = {5, 3, 8, 3, 1, 9, 5, 2};
    for (size_t i = 0; i < sizeof(v) / sizeof(*v); i++)
        fset_int_insert(&a, v[i]);
    /* unique + sorted: 1 2 3 5 8 9 */
    assert(fset_int_size(&a) == 6);
    int prev = -1;
    size_t n = 0;
    foreach (fset_int, &a, it)
    {
        assert(*it.ref > prev);
        prev = *it.ref;
        n++;
    }
    assert(n == 6);
    /* random access via inherited at() */
    assert(*fset_int_at(&a, 0) == 1 && *fset_int_at(&a, 5) == 9);
    /* lookup */
    assert(fset_int_contains(&a, 8));
    assert(!fset_int_contains(&a, 7));
    assert(fset_int_count(&a, 3) == 1);
    fset_int_it lb = fset_int_lower_bound(&a, 3);
    assert(*lb.ref == 3);
    fset_int_it ub = fset_int_upper_bound(&a, 3);
    assert(*ub.ref == 5);
    fset_int_it f = fset_int_find(&a, 8);
    assert(!fset_int_it_done(&f) && *f.ref == 8);
    f = fset_int_find(&a, 100);
    assert(fset_int_it_done(&f));
    /* insert_found reports duplicate */
    int found = -1;
    fset_int_insert_found(&a, 3, &found);
    assert(found == 1 && fset_int_size(&a) == 6);
    fset_int_insert_found(&a, 4, &found);
    assert(found == 0 && fset_int_size(&a) == 7);
    /* erase by key and by iterator */
    assert(fset_int_erase(&a, 3) == 1);
    assert(!fset_int_contains(&a, 3));
    fset_int_it f9 = fset_int_find(&a, 9);
    fset_int_erase_it(&f9);
    assert(!fset_int_contains(&a, 9));
    /* copy + equal */
    fset_int b = fset_int_copy(&a);
    assert(fset_int_equal(&a, &b));
    fset_int_free(&a);
    fset_int_free(&b);
}

static void test_flat_multiset_int(void)
{
    fmset_int m = fmset_int_init(NULL);
    int v[] = {5, 3, 8, 3, 1, 3, 5};
    for (size_t i = 0; i < sizeof(v) / sizeof(*v); i++)
        fmset_int_insert(&m, v[i]);
    assert(fmset_int_size(&m) == 7);
    assert(fmset_int_count(&m, 3) == 3);
    assert(fmset_int_count(&m, 5) == 2);
    assert(fmset_int_count(&m, 42) == 0);
    /* nondecreasing order */
    int prev = -1;
    foreach (fmset_int, &m, it)
    {
        assert(*it.ref >= prev);
        prev = *it.ref;
    }
    /* equal_range spans exactly the equal run */
    fmset_int_it lo, hi;
    fmset_int_equal_range(&m, 3, &lo, &hi);
    size_t c = 0;
    for (fmset_int_it it = lo; it.ref != hi.ref; fmset_int_it_next(&it))
    {
        assert(*it.ref == 3);
        c++;
    }
    assert(c == 3);
    /* erase removes every equal element */
    assert(fmset_int_erase(&m, 3) == 3);
    assert(fmset_int_count(&m, 3) == 0 && fmset_int_size(&m) == 4);
    fmset_int_free(&m);
}

static void test_flat_set_own(void)
{
    fset_own a = fset_own_init(own_cmp);
    a.equal = own_eq;
    const char *w[] = {"pear", "apple", "pear", "fig", "apple", "kiwi"};
    for (int i = 0; i < 6; i++)
        fset_own_insert(&a, own_make(w[i]));
    /* unique: apple fig kiwi pear */
    assert(fset_own_size(&a) == 4);
    assert(fset_own_contains(&a, key("fig")));
    assert(!fset_own_contains(&a, key("plum")));
    /* sorted */
    const char *prev = "";
    foreach (fset_own, &a, it)
    {
        assert(strcmp(it.ref->s, prev) > 0);
        prev = it.ref->s;
    }
    assert(fset_own_erase(&a, key("apple")) == 1);
    assert(fset_own_size(&a) == 3);
    fset_own b = fset_own_copy(&a);
    assert(fset_own_size(&b) == 3 && fset_own_equal(&a, &b));
    fset_own_free(&a);
    fset_own_free(&b);
}

static void test_flat_multiset_own(void)
{
    fmset_own m = fmset_own_init(own_cmp);
    m.equal = own_eq;
    const char *w[] = {"pear", "apple", "pear", "fig", "apple", "kiwi"};
    for (int i = 0; i < 6; i++)
        fmset_own_insert(&m, own_make(w[i]));
    assert(fmset_own_size(&m) == 6);
    assert(fmset_own_count(&m, key("pear")) == 2);
    assert(fmset_own_erase(&m, key("pear")) == 2);
    assert(fmset_own_size(&m) == 4);
    fmset_own_free(&m);
}

int main(void)
{
    test_flat_set_int();
    test_flat_multiset_int();
    test_flat_set_own();
    test_flat_multiset_own();
    printf("%s: PASS\n", __FILE__);
    return 0;
}
