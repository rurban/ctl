/* Functional tests for flat_map (C++23) and flat_multimap (C++23).
   Pure C assertion tests of the documented CTL contract.
   SPDX-License-Identifier: MIT */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* POD key/value pair, ordered by key only */
typedef struct
{
    int key;
    int value;
} intint;
static int intint_cmp(intint *a, intint *b)
{
    return a->key < b->key;
}
static int intint_eq(intint *a, intint *b)
{
    return a->key == b->key;
}
static intint kv(int k, int v)
{
    intint p;
    p.key = k;
    p.value = v;
    return p;
}

#define POD
#define NOT_INTEGRAL
#define T intint
#include <ctl/flat_map.h>

#define POD
#define NOT_INTEGRAL
#define T intint
#include <ctl/flat_multimap.h>

static void test_flat_map(void)
{
    fmap_intint m = fmap_intint_init(intint_cmp);
    m.equal = intint_eq;
    fmap_intint_insert(&m, kv(2, 20));
    fmap_intint_insert(&m, kv(1, 10));
    fmap_intint_insert(&m, kv(2, 999)); /* duplicate key ignored */
    assert(fmap_intint_size(&m) == 2);
    fmap_intint_it f = fmap_intint_find(&m, kv(2, 0));
    assert(!fmap_intint_it_done(&f) && f.ref->value == 20);
    /* insert_or_assign overwrites the mapped value */
    fmap_intint_insert_or_assign(&m, kv(2, 222));
    f = fmap_intint_find(&m, kv(2, 0));
    assert(f.ref->value == 222 && fmap_intint_size(&m) == 2);
    /* insert_or_assign of a new key inserts */
    int found = -1;
    fmap_intint_insert_or_assign_found(&m, kv(3, 30), &found);
    assert(found == 0 && fmap_intint_size(&m) == 3);
    fmap_intint_insert_or_assign_found(&m, kv(3, 33), &found);
    assert(found == 1 && fmap_intint_size(&m) == 3);
    /* keys stay sorted */
    int pk = -1;
    foreach (fmap_intint, &m, it)
    {
        assert(it.ref->key > pk);
        pk = it.ref->key;
    }
    assert(fmap_intint_contains(&m, kv(3, 0)));
    assert(fmap_intint_count(&m, kv(2, 0)) == 1);
    assert(fmap_intint_erase(&m, kv(1, 0)) == 1);
    assert(fmap_intint_size(&m) == 2);
    fmap_intint_free(&m);
}

static void test_flat_multimap(void)
{
    fmmap_intint m = fmmap_intint_init(intint_cmp);
    m.equal = intint_eq;
    fmmap_intint_insert(&m, kv(1, 10));
    fmmap_intint_insert(&m, kv(1, 11));
    fmmap_intint_insert(&m, kv(2, 20));
    fmmap_intint_insert(&m, kv(1, 12));
    assert(fmmap_intint_size(&m) == 4);
    assert(fmmap_intint_count(&m, kv(1, 0)) == 3);
    /* equal keys keep insertion order: 10, 11, 12 */
    fmmap_intint_it lo, hi;
    fmmap_intint_equal_range(&m, kv(1, 0), &lo, &hi);
    int expect[] = {10, 11, 12}, k = 0;
    for (fmmap_intint_it it = lo; it.ref != hi.ref; fmmap_intint_it_next(&it))
        assert(it.ref->value == expect[k++]);
    assert(k == 3);
    /* keys nondecreasing overall */
    int pk = -1;
    foreach (fmmap_intint, &m, it)
    {
        assert(it.ref->key >= pk);
        pk = it.ref->key;
    }
    assert(fmmap_intint_erase(&m, kv(1, 0)) == 3);
    assert(fmmap_intint_size(&m) == 1);
    fmmap_intint_free(&m);
}

int main(void)
{
    test_flat_map();
    test_flat_multimap();
    printf("%s: PASS\n", __FILE__);
    return 0;
}
