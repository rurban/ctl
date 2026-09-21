/* Functional tests for hive (C++26): unordered container with stable element
   addresses that reuses the memory of erased elements.  Pure C assertion tests.
   SPDX-License-Identifier: MIT */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CTL_HIVE_BLOCK 8
#define POD
#define T int
#include <ctl/hive.h>

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
static int own_eq(own *a, own *b)
{
    return strcmp(a->s, b->s) == 0;
}

#define T own
#include <ctl/hive.h>

static int is_odd(int *a)
{
    return (*a % 2) != 0;
}

static void test_pod(void)
{
    hive_int h = hive_int_init();
    assert(hive_int_empty(&h));
    /* insert past a single block (cap 8) to force multiple blocks */
    hive_int_it it[100];
    for (int i = 0; i < 100; i++)
        it[i] = hive_int_insert(&h, i);
    assert(hive_int_size(&h) == 100);
    assert(hive_int_capacity(&h) >= 100);
    /* stable addresses: recorded refs still point at the right values */
    for (int i = 0; i < 100; i++)
        assert(*it[i].ref == i);
    /* iteration visits every element exactly once */
    long sum = 0;
    size_t cnt = 0;
    foreach (hive_int, &h, i)
    {
        sum += *i.ref;
        cnt++;
    }
    assert(cnt == 100 && sum == (99 * 100 / 2));
    /* a live element's address is unaffected by erasing others */
    int *p50 = it[50].ref;
    hive_int_erase_it(&it[10]);
    hive_int_erase_it(&it[20]);
    hive_int_erase_it(&it[30]);
    assert(hive_int_size(&h) == 97 && *p50 == 50);
    /* memory reuse: the next insert refills the most-recently-erased slot */
    void *reused = &it[30].block->data[it[30].index];
    hive_int_it n1 = hive_int_insert(&h, 1000);
    assert((void *)n1.ref == reused && hive_int_size(&h) == 98);
    /* lookup */
    assert(hive_int_contains(&h, 50));
    assert(!hive_int_contains(&h, 10)); /* erased */
    assert(hive_int_count(&h, 1000) == 1);
    /* remove_if */
    size_t before = hive_int_size(&h);
    size_t removed = hive_int_remove_if(&h, is_odd);
    assert(hive_int_size(&h) == before - removed);
    foreach (hive_int, &h, i)
        assert((*i.ref % 2) == 0);
    /* copy preserves contents */
    hive_int c = hive_int_copy(&h);
    long s1 = 0, s2 = 0;
    foreach (hive_int, &h, i)
        s1 += *i.ref;
    foreach (hive_int, &c, i)
        s2 += *i.ref;
    assert(hive_int_size(&c) == hive_int_size(&h) && s1 == s2);
    /* clear + reuse the container */
    hive_int_clear(&h);
    assert(hive_int_empty(&h));
    hive_int_insert(&h, 7);
    assert(hive_int_size(&h) == 1);
    hive_int_free(&h);
    hive_int_free(&c);
}

static void test_own(void)
{
    hive_own h = hive_own_init();
    h.equal = own_eq;
    const char *w[] = {"pear", "apple", "pear", "fig", "apple", "kiwi"};
    hive_own_it it[6];
    for (int i = 0; i < 6; i++)
        it[i] = hive_own_insert(&h, own_make(w[i]));
    assert(hive_own_size(&h) == 6);
    hive_own_erase_it(&it[2]);
    assert(hive_own_size(&h) == 5);
    /* reuse the freed slot with a new owning element */
    hive_own_insert(&h, own_make("date"));
    assert(hive_own_size(&h) == 6);
    hive_own c = hive_own_copy(&h);
    assert(hive_own_size(&c) == hive_own_size(&h));
    hive_own_free(&h);
    hive_own_free(&c);
}

int main(void)
{
    test_pod();
    test_own();
    printf("%s: PASS\n", __FILE__);
    return 0;
}
