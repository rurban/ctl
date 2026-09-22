#include <assert.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
typedef char *charp;

#define POD
#define TK int
#define T int
#include <ctl/hashmap.h>

#define POD
#define TK charp
#define T int
#include <ctl/hashmap.h>

int main(void)
{
    // integral key: defaults to the stanford avalanche hash.
    hmap_int_int map = hmap_int_int_init();
    for (int i = 0; i < 256; i++)
        assert(hmap_int_int_insert(&map, i, i * 2));
    assert(map.size == 256);
    for (int i = 0; i < 256; i++)
        assert(*hmap_int_int_find(&map, i) == i * 2);
    assert(!hmap_int_int_insert(&map, 4, 99));
    assert(*hmap_int_int_find(&map, 4) == 99);
    assert(hmap_int_int_erase(&map, 4));
    assert(!hmap_int_int_contains(&map, 4));

    assert(hmap_int_int_count(&map, 4) == 0);
    assert(hmap_int_int_count(&map, 5) == 1);

    hmap_int_int_it lo, hi;
    hmap_int_int_equal_range(&map, 5, &lo, &hi);
    assert(!hmap_int_int_it_done(&lo));
    assert(*hmap_int_int_it_key(&lo) == 5);
    assert(*hmap_int_int_it_ref(&lo) == 10);
    hmap_int_int_it_next(&lo);
    assert(lo.entry == hi.entry);

    hmap_int_int_equal_range(&map, 4, &lo, &hi);
    assert(hmap_int_int_it_done(&lo));
    assert(lo.entry == hi.entry);

    size_t seen = 0;
    for (hmap_int_int_it it = hmap_int_int_begin(&map); !hmap_int_int_it_done(&it); hmap_int_int_it_next(&it))
        seen++;
    assert(seen == map.size);

    hmap_int_int_clear(&map);
    assert(map.size == 0);
    assert(hmap_int_int_empty(&map));
    assert(hmap_int_int_find(&map, 5) == NULL);

    assert(hmap_int_int_reserve(&map, 1000));
    assert(map.capacity >= 1000);
    for (int i = 0; i < 500; i++)
        assert(hmap_int_int_insert(&map, i, i));
    assert(map.size == 500);

    hmap_int_int other = hmap_int_int_init();
    hmap_int_int_insert(&other, 999, 999);
    hmap_int_int_swap(&map, &other);
    assert(map.size == 1);
    assert(*hmap_int_int_find(&map, 999) == 999);
    assert(other.size == 500);
    hmap_int_int_free(&other);

    assert(hmap_int_int_max_size() > 0);
    float lf = hmap_int_int_load_factor(&map);
    assert(lf > 0.0f && lf <= 1.0f);

    hmap_int_int cp = hmap_int_int_copy(&map);
    assert(cp.size == map.size);
    assert(*hmap_int_int_find(&cp, 999) == 999);
    assert(cp.entries != map.entries);
    assert(hmap_int_int_insert(&cp, 12345, 1));
    assert(cp.size == 2);
    assert(hmap_int_int_find(&map, 12345) == NULL);

    hmap_int_int_assign(&map, &cp);
    assert(map.size == 2);
    assert(hmap_int_int_contains(&map, 12345));
    assert(map.entries != cp.entries);
    hmap_int_int_free(&cp);

    hmap_int_int mlf = hmap_int_int_init();
    hmap_int_int_max_load_factor(&mlf, 0.5f);
    assert(mlf.max_load_factor == 0.5f);
    for (int i = 0; i < 4; i++)
        assert(hmap_int_int_insert(&mlf, i, i));
    assert(mlf.size == 4);
    assert(mlf.capacity == 16);
    hmap_int_int_free(&mlf);

    hmap_int_int_free(&map);

    // string key: defaults to wyhash + strcmp.
    hmap_charp_int smap = hmap_charp_int_init();
    char buf[256][16];
    for (int i = 0; i < 256; i++)
    {
        snprintf(buf[i], sizeof(buf[i]), "key%d", i);
        assert(hmap_charp_int_insert(&smap, buf[i], i));
    }
    assert(smap.size == 256);
    for (int i = 0; i < 256; i++)
        assert(*hmap_charp_int_find(&smap, buf[i]) == i);
    assert(!hmap_charp_int_insert(&smap, buf[4], 99));
    assert(*hmap_charp_int_find(&smap, buf[4]) == 99);
    assert(hmap_charp_int_erase(&smap, buf[4]));
    assert(!hmap_charp_int_contains(&smap, buf[4]));
    // distinct pointers, same contents: still found by value.
    char dup[16];
    strcpy(dup, buf[7]);
    assert(*hmap_charp_int_find(&smap, dup) == 7);
    assert(hmap_charp_int_count(&smap, dup) == 1);
    assert(hmap_charp_int_count(&smap, buf[4]) == 0);
    size_t sseen = 0;
    for (hmap_charp_int_it it = hmap_charp_int_begin(&smap); !hmap_charp_int_it_done(&it); hmap_charp_int_it_next(&it))
        sseen++;
    assert(sseen == smap.size);
    hmap_charp_int_clear(&smap);
    assert(hmap_charp_int_empty(&smap));
    hmap_charp_int_free(&smap);
}
