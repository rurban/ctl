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
    hmap_charp_int_free(&smap);
}
