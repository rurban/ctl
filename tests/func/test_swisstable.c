#include <assert.h>
#include <stddef.h>
static size_t int_hash(int *key) { return (size_t)(unsigned)*key * 2654435761u; }
static int int_equal(int *left, int *right) { return *left == *right; }
#define POD
#define TK int
#define T int
#include <ctl/swisstable.h>
int main(void) {
    swiss_int_int map = swiss_int_int_init(int_hash, int_equal);
    for (int i = 0; i < 256; i++) assert(swiss_int_int_insert(&map, i, i * 2));
    assert(map.size == 256);
    for (int i = 0; i < 256; i++) assert(*swiss_int_int_find(&map, i) == i * 2);
    assert(!swiss_int_int_insert(&map, 4, 99));
    assert(*swiss_int_int_find(&map, 4) == 99);
    assert(swiss_int_int_erase(&map, 4));
    assert(!swiss_int_int_contains(&map, 4));

    assert(swiss_int_int_count(&map, 4) == 0);
    assert(swiss_int_int_count(&map, 5) == 1);

    swiss_int_int_it lo, hi;
    swiss_int_int_equal_range(&map, 5, &lo, &hi);
    assert(!swiss_int_int_it_done(&lo));
    assert(*swiss_int_int_it_key(&lo) == 5);
    assert(*swiss_int_int_it_ref(&lo) == 10);
    swiss_int_int_it_next(&lo);
    assert(lo.entry == hi.entry);

    swiss_int_int_equal_range(&map, 4, &lo, &hi);
    assert(swiss_int_int_it_done(&lo));
    assert(lo.entry == hi.entry);

    size_t seen = 0;
    for (swiss_int_int_it it = swiss_int_int_begin(&map); !swiss_int_int_it_done(&it); swiss_int_int_it_next(&it))
        seen++;
    assert(seen == map.size);

    swiss_int_int_clear(&map);
    assert(map.size == 0);
    assert(swiss_int_int_empty(&map));
    assert(swiss_int_int_find(&map, 5) == NULL);

    assert(swiss_int_int_reserve(&map, 1000));
    assert(map.capacity >= 1000);
    for (int i = 0; i < 500; i++) assert(swiss_int_int_insert(&map, i, i));
    assert(map.size == 500);

    swiss_int_int other = swiss_int_int_init(int_hash, int_equal);
    swiss_int_int_insert(&other, 999, 999);
    swiss_int_int_swap(&map, &other);
    assert(map.size == 1);
    assert(*swiss_int_int_find(&map, 999) == 999);
    assert(other.size == 500);
    swiss_int_int_free(&other);

    swiss_int_int_free(&map);
}
