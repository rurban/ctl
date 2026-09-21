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
    swiss_int_int_free(&map);
}
