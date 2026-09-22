# hashmap - CTL C Container Template library

Defined in **<ctl/hashmap.h>**. Same open-addressing design as
[swisstable](swisstable.md) (separate key `TK` and value `T` types,
generated prefix `hmap_TK_T`), but `init()` takes no arguments: the
hash/equal policy is chosen automatically from `TK`.

    #define POD
    #define TK int
    #define T int
    #include <ctl/hashmap.h>

    hmap_int_int map = hmap_int_int_init();
    hmap_int_int_insert(&map, 7, 42);

    typedef char *charp;
    #define POD
    #define TK charp
    #define T int
    #include <ctl/hashmap.h>

    hmap_charp_int names = hmap_charp_int_init();
    hmap_charp_int_insert(&names, "seven", 7);

## Default hash policy

* String keys (`TK` a single-token `char *` alias recognized by name:
  `charp`, `ucharp`, `cstr`, `str`, `string`, `cstring`, `u8ident`,
  `u8string`) get [wyhash](https://github.com/wangyi-fudan/wyhash) over
  the NUL-terminated bytes, and `strcmp` equality.
* Every other key defaults to the "stanford hash" avalanche mix (the
  Murmur3 finalizer from
  [stanford-futuredata/index-baselines](https://github.com/stanford-futuredata/index-baselines)'
  `hashing.cpp`, generalized to `size_t`), and `==` equality. This suits
  plain integers and other POD scalars.

Force one policy regardless of the detected spelling by defining
`CTL_HMAP_STRING_KEY` or `CTL_HMAP_INTEGRAL_KEY` before the include.
Struct keys, or keys needing a different hash entirely, bypass detection
with `_init_with`, or use [swisstable](swisstable.md) directly.

The initial implementation supports POD keys and values. It uses
power-of-two open addressing, grows at 75% load, and rehashes after
erase so probes always terminate at an unused entry. Pointers returned
by `find` are invalidated by insertion that grows the table and by
erase.

## API

    A init(void)
    A init_with(size_t hash(TK*), int equal(TK*, TK*))
    bool empty(A* self)
    size_t max_size(void)
    T* find(A* self, TK key)
    int contains(A* self, TK key)
    size_t count(A* self, TK key)
    void equal_range(A* self, TK key, I* lower, I* upper)
    bool insert(A* self, TK key, T value)
    bool erase(A* self, TK key)
    void clear(A* self)
    float load_factor(A* self)
    void max_load_factor(A* self, float factor)
    bool rehash(A* self, size_t bucket_count)
    bool reserve(A* self, size_t count)
    A copy(A* self)
    void assign(A* self, A* other)
    void swap(A* self, A* other)
    void free(A* self)

    I begin(A* self)
    I end(A* self)
    int it_done(I* it)
    void it_next(I* it)
    TK* it_key(I* it)
    T* it_ref(I* it)

`insert` returns true for a new key and false when it replaces an
existing value. Lookup and erase keys are borrowed. See
[swisstable](swisstable.md#api) for `equal_range`/`count`/`rehash`/
`reserve`/`swap`/iteration semantics — identical here.
