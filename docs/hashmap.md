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

The initial implementation supports POD keys and values. It grows at 75%
load, and rehashes after erase so probes always terminate at an unused
entry. Pointers returned by `find` are invalidated by insertion that
grows the table and by erase.

## Growth, cached-hash and security policy

Same tunables as [unordered_set](unordered_set.md#hash-policy), reusing
the identical `CTL_USET_*` macro names — one `#define` before any
hash-container include (`unordered_set.h`, `unordered_map.h`,
`hashmap.h`, `swisstable.h`) configures all of them for the translation
unit:

    #define CTL_USET_GROWTH_PRIMED
    /* slower but more secure: capacity grows to the next prime and
       `find`/`insert`/`erase` index with `hash % capacity`, using all
       hash bits. (default) */
    #define CTL_USET_GROWTH_POWER2
    /* faster, but less secure: capacity stays a power of two and
       indexing masks with `hash & (capacity - 1)`, using only the
       low bits. not recommended with public inet access (json, ...) */

`CTL_USET_GROWTH_FACTOR` defaults to `2` for `CTL_USET_GROWTH_POWER2`
and `1.618` for `CTL_USET_GROWTH_PRIMED`.

`CTL_USET_CACHED_HASH` stores each key's hash next to its entry, to
short-circuit `equal()` on probe misses — faster unsuccessful `find`
at high load factors, at the cost of one `size_t` per entry.

`CTL_USET_SECURITY_COLLCOUNTING` guards against DDOS-crafted keys that
force long probe runs:

    0: ignore                             CTL_USET_SECURITY_COLLCOUNTING 0
    2: collision counting with sleep      CTL_USET_SECURITY_COLLCOUNTING 2 (default)
    3: collision counting with abort      CTL_USET_SECURITY_COLLCOUNTING 3

Modes `1`/`4`/`5` (sorted-vector/tree chain fallback) are a chained
hashtable concept ([unordered_set](unordered_set.md#hash-policy) /
unordered_map); selecting them for `hashmap.h` is a compile error. With
`2`/`3`, override `CTL_USET_SECURITY_ACTION`, which defaults to
`sleep(1)` (`Sleep(500)` on Windows) for `2`, and `abort()` for `3`.

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
