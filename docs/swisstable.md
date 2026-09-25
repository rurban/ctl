# swisstable - CTL C Container Template library

Defined in **<ctl/swisstable.h>**. It is an open-addressing hashmap with separate key `TK` and value `T` types. The generated prefix is `swiss_TK_T`.

    static size_t int_hash(int *key) { return (size_t)*key; }
    static int int_equal(int *left, int *right) { return *left == *right; }
    #define POD
    #define TK int
    #define T int
    #include <ctl/swisstable.h>

    swiss_int_int map = swiss_int_int_init(int_hash, int_equal);
    swiss_int_int_insert(&map, 7, 42);

The initial implementation supports POD keys and values. It grows at
75% load, and rehashes after erase so probes always terminate at an
unused entry. Pointers returned by `find` are invalidated by insertion
that grows the table and by erase.

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
unordered_map); selecting them for `swisstable.h` is a compile error.
With `2`/`3`, override `CTL_USET_SECURITY_ACTION`, which defaults to
`sleep(1)` (`Sleep(500)` on Windows) for `2`, and `abort()` for `3`.

## API

    A init(size_t hash(TK*), int equal(TK*, TK*))
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

`insert` returns true for a new key and false when it replaces an existing
value. Lookup and erase keys are borrowed.

Iteration order is unspecified (bucket order), matching
`std::unordered_map`. `equal_range` returns a one-element `[lower, upper)`
range when the key is found (`upper` is `lower` advanced by one), or an
empty range at `end()` when it is not — keys are unique, so it never spans
more than one entry. `count` is always 0 or 1 for the same reason.
`rehash`/`reserve` only grow (never shrink) to the next valid capacity
(prime or power-of-two, per the growth policy above) that keeps the
existing/requested element count under the current max load factor
(0.75 by default, adjustable with `max_load_factor`). `load_factor`
reports `size / capacity` as a float.
`max_size` is a compile-time cap of ~4GB of entries, like the other
containers. `copy` deep-copies the table into fresh storage (no shared
entries); `assign` replaces a table's contents with a copy of another,
freeing the old storage. `swap` exchanges two containers' entire state
(entries, size, capacity, hash, equal) in O(1).
