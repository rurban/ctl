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

The initial implementation supports POD keys and values. It uses power-of-two open addressing, grows at 75% load, and rehashes after erase so probes always terminate at an unused entry. Pointers returned by `find` are invalidated by insertion that grows the table and by erase.

## API

    A init(size_t hash(TK*), int equal(TK*, TK*))
    bool empty(A* self)
    T* find(A* self, TK key)
    int contains(A* self, TK key)
    size_t count(A* self, TK key)
    void equal_range(A* self, TK key, I* lower, I* upper)
    bool insert(A* self, TK key, T value)
    bool erase(A* self, TK key)
    void clear(A* self)
    bool rehash(A* self, size_t bucket_count)
    bool reserve(A* self, size_t count)
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
`rehash`/`reserve` only grow (never shrink) to the next power-of-two
bucket count that keeps the existing/requested element count under the
75% load factor. `swap` exchanges two containers' entire state
(entries, size, capacity, hash, equal) in O(1).
