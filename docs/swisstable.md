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
    T* find(A* self, TK key)
    int contains(A* self, TK key)
    bool insert(A* self, TK key, T value)
    bool erase(A* self, TK key)
    void free(A* self)

`insert` returns true for a new key and false when it replaces an existing value. Lookup and erase keys are borrowed.
