# unordered_map - CTL - C Container Template library
 
Defined in header **<ctl/unordered_map.h>**, CTL prefix **umap**,
derived from [unordered_set](unordered_set.md)

Implementation in work still. Esp. lookup should be key only.

## SYNOPSIS

    typedef struct {
      char *key;
      int value;
    } charint;
    
    static inline size_t
    charint_hash(charint *a) { return ctl_string_hash(a->key); }

    static inline int
    charint_equal(charint *a, charint *b) { return strcmp(a->key, b->key) == 0; }

    static inline void
    charint_free(charint *a) { free(a->key); }

    static inline charint
    charint_copy(charint *self) {
      char *copy_key = (char*) malloc(strlen(self->key) + 1);
      strcpy (copy_key, self->key);
      charint copy = {
        copy_key,
        self->value,
      };
      return copy;
    }

    #define T charint
    #include <ctl/unordered_map.h>

    umap_charint a = umap_charint_init();

    char c_char[36];
    for (int i=0; i<1000; i++) {
        snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
        //str s = (str){.value = c_char};
        umap_charint_insert(&a, charint_copy(&(charint){ c_char, i }));
    }
    foreach(umap_charint, &a, it) { strcpy (c_char, it.ref->key); }
    printf("last key \"%s\", ", c_char);
    foreach(umap_charint, &a, it) { umap_charint_bucket_size(it.node); }
    printf("umap_charint load_factor: %f\n", umap_charint_load_factor(&a));
    umap_charint_free(&a);

## DESCRIPTION
		
`unordered_map` is an associative container that contains a map of unique
objects of type Key. Search, insertion, and removal have average constant-time
complexity.

The function names are composed of the prefix **umap_**, the user-defined type
**T** and the method name. E.g `umap_charint` with `#define T charint`. The type
must be a custom struct.

Internally, the elements are not sorted in any particular order, but organized
into buckets. Which bucket an element is placed into depends entirely on the
hash of its value. This allows fast access to individual elements, since once a
hash is computed, it refers to the exact bucket the element is placed into.

We need the slow chained hash table to guarantee that pointers into nodes and
values stay the same. For faster open-adressing hash tables an experimental
[hashtable](hashtable.md) container is planned.
Container elements may not be modified (even by non const iterators) since
modification could change an element's hash and corrupt the container. 

## Member types

`T`                     value type

`A` being `umap_T`       container type

`B` being `umap_T_node`  node type

`I` being `umap_T_it`    iterator type

## Member functions

    A init (T_hash(T*), T_equal(T*, T*))

constructs the hash table.

    free (A* self)

destructs the hash table.

    assign (A* self, A* other)

replaces the contents of the container.

    A copy (A* self)

returns a copy of the container.

## Iterators

    I begin (A* self)

Constructs an iterator to the begin.

    I end (A* self)

constructs an iterator to the end.

`unordered_set` does not support ranges, as this does not make sense.
Our iterator just supports `foreach` and `foreach_n`.

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of non-empty and non-deleted elements

    size_t bucket_count (A* self)

returns the size of the array. Same as capacity

    size_t max_size ()

returns the maximum possible number of elements

## Modifiers

    clear (A* self)

clears the contents

    B* insert (A* self, T value)

inserts new element.

    B* insert_found (A* self, T value, int* foundp)

inserts the element and sets foundp if it already existed.

    B* insert_or_assign (A* self, T value)

inserts the new element, or replaces its value (C++17)

    B* insert_or_assign_found (A* self, T value, int *foundp)

inserts the new element, or replaces its value (C++17)

    emplace (A* self, T* value)

constructs elements in-place. _(NYI)_

    emplace_hint (I* pos, T* value)

constructs elements in-place at position. _(NYI)_

    emplace_found (A* self, T *value, int* foundp)

constructs elements in-place and sets foundp if it already existed. _(NYI)_

    try_emplace (A* self, T *value)

inserts in-place if the key does not exist, does nothing if the key exists. _(NYI)_

    erase (A* self, T key)

erases the element by key, i.e. pair.first

    erase_if (A* self, int _match(T*))

erases the element by match.

    swap (A* self, A* other)

swaps the contents

    B* extract (A* self, T key)

extracts a node from the container.  _(NYI)_

    merge (A* self, A* other)

splices nodes from another container

## Member fields

    .hash

Hash method `int hash(T*)`

    .equal

equal method `int equal(T*, T*)`

## Lookup

    size_t count (A* self)

returns the number of elements matching specific key. It will always be 1,
unless your equal method s broken.

    B* find (A* self, T key)

finds element with specific key, i.e. pair.first

    bool contains (A* self, T key)

checks if the container contains element with specific key,
i.e. pair.first. (C++20)

    int equal (A* self, A* other)

## Bucket interface

    B* begin (A* self, size_t bucket_index)

returns an iterator to the beginning of the specified bucket _(NYI)_

    B* end (A* self, size_t bucket_index)

returns an iterator to the end of the specified bucket _(NYI)_

    size_t bucket_count (A* self)

returns the number of buckets

    size_t max_bucket_count (A* self)

returns the maximum number of buckets of the set.

    size_t bucket_size (A* self, size_t bucket_index)
    size_t bucket_size (B* bucket)

returns the number of elements in the specific bucket, the collisions.

    size_t bucket (A* self, T value)

returns the bucket index for the key.

## Hash policy

Growth policies:
```C
#define CTL_USET_GROWTH_PRIMED
/* slower but more secure. uses all hash bits. (default) */
#define CTL_USET_GROWTH_POWER2
/* faster, but less secure. uses only some lower bits.
   not recommended with public inet access (json, ...) */
``

`CTL_USET_GROWTH_POWER2` rehashes with bucket_count * 2,
`CTL_USET_GROWTH_PRIMED` rehashes with the next prime at bucket_count * 1.618.

    float load_factor (A* self)

returns average number of elements per bucket

    max_load_factor (A* self, float load_factor)

Sets maximum average number of elements per bucket. defaults to 0.85

    rehash (A* self, size_t bucket_count)

reserves at least the specified number of buckets.
This might regenerate the hash table, but not the buckets.

    reserve (A* self, size_t desired_size)

reserves space for at least the specified number of elements.
This might regenerate the hash table, but not the buckets.

## Non-member functions

    swap (A* self)

specializes the swap algorithm

    size_if remove_if (A* self, int _match(T*))

Removes all elements satisfying specific criteria.

    B* find_if (A* self, int _match(T*))

finds element by predicate

    B* find_if_not (A* self, int _match(T*))

finds element by predicate

    A intersection (A* self, A* other)
    A union (A* self, A* other)
    A difference (A* self, A* other)
    A symmetric_difference (A* self, A* other)

    bool all_of (A* self, int _match(T*))
    bool any_of (A* self, int _match(T*))
    bool none_of (A* self, int _match(T*))

See [algorithm](algorithm.md) for more.
