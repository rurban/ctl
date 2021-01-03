# hashtable - CTL - C Container Template library
 
Defined in header **<ctl/hashtable.h>**, CTL prefix **htbl**,
parent of [unordered_map](unordered_map.md)

No implementation yet.

# SYNOPSIS

    typedef struct {
      char *key;
      int value;
    } charint;
    
    static inline size_t
    charint_hash(charint *a) { return FNV1a(a->key); }

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

    #undef POD
    #define T charint
    #include <ctl/hashtable.h>

    htbl_charint a = htbl_charint_init(1000, charint_hash, charint_equal);
    
    char c_char[36];
    for (int i=0; i<1000; i++) {
        snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
        //str s = (str){.value = c_char};
        htbl_charint_insert(&a, charint_copy(&(charint){ c_char, i }));
    }
    foreach(htbl_charint, &a, it) { strcpy (c_char, it.ref->key); }
    printf("last key \"%s\", ", c_char);
    foreach(htbl_charint, &a, it) { htbl_charint_bucket_size(it.node); }
    printf("htbl_charint load_factor: %f\n", htbl_charint_load_factor(&a));
    htbl_charint_free(&a);

# DESCRIPTION

`hashtable` is an optimized associative container (open-addressing hash table)
that contains a set of unique objects of type Key. Search, insertion, and
removal have average constant-time complexity.

The function names are composed of the prefix **htbl_**, the user-defined type
**T** and the method name. E.g `htbl_charint` with `#define T charint`. The type
must be a custom struct.

Internally, the elements are not sorted in any particular order, but organized
into buckets. Which bucket an element is placed into depends entirely on the
hash of its value. This allows fast access to individual elements, since once a
hash is computed, it refers to the exact bucket the element is placed into.

This hash table, in opposition to `unordered_map`, does not to guarantee that
pointers into nodes and values stay the same.
Container elements may not be modified since modification could change an
element's hash and corrupt the container.

It has the same API as unordered_map, just no Bucket interface.

# Member types

`T`                      value type

`A` being `uset_T`       container type

`B` being `uset_T_node`  node type

`I` being `uset_T_it`    iterator type

## Member functions

[init](htbl/init.md) `(bucket_count, T_hash(T*), T_equal(T*, T*))`

constructs the hash table.

[free](htbl/free.md) `(A* self)`

destructs the hash table.

[assign](htbl/assign.md) `(A* self, A* other)`

replaces the contents of the container.

[copy](htbl/copy.md) `(A* self)`

returns a copy of the container.

## Iterators

[begin](htbl/begin.md) `(A* self)`

returns an iterator to the beginning

[end](htbl/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](htbl/empty.md) `(A* self)`

checks whether the container is empty

[size](htbl/size.md) `(A* self)`

returns the number of non-empty and non-deleted elements

[capacity](htbl/size.md) `(A* self)`

returns the size of the array

[max_size](htbl/max_size.md) `()`

returns the maximum possible number of elements

## Modifiers

[clear](htbl/clear.md) `(A* self)`

clears the contents

[insert](htbl/insert.md) `(A* self, T value)`

inserts the element `(C++17)`

[emplace](htbl/emplace.md) `(A* self, T values...)`

constructs elements in-place. (NYI)

[emplace_hint](map/emplace_hint.md) `(A* self, I* pos, T values...)`

constructs elements in-place at position. (NYI)

[erase](htbl/erase.md) `(A* self, T key)`

erases the element by key

[erase_it](htbl/erase.md) `(A* self, I* pos)`

erases the element at pos

[erase_range](htbl/erase.md) `(A* self, I* first, I* last)`

erases elements

[swap](htbl/swap.md) `(A* self, A* other)`

swaps the contents

[extract](htbl/extract.md) `(A* self, T key)`
[extract_it](htbl/extract.md) `(A* self, I* pos)`

extracts a node from the container. NYI

[merge](htbl/merge.md) `(A* self)`

splices nodes from another container

## Lookup

[count](htbl/count.md) `(A* self)`

returns the number of elements matching specific key

[find](htbl/find.md) `(A* self, T key)`

finds element with specific key

[contains](htbl/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal_range](htbl/equal_range.md) `(A* self)`

returns range of elements matching a specific key. (NYI)

## Hash policy

[load_factor](htbl/load_factor.md) `(A* self)`

returns average number of elements per bucket

[max_load_factor](htbl/max_load_factor.md) `()`
[set_max_load_factor](htbl/max_load_factor.md) `(A* self, float factor)`
	
manages maximum average number of elements per bucket. defaults to 0.70

[rehash](htbl/rehash.md) `(A* self, size_t bucket_count)`

reserves at least the specified number of buckets.
This regenerates the hash table.

[reserve](htbl/reserve.md) `(A* self, size_t desired_size)`

reserves space for at least the specified number of elements.
This regenerates the hash table. 

## Non-member functions

[swap](htbl/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](htbl/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](htbl/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[intersection](htbl/intersection.md) `(A* self, A* other)`

[union](htbl/union.md) `(A* self, A* other)`

[difference](htbl/difference.md) `(A* self, A* other)`

[symmetric_difference](htbl/symmetric_difference.md) `(A* self, A* other)`

