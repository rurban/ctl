# unordered_map - CTL - C Container Template library
 
Defined in header **<ctl/unordered_map.h>**, CTL prefix **umap**,
derived from [unordered_set](unordered_set.md)

Implementation in work still.

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
    #include <ctl/unordered_map.h>

    umap_charint a = umap_charint_init(1000, charint_hash, charint_equal);
    
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

# DESCRIPTION
		
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

# Member types

`T`                     value type

`A` being `umap_T`       container type

`B` being `umap_T_node`  node type

`I` being `umap_T_it`    iterator type

## Member functions

[init](uset/init.md) `(bucket_count, T_hash(T*), T_equal(T*, T*))`

constructs the hash table.

[free](uset/free.md) `(A* self)`

destructs the hash table.

[assign](uset/assign.md) `(A* self, A* other)`

replaces the contents of the container.

[copy](uset/copy.md) `(A* self)`

returns a copy of the container.

## Iterators

[begin](uset/begin.md) `(A* self)`

returns an iterator to the beginning

[end](uset/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](uset/empty.md) `(A* self)`

checks whether the container is empty

[size](uset/size.md) `(A* self)`

returns the number of non-empty and non-deleted elements

[capacity](uset/size.md) `(A* self)`

returns the size of the array

[max_size](uset/max_size.md) `()`

returns the maximum possible number of elements

## Modifiers

[clear](uset/clear.md) `(A* self)`

clears the contents

[insert](uset/insert.md) `(A* self, T value)`

inserts new element.

[insert_or_assign](umap/insert_or_assign.md) `(A* self, T value)`

inserts the new element, or replaces its value `(C++17)`

[emplace](uset/emplace.md) `(A* self, T values...)`

constructs elements in-place. (NYI)

[emplace_hint](map/emplace_hint.md) `(A* self, I* pos, T values...)`

constructs elements in-place at position. (NYI)

[try_emplace](uset/emplace.md) `(A* self, T values...)`

inserts in-place if the key does not exist, does nothing if the key exists. (NYI)

[erase](uset/erase.md) `(A* self, T key)`

erases the element by key

[erase_it](uset/erase.md) `(A* self, I* pos)`

erases the element at pos

[erase_range](uset/erase.md) `(A* self, I* first, I* last)`

erases elements

[swap](uset/swap.md) `(A* self, A* other)`

swaps the contents

[extract](uset/extract.md) `(A* self, T key)`
[extract_it](uset/extract.md) `(A* self, I* pos)`

extracts a node from the container. NYI

[merge](uset/merge.md) `(A* self)`

splices nodes from another container

## Lookup

[count](uset/count.md) `(A* self)`

returns the number of elements matching specific key

[find](uset/find.md) `(A* self, T key)`

finds element with specific key

[contains](uset/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal_range](uset/equal_range.md) `(A* self)`

returns range of elements matching a specific key. (NYI)

## Bucket interface

begin `(A* self, size_t bucket_index)`

returns an iterator to the beginning of the specified bucket

end `(A* self, size_t bucket_index)`

returns an iterator to the end of the specified bucket

bucket_count `(A* self)`

returns the number of buckets

max_bucket_count `(A* self)`

returns the maximum number of buckets of the map.

bucket_size `(A* self, size_t bucket_index)`

returns the number of elements in specific bucket.

bucket `(A* self, T value)`

returns the bucket index for the key.

## Hash policy

[load_factor](uset/load_factor.md) `(A* self)`

returns average number of elements per bucket

[max_load_factor](uset/max_load_factor.md) `(A* self)`
[set_max_load_factor](uset/max_load_factor.md) `(A* self, float factor)`
	
manages maximum average number of elements per bucket. defaults to 0.85

[rehash](uset/rehash.md) `(A* self, size_t bucket_count)`

reserves at least the specified number of buckets.
This regenerates the hash table.

[reserve](uset/reserve.md) `(A* self, size_t desired_size)`

reserves space for at least the specified number of elements.
This regenerates the hash table. 

## Non-member functions

[swap](uset/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](uset/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](uset/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[intersection](uset/intersection.md) `(A* self, A* other)`

[union](uset/union.md) `(A* self, A* other)`

[difference](uset/difference.md) `(A* self, A* other)`

[symmetric_difference](uset/symmetric_difference.md) `(A* self, A* other)`

