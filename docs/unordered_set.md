# unordered_set - CTL - C Container Template library
 
Defined in header **<ctl/unordered_set.h>**, CTL prefix **uset**,
parent of [unordered_map](unordered_map.md)

Implementation in work still.

# SYNOPSIS

    size_t int_hash(int* x) { return abs(*x); }
    int int_eq(int* a, int* b) { return *a == *b; }

    #undef POD
    #define T int
    #include <ctl/unordered_set.h>

    uset_int a = uset_int_init(200, int_hash, int_eq);
    for (int i=0; i < 120; i++)
      uset_int_insert(&a, rand());

    foreach(uset_int, &a, it) { printf("GOT %d\n", *it.ref); }
    foreach(uset_int, &a, it) { printf("SIZE %lu\n", uset_int_bucket_size(it.node)); }
    printf("load_factor: %f\n", uset_int_load_factor(&a));

    uset_int_free(&a);

# DESCRIPTION
		
`unordered_set` is an associative container (chained hash table) that contains a
set of unique objects of type Key. Search, insertion, and removal have average
constant-time complexity.

The function names are composed of the prefix **uset_**, the user-defined type
**T** and the method name. E.g `uset_int` with `#define T int`.

Internally, the elements are not sorted in any particular order, but organized
into buckets. Which bucket an element is placed into depends entirely on the
hash of its value. This allows fast access to individual elements, since once a
hash is computed, it refers to the exact bucket the element is placed into.

We need the slow chained hash table to guarantee that pointers into nodes and
values stay the same. For faster open-adressing hash tables an experimental
[hashtable](hashtable.md) container is planned.
Container elements may not be modified since modification could change an
element's hash and corrupt the container.

# Member types

`T`                      value type

`A` being `uset_T`       container type

`B` being `uset_T_node`  node type

`I` being `uset_T_it`    iterator type

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

inserts the element `(C++17)`

[emplace](uset/emplace.md) `(A* self, T values...)`

constructs elements in-place. (NYI)

[emplace_hint](map/emplace_hint.md) `(A* self, I* pos, T values...)`

constructs elements in-place at position. (NYI)

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

