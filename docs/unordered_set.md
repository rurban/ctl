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

    uset_int a = uset_int_init(int_hash, int_eq);
    for (int i=0; i < 120; i++)
      uset_int_insert(&a, rand());

    printf ("5 is %s included\n", uset_int_contains(&a, 5) ? "" : "not");
    uset_digi_node* n = uset_int_find(&a, 5));
    uset_int_erase(&a, 5);

    foreach(uset_int, &a, it) { printf("GOT %d\n", *it.ref); }
    foreach(uset_int, &a, it) { printf("SIZE %lu\n", uset_int_node_bucket_size(it.node)); }
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

[init](uset/init.md) `(T_hash(T*), T_equal(T*, T*))`

constructs the hash table.
with INTEGRAL types the member may be NULL, and are then set to default
methods.

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

[bucket_count](uset/size.md) `(A* self)`

returns the size of the array. Same as capacity

[max_size](uset/max_size.md) `()`

returns the maximum possible number of elements

## Modifiers

[clear](uset/clear.md) `(A* self)`

clears the contents

[insert](uset/insert.md) `(A* self, T value)`

inserts the element `(C++17)`

[insert_found](uset/insert.md) `(A* self, T value, int* foundp)`

inserts the element and sets foundp if it already existed.

[emplace](uset/emplace.md) `(A* self, T *value)`

constructs elements in-place. (NYI)

[emplace_hint](uset/emplace.md) `(A* self, I* pos, T *value)`

constructs elements in-place at position. (NYI)

[emplace_found](uset/emplace.md) `(A* self, T *value, int* foundp)`

constructs elements in-place and sets foundp if it already existed. (NYI)

[erase](uset/erase.md) `(A* self, T key)`

erases the element by key

[erase_if](uset/erase_if.md) `(A* self, int (*_match)(T*))`

erases the element by match.

[erase_range](uset/erase.md) `(A* self, I* first, I* last)`

erases elements

[swap](uset/swap.md) `(A* self, A* other)`

swaps the contents

[extract](uset/extract.md) `(A* self, T key)`

extracts a node from the container. NYI

[merge](uset/merge.md) `(A* self, A* other)`

splices nodes from another container

## Member fields

[`.hash`](uset/.hash.md)

Hash method `int (*hash)(T*)`

[`.equal`](uset/.equal.md)

equal method `int (*equal)(T*, T*)`

## Lookup

[count](uset/count.md) `(A* self)`

returns the number of elements matching specific key. It will always be 1,
unless your equal method s broken.

[find](uset/find.md) `(A* self, T key)`

finds element with specific key

[contains](uset/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal](uset/equal.md) `(A* self, A* other)`

[equal_range](uset/equal_range.md) `(A* self, I* first, I* last)`

if range of elements match a specific key. (NYI)

## Bucket interface

begin `(A* self, size_t bucket_index)`

returns an iterator to the beginning of the specified bucket (NYI)

end `(A* self, size_t bucket_index)`

returns an iterator to the end of the specified bucket (NYI)

bucket_count `(A* self)`

returns the number of buckets

max_bucket_count `(A* self)`

returns the maximum number of buckets of the set.

bucket_size `(A* self, size_t bucket_index)`
bucket_size `(B* bucket)`

returns the number of elements in the specific bucket, the collisions.

bucket `(A* self, T value)`

returns the bucket index for the key.

## Hash policy

Growth policies:
```C
#define CTL_USET_GROWTH_PRIMED
/* slower but more secure. uses all hash bits. (default) */
#define CTL_USET_GROWTH_POWER2
/* faster, but less secure. uses only some lower bits.
   not recommended with public inet access (json, ...) */
```

`CTL_USET_GROWTH_POWER2` rehashes with bucket_count * 2,
`CTL_USET_GROWTH_PRIMED` rehashes with the next prime at bucket_count * 1.618.

[load_factor](uset/load_factor.md) `(A* self)`

returns average number of elements per bucket

[max_load_factor](uset/max_load_factor.md) `(A* self)`
[set_max_load_factor](uset/max_load_factor.md) `(A* self, float factor)`

manages maximum average number of elements per bucket. defaults to 0.85

[rehash](uset/rehash.md) `(A* self, size_t bucket_count)`

reserves at least the specified number of buckets.
This might regenerate the hash table, but not the buckets.

[reserve](uset/reserve.md) `(A* self, size_t desired_size)`

reserves space for at least the specified number of elements.
This might regenerate the hash table, but not the buckets.

## Non-member functions

[swap](uset/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](uset/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[find_if](algorithm/find_if.md) `(A* self, int _match(T*))`

finds element by predicate

[find_if_not](algorithm/find_if.md) `(A* self, int _match(T*))`

finds element by predicate

[intersection](algorithm/intersection.md) `(A* self, A* other)`

[union](algorithm/union.md) `(A* self, A* other)`

[difference](algorithm/difference.md) `(A* self, A* other)`

[symmetric_difference](algorithm/symmetric_difference.md) `(A* self, A* other)`

[all_of](algorithm/all_of.md) `(A* self, int _match(T*))`

[any_of](algorithm/any_of.md) `(A* self, int _match(T*))`

[none_of](algorithm/none_of.md) `(A* self, int _match(T*))`

[all_of_range](algorithm/all_of.md) `(A* self, I* first, I* last, int _match(T*))`

[any_of_range](algorithm/any_of.md) `(A* self, I* first, I* last, int _match(T*))`

[none_of_range](algorithm/none_of.md) `(A* self, I* first, I* last, int _match(T*))`
