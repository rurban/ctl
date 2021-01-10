# set - CTL - C Container Template library

Defined in header **<ctl/set.h>**, CTL prefix **set**,
parent for [map](map.md).

## SYNOPSIS

    static inline int
    int_cmp(int *a, int *b) {
      return *a < *b;
    }

    #define POD
    #define T int
    #include <ctl/set.h>

    int i = 0;
    set_int a = set_int_init (int_cmp);

    for (i=0; i<1000; i++) {
      set_int_insert (&a, i);
    }

    foreach(set_int, &a, it) { i = it.ref->key); }
    printf("last key %d, ", i);

    printf("min {\"%s\", %d} ", set_int_min (a));
    printf("max {\"%s\", %d}\n", set_int_max (a));
    set_int_free(&a);

## DESCRIPTION

set is a sorted associative container that contains key-value pairs with unique
keys. Keys are sorted by using the custom comparison function T_cmp. Search, removal,
and insertion operations have logarithmic complexity. set is implemented as red-black tree.

The function names are composed of the prefix **set_**, the user-defined type
**T** and the method name. E.g `set_int` with `#define T int`.

Everywhere the CTL uses the Compare requirements, uniqueness is
determined by using the equivalence relation. In imprecise terms, two objects a
and b are considered equivalent (not unique) if neither compares less than the
other: !comp(a, b) && !comp(b, a).

## Member types

`T`                     value type

`A` being `set_T`       container type

`B` being `set_T_node`  node type

`I` being `set_T_it`    iterator type

## Member functions

[init](set/init.md) `(T_compare(T*, T*))`

constructs the set.

[free](set/free.md) `(A* self)`

destructs the set.

[assign](set/assign.md) `(A* self, A* other)`

replaces the contents of the container.

[copy](set/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[at](set/at.md) `(A* self, size_t index)`

access specified element with bounds checking

## Iterators

[begin](set/begin.md) `(A* self)`

returns an iterator to the beginning

[end](set/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](set/empty.md) `(A* self)`

checks whether the container is empty

[size](set/size.md) `(A* self)`

returns the number of elements

[max_size](set/max_size.md) ()

returns the maximum possible number of elements

## Modifiers

[clear](set/clear.md) `(A* self)`

clears the contents

[insert](set/insert.md) `(A* self, T key)`

inserts the element `(C++17)`

[emplace](set/emplace.md) `(A* self, T values...)`

constructs elements in-place. (NYI)

[emplace_hint](map/emplace_hint.md) `(A* self, I* pos, T values...)`

constructs elements in-place at position. (NYI)

[erase](set/erase.md) `(A* self, T key)`

erases the element by value

[erase_it](set/erase.md) `(A* self, I* pos)`

erases the element at pos

[erase_range](set/erase.md) `(A* self, I* first, I* last)`

erases elements

[swap](set/swap.md) `(A* self, A* other)`

swaps the contents

[extract](set/extract.md) `(A* self, T key)`

extracts a node from the container. NYI

[extract_it](set/extract.md) `(A* self, I* pos)`

extracts nodes from the container. NYI

[merge](set/merge.md) `(A* self)`

splices nodes from another container

## Lookup

[count](set/count.md) `(A* self)`

returns the number of elements matching specific key

[find](set/find.md) `(A* self, T key)`

finds element with specific key

[contains](set/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal_range](set/equal_range.md) `(A* self)`

returns range of elements matching a specific key. (NYI)

[lower_bound](set/lower_bound.md) `(A* self)`

returns an iterator to the first element not less than the given key. (NYI)

[upper_bound](set/upper_bound.md) `(A* self)`

returns an iterator to the first element greater than the given key. (NYI)

## Observers

[value_comp](set/value_comp.md) `(A* self)`

Returns the function that compares keys in objects of type value_type T. (NYI)

## Non-member functions

[swap](set/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](set/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](set/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[intersection](set/intersection.md) `(A* self, A* other)`

[union](set/union.md) `(A* self, A* other)`

[difference](set/difference.md) `(A* self, A* other)`

[symmetric_difference](set/symmetric_difference.md) `(A* self, A* other)`

