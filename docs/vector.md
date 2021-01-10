# vector - CTL - C Container Template library

Defined in header **<ctl/vector.h>**, CTL prefix **vec**,
parent for [string](string.md), [priority_queue](priority_queue.md),
[u8string](u8string.md) and [u8ident](u8ident.md)

# SYNOPSIS

    #define POD
    #define T int
    #include <ctl/vector.h>

    vec_int a = vec_int_init ();

    vec_digi_resize(&a, 1000, 0);
    for (i=0; i<1000; i++)
      vec_int_push_back(&a, i);
    for (i=0; i<20; i++)
       vec_digi_pop_back(&a);
    vec_int_erase(&a, 5);
    vec_int_insert(&a, 5, 2);

    vec_int_free(&a);

# DESCRIPTION

The elements are stored contiguously, which means that elements can be accessed
not only through iterators, but also using offsets to regular pointers to
elements. This means that a pointer to an element of a vector may be passed to
any function that expects a pointer to an element of an array.

The function names are composed of the prefix **vec_**, the user-defined type
**T** and the method name. E.g `vec_int` with `#define T int`.

Reallocations are usually costly operations in terms of performance. The
`reserve` function can be used to eliminate reallocations if the number of
elements is known beforehand.

The complexity (efficiency) of common operations on a `vector` is as follows:

* Random access - constant 𝓞(1)
* Insertion or removal of elements at the end - amortized constant 𝓞(1)
* Insertion or removal of elements - linear in the distance to the end of the vector 𝓞(n) 

# Member types

`T`                     value type

`A` being `vec_T`       container type

`I` being `vec_T_it`    iterator type

There is no `B` node type.

## Member functions

[init](vec/init.md) `()`

constructs the vector.

[free](vec/free.md) `(A* self)`

destructs the vector.

[assign](vec/assign.md) `(A* self, size_t count, T value)`

replaces the contents of the container.

[assign_range](vec/assign.md) `(A* self, I* first, I* last)`

replaces the contents of the container with the values from range.

[copy](vec/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[at](vec/at.md) `(A* self, size_t index)`

access specified element with bounds checking

[front](vec/front.md) `(A* self)`

access the first element

[back](vec/back.md) `(A* self)`

access the last element

[data](vec/data.md) `(A* self)`

access the underlying array

## Iterators

[begin](vec/begin.md) `(A* self)`

returns an iterator to the beginning

[end](vec/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](vec/empty.md) `(A* self)`

checks whether the container is empty

[size](vec/size.md) `(A* self)`

returns the number of elements

[max_size](vec/max_size.md) `()`

returns the maximum possible number of elements

[reserve](vec/reserve.md) `(A* self, const size_t capacity)`

reserves storage

[capacity](vec/capacity.md) `(A* self)`

returns the number of elements that can be held in currently allocated storage

[shrink_to_fit](vec/shrink_to_fit.md) `(A* self)`

reduces memory usage by freeing unused memory

## Modifiers

[clear](vec/clear.md) `(A* self)`

clears the contents

[insert](vec/insert.md) `(A* self, T key)`

inserts the element `(C++17)`

[emplace](vec/emplace.md) `(A* self, ...)`

constructs elements in-place

[emplace_back](vec/emplace_back.md) `(A* self, it *position, ...)`

constructs elements in-place at position

[erase](vec/erase.md) `(A* self, size_t index)`

erases the element by index

[erase_it](vec/erase.md) `(A* self, I* pos)`

erases the element at position

[erase_range](vec/erase.md) `(A* self, I* first, I* last)`

erases elements from to

[swap](vec/swap.md) `(A* self, A* other)`

swaps the contents

[extract](vec/extract.md) `(A* self, T key)`

extracts a node from the container. NYI

[extract_it](vec/extract.md) `(A* self, I* pos)`

extracts nodes from the container. NYI

[merge](vec/merge.md) `(A* self)`

splices nodes from another container

## Lookup

[count](vec/count.md) `(A* self)`

returns the number of elements matching specific key

[find](vec/find.md) `(A* self, T key)`

finds element with specific key

[contains](vec/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal_range](vec/equal_range.md) `(A* self)`

returns range of elements matching a specific key. (NYI)

[lower_bound](vec/lower_bound.md) `(A* self)`

returns an iterator to the first element not less than the given key. (NYI)

[upper_bound](vec/upper_bound.md) `(A* self)`

returns an iterator to the first element greater than the given key. (NYI)

## Observers

[value_comp](vec/value_comp.md) `(A* self)`

Returns the function that compares keys in objects of type value_type T. (NYI)

## Non-member functions

[swap](vec/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](vec/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](vec/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[intersection](vec/intersection.md) `(A* self, A* other)`

[union](vec/union.md) `(A* self, A* other)`

[difference](vec/difference.md) `(A* self, A* other)`

[symmetric_difference](vec/symmetric_difference.md) `(A* self, A* other)`

