# string - CTL - C Container Template library

Defined in header **<ctl/string.h>**, CTL prefix **str**.
deriving from [vector](vector.md).

# SYNOPSIS

    #undef POD
    #define T int
    #include <ctl/string.h>

    str_int a = str_int_init ();

    str_digi_resize(&a, 1000, 0);
    for (i=0; i<1000; i++)
      str_int_push_back(&a, i);
    for (i=0; i<20; i++)
       str_digi_pop_back(&a);
    str_int_erase(&a, 5);
    str_int_insert(&a, 5, 2);

    str_int_free(&a);

# DESCRIPTION

The elements are stored contiguously, which means that elements can be accessed
not only through iterators, but also using offsets to regular pointers to
elements. This means that a pointer to an element of a string may be passed to
any function that expects a pointer to an element of an array.

The function names are composed of the prefix **str_**, the user-defined type
**T** and the method name. E.g `str_int` with `#define T int`.

Reallocations are usually costly operations in terms of performance. The
`reserve` function can be used to eliminate reallocations if the number of
elements is known beforehand.

The complexity (efficiency) of common operations on a `string` is as follows:

* Random access - constant 𝓞(1)
* Insertion or removal of elements at the end - amortized constant 𝓞(1)
* Insertion or removal of elements - linear in the distance to the end of the string 𝓞(n) 

# Member types

`T`                     value type

`A` being `str_T`       container type

`I` being `str_T_it`    iterator type

## Member functions

[init](str/init.md) `()`

constructs the string.

[free](str/free.md) `(A* self)`

destructs the string.

[assign](str/assign.md) `(A* self, size_t count, T value)`

replaces the contents of the container.

[assign_range](str/assign.md) `(A* self, I* first, I* last)`

replaces the contents of the container with the values from range.

[copy](str/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[at](str/at.md) `(A* self, size_t index)`

access specified element with bounds checking

[front](str/front.md) `(A* self)`

access the first element

[back](str/back.md) `(A* self)`

access the last element

[data](str/data.md) `(A* self)`

access the underlying array

## Iterators

[begin](str/begin.md) `(A* self)`

returns an iterator to the beginning

[end](str/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](str/empty.md) `(A* self)`

checks whether the container is empty

[size](str/size.md) `(A* self)`

returns the number of elements

[max_size](str/max_size.md) `()`

returns the maximum possible number of elements

[reserve](str/reserve.md) `(A* self, const size_t capacity)`

reserves storage

[capacity](str/capacity.md) `(A* self)`

returns the number of elements that can be held in currently allocated storage

[shrink_to_fit](str/shrink_to_fit.md) `(A* self)`

reduces memory usage by freeing unused memory

## Modifiers

[clear](str/clear.md) `(A* self)`

clears the contents

[insert](str/insert.md) `(A* self, T key)`

inserts the element `(C++17)`

[emplace](str/emplace.md) `(A* self, ...)`

constructs elements in-place

[emplace_back](str/emplace_back.md) `(A* self, I* position, ...)`

constructs elements in-place at position

[erase](str/erase.md) `(A* self, size_t index)`

erases the element by index

[erase_it](str/erase.md) `(A* self, I* position)`

erases the element at position

[erase_range](str/erase.md) `(A* self, I* first, I* last)`

erases elements from to

[swap](str/swap.md) `(A* self, A* other)`

swaps the contents

[extract](str/extract.md) `(A* self, T key)`

extracts a node from the container. NYI

[extract_it](str/extract.md) `(A* self, I* position)`

extracts nodes from the container. NYI

[merge](str/merge.md) `(A* self)`

splices nodes from another container

## Lookup

[count](str/count.md) `(A* self)`

returns the number of elements matching specific key

[find](str/find.md) `(A* self, T key)`

finds element with specific key

[contains](str/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. (C++20)

[equal_range](str/equal_range.md) `(A* self)`

returns range of elements matching a specific key. (NYI)

[lower_bound](str/lower_bound.md) `(A* self)`

returns an iterator to the first element not less than the given key. (NYI)

[upper_bound](str/upper_bound.md) `(A* self)`

returns an iterator to the first element greater than the given key. (NYI)

## Observers

[value_comp](str/value_comp.md) `(A* self)`

Returns the function that compares keys in objects of type value_type T. (NYI)

## Non-member functions

[swap](str/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](str/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](str/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[intersection](str/intersection.md) `(A* self, A* other)`

[union](str/union.md) `(A* self, A* other)`

[difference](str/difference.md) `(A* self, A* other)`

[symmetric_difference](str/symmetric_difference.md) `(A* self, A* other)`

