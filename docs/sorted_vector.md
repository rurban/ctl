# sorted_vector - CTL - C Container Template library

Defined in header **<ctl/sorted_vector.h>**, CTL prefix **svec**.
Derived from vector.

# SYNOPSIS

    #define POD
    #define T int
    #include <ctl/sorted_vector.h>

    svec_int a = svec_int_init ();

    svec_digi_resize(&a, 1000, 0);
    for (i=0; i<100; i++)
      svec_int_insert(&a, i);
    for (i=500; i>100; i--)
      svec_int_insert(&a, i);
    for (i=0; i<20; i++)
       svec_int_erase(&a, i);
    svec_int_erase(&a, 50);
    svec_int_insert(&a, 50);

    svec_int_free(&a);

# DESCRIPTION

A vector that keep its elements sorted on insertion.

The function names are composed of the prefix **svec_**, the user-defined type
**T** and the method name. E.g `svec_int` with `#define T int`.

# Member types

`T`                     value type

`A` being `svec_T`       container type

`I` being `svec_T_it`    internal iterator type for loops

There is no `B` node type.

## Member functions

    A init ()
    A init_from (A* other)

constructs the object. init_from just takes the methods from other, not the vector.

    free (A* self)

destructs the vector.

    assign (A* self, size_t count, T value)

replaces the contents of the container.

    assign_range (A* self, T* first, T* last)
    assign_generic (A* self, GI *range)

replaces the contents of the container with the values from range. The input
ranges are considered unsorted. Use `insert_sorted` for sorted input.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* at (A* self, size_t index)

access specified element with bounds checking

    T* front (A* self)

access the first element

    T* back (A* self)

access the last element

    T* data (A* self)

access the underlying array

## Iterators

    I begin (A* self)

constructs an iterator to the beginning.

    I end (A* self)

constructs an iterator to the end (one past the last element).

    I* next (I* iter)

Advances the iterator by 1 forwards. There's no prev yet.

    I* advance (I* iter, long i)

All our variants accepts negative `i` to move back. The return value may be ignored.

    I iter (A* self, size_t index)

Constructs an iterator to an element.

    size_t index (I* iter)

Returns the index of the iterator, which is just a `T* ref`.

See [iterators](iterators.md) for more.

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

    reserve (A* self, const size_t capacity)

reserves storage

    size_t capacity (A* self)

returns the number of elements that can be held in currently allocated storage

    shrink_to_fit (A* self)

reduces memory usage by freeing unused memory

## Modifiers

    clear (A* self)

clears the contents

    insert (A* self, T value)
    insert_sorted (A* self, I* sortedrange)
    insert_count (A* self, size_t count, T value)
    insert_range (A* self, I* range2)
    insert_generic (A* self, GI* range2)

inserts copies of values.

    I erase_index (A* self, size_t index)

erases the element by index, and returns the position following the last removed element.

    I erase (T value)

erases a single element.

    I* erase_range (I* range)

erases elements from sorted range.

    erase_generic (A* self, GI* range2)

erases elements by value from another unsorted container.

    swap (A* self, A* other)

swaps the contents.

    extract (A* self, T value)

extracts a value from the container. _(NYI)_

    extract_it (I* pos)

extracts a node from the container. _(NYI)_

    merge (A* self, A* other)

splices nodes from another container

## Lookup

    size_t count (A* self, T value)

returns the number of elements matching specific key.

    I find (A* self, T value)

binary search for an element.

    bool equal_range (I* range1, I* range2)

returns range of elements matching a specific key.

    I lower_bound (A* self, T key)
    I lower_bound_range (I* range, T key)

returns an iterator to the first element of the sorted sequence not less than the given key.

    I upper_bound (A* self, T key)
    I upper_bound_range (I* range, T key)

returns an iterator to the first element of the sorted sequence greater than the given key.

## Non-member functions

    size_t remove_if (A* self, int T_match(T*))
    size_t erase_if (A* self, int T_match(T*)) (C++20)

Returns the number of elements removed, satisfying specific criteria.

See [algorithm](algorithm.md) for more.
