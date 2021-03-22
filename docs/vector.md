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

`I` being `vec_T_it`    internal iterator type for loops

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

replaces the contents of the container with the values from range.

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

    insert_index (A* self, size_t index, T value)
    insert (I* pos, T value)
    insert_count (I* pos, size_t count, T value)
    insert_range (I* pos, I* range2)

inserts copies of the element(s), before pos.

    insert_generic (I* pos, GI* range2)

inserts copies of values from generic range2 before pos. _(NYI)_

    emplace (I* pos, T* value)

constructs elements in-place before pos. _(NY, still leaks)_

    emplace_back (A* self, T* value)

appends new element at the back.

    I erase_index (A* self, size_t index)

erases the element by index, and returns the position following the last removed element.

    I erase (I* pos)

erases a single element at position. Ignores `pos->end` range.

    I* erase_range (I* range)

erases elements from range.

    erase_generic (A* self, GI* range2)

erases elements by value from another container.

    swap (A* self, A* other)

swaps the contents.

    extract (A* self, T value)

extracts a value from the container. _(NYI)_

    extract_it (I* pos)

extracts a node from the container. _(NYI)_

    merge (A* self, A* other)

splices nodes from another container _(NYI)_

## Lookup

    size_t count (A* self, T value)

returns the number of elements matching specific key.

    I find (A* self, T value)

linear search for an element.

    bool equal_range (I* range1, I* range2)

returns range of elements matching a specific key.

    I lower_bound (A* self, T key)
    I lower_bound_range (I* range, T key)

returns an iterator to the first element of the sorted sequence not less than the given key.

    I upper_bound (A* self, T key)
    I upper_bound_range (I* range, T key)

returns an iterator to the first element of the sorted sequence greater than the given key.

## Observers

    FN value_comp (A* self)

Returns the function that compares keys in objects of type value_type T. _(NYI)_

## Non-member functions

    swap (A* self)

specializes the swap algorithm

    size_t remove_if (A* self, int T_match(T*))
    size_t erase_if (A* self, int T_match(T*)) (C++20)

Returns the number of elements removed, satisfying specific criteria.

See [algorithm](algorithm.md) for more.
