# string - CTL - C Container Template library

Defined in header **<ctl/string.h>**, CTL prefix **str**.
deriving from [vector](vector.md).

# SYNOPSIS

    #define POD
    #define T int
    #include <ctl/string.h>

    str_int a = str_int_init ();

    str_digi_resize(&a, 1000, '\0');
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

`T` being `char`     value type

`A` being `str`       container type

`I` being `str_it`    iterator type

## Member functions

    str init (char* str)

constructs the string.

    free (str* self)

destructs the string.

    assign (str* self, size_t count, char value)

replaces the contents of the container.

    assign_range (str* self, I* first, I* last)

replaces the contents of the container with the values from range.

    str copy (str* self)

returns a copy of the container.

## Element access

    char* at (str* self, size_t index)

access specified element with bounds checking

    char* front (str* self)

access the first element

    char* back (str* self)

access the last element

    char* data (str* self)

access the underlying array

## Iterators

    char* begin (str* self)

returns an iterator to the beginning

    char* end (str* self)

returns an iterator to the end

## Capacity

    int empty (str* self)

checks whether the container is empty

    size_t size (str* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements

    reserve (str* self, const size_t capacity)

reserves storage

    size_t capacity (str* self)

returns the number of elements that can be held in currently allocated storage

    shrink_to_fit (str* self)

reduces memory usage by freeing unused memory

## Modifiers

    clear (str* self)

clears the contents

    char* insert (str* self, char key)

inserts the element (C++17)

    emplace (str* self, char* key)

constructs elements in-place

    emplace_back (str* self, I* position, char* key)

constructs elements in-place at position

    erase (str* self, size_t index)

erases the element by index

    erase_it (str* self, I* position)

erases the element at position

    erase_range (str* self, I* first, I* last)

erases elements from to

    swap (str* self, str* other)

swaps the contents

    extract (str* self, charkey)

extracts a node from the container. NYI

    extract_it (str* self, I* position)

extracts nodes from the container. NYI

    merge (str* self)

splices nodes from another container

## Lookup

    size_t count (str* self)

returns the number of elements matching specific key

    char* find (str* self, char key)

finds element with specific key

    bool contains (str* self, char key)

checks if the container contains element with specific key. (C++20)

    int equal_range (str* self)

returns range of elements matching a specific key. _(NYI)_

    size_t lower_bound (str* self)

returns an iterator to the first element not less than the given key. _(NYI)_

    char* upper_bound (str* self)

returns an iterator to the first element greater than the given key. _(NYI)_

## Observers

    value_comp (str* self)

Returns the function that compares keys in objects of type value_type T. _(NYI)_

## Non-member functions

    swap (str* self)

specializes the swap algorithm

    remove_if (str* self, int match(T*))

Removes all elements satisfying specific criteria.

    erase_if (str* self, int match(T*))

erases all elements satisfying specific criteria (C++20)

    intersection (str* self, str* other)
    union (str* self, str* other)
    difference (str* self, str* other)
    symmetric_difference (str* self, str* other)

