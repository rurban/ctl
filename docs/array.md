# array - CTL - C Container Template library

Defined in header **<ctl/array.h>**, CTL prefix **array**.

# SYNOPSIS

    #define POD
    #define T int
    #define N 128
    #include <ctl/array.h>

    #define ARRAY     arr128_int
    #define ARR(name) JOIN(ARRAY, name)

    ARRAY a = ARR(init)();

    for (int i=0; i<128; i++)
        ARR(set)(&a, i, rand() % 50);
    int* p = ARR(find)(&a, 5);
    if (p)
        printf ("First element 5 found at a[%ld]\n", p - a.vector);
    ARRAY aa = ARR(copy)(&a);
    ARR(sort)(&aa);

    ARR(free)(&aa);
    ARR(free)(&a);

# DESCRIPTION

Compile-time fixed-size vector. The elements are stored contiguously, which
means that elements can be accessed not only through iterators, but also using
offsets to regular pointers to elements. This means that a pointer to an element
of a vector may be passed to any function that expects a pointer to an element
of an array.

The function names are composed of the prefix **arrN_**, the user-defined type
**T** and the method name. E.g `arr128_int` with `#define T int` and `#define N 128`.

# Member types

`T`                     value type

`N`                     number of elements

`A` being `arrN_T`       container type

`I` being `arrN_T_it`    internal iterator type for loops

`IT` being `T*`, the generic type of iterators.

There is no `B` node type.

## Member functions

    A init ()

constructs the array.

    free (A* self)

destructs the array.

    assign (A* self, size_t count, T value)

replaces the contents of the container.

    assign_range (A* self, T* first, T* last)

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

Note: `begin` and `end` return `T*` pointers, not iterators yet.

    T* begin (A* self)

constructs an iterator to the beginning

    T* end (A* self)

constructs an iterator to the end (one past the last element).

## Capacity

    int empty (A* self)

checks whether the container is empty, i.e. N == 0.

    size_t size (A* self)

returns the number of elements, i.e. N.

    size_t max_size ()

returns the maximum possible number of elements, i.e. N.

## Modifiers

    fill (A* self, T value)
    fill_n (A* self, size_t n, T value)

fill array with values. On invalid n do nothing.

    swap (A* self, A* other)

swaps the contents.

    #ifdef POD
    clear (A* self)
    #endif

fill with zero. only for POD elements, no pointers.

## Lookup

    size_t count (A* self, T value)

returns the number of elements matching specific key.

    T* find (A* self, T value)

finds element with specific key

    bool equal_range (A* self)

returns range of elements matching a specific key. _(NYI)_

    T* lower_bound (A* self)

returns an iterator to the first element not less than the given key. _(NYI)_

    T* upper_bound (A* self)

returns an iterator to the first element greater than the given key. _(NYI)_

## Observers

    FN value_comp (A* self)

Returns the function that compares keys in objects of type value_type T. _(NYI)_

## Non-member functions

    swap (A* self)

specializes the swap algorithm


See [algorithm](algorithm.md) for more.
