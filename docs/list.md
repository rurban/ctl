# list - CTL - C Container Template library

Defined in header **<ctl/list.h>**, CTL prefix **list**.

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/list.h>

    int i = 0;
    list_int a = list_int_init ();

    for (i=0; i<100; i++) {
      list_int_push_front (&a, i);
      list_int_push_back (&a, i);
      list_int_pop_front (&a, i);
      list_int_pop_back (&a, i);
    }

    foreach(list_int, &a, it) { printf "%d ", *it.ref); }

    list_int_free(&a);

## DESCRIPTION

list, a double-linked list, is a container that supports constant time insertion
and removal of elements from anywhere in the container. Fast random access is
not supported. It is usually implemented as a doubly-linked list. Compared to
forward_list this container provides bidirectional iteration capability
while being less space efficient.

The function names are composed of the prefix **list_**, the user-defined type
**T** and the method name. E.g `list_int` with `#define T int`.

Adding, removing and moving the elements within the list or across several lists
does not invalidate the iterators or references.

Note:
Most function accepting or returning iterators, use return `node*` (`B*`)
pointers instead.

## Member types

`T`                     value type

`A` being `list_T`       container type

`B` being `list_T_node`  node type

`I` being `list_T_it`    internal iterator type for loops

## Member functions

    A init ()

constructs an empty list.

    free (A* self)

destructs the list.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* front (A* self)

access the first element

    T* back (A* self)

access the last element

## Iterators

    I begin (A* self)

Constructs an iterator to the begin.

    I end (A* self)

constructs an iterator to the end.

    I* next (I* iter)

Advances the iterator by 1 forwards. There's no prev yet.

    I* advance (I* iter, long i)

All our variants accepts negative `i` to move back. The return value may be ignored.


See [iterators](iterators.md) for more.

## Capacity

    int empty (A* self)

checks whether the container is empty.

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

## Modifiers

    assign (A* self, size_t count, T value)

resizes and sets count elements to the value

    clear (A* self)

clears the contents

    I* insert (I* pos, T value)

inserts value before the element.

    I* insert_count (I* pos, size_t count, T value)

inserts count copies of value before the element.

    I* insert_range (I* pos, I* range2)

inserts copies of values from first to last before pos.

    I* emplace (I* pos, T* value)

Insert the value into the container before pos.

    erase_node (A* self, B* node)
    erase (I* pos)

erases the element.

    I* erase_range (I* range)

erases elements.

    push_front (A* self, T value)

inserts an element to the beginning.

    B* emplace_front (A* self, T *value)

inserts a copy of the value at the beginning.

    push_back (A* self, T value)

inserts an element to the end.

    B* emplace_back (A* self, T* value)

adds a copy of the value at the end.

    pop_front (A* self)

removes the first element

    pop_back (A* self)

removes the last element

    resize (A* self, size_t count, T default_value)

Resizes the container to contain count elements.

    swap (A* self, A* other)

swaps the contents

## Operations

    merge (A* self, A* other)

merges two sorted lists.

    splice (I* pos, A* other)

Moves all elements from the other list to this list before pos.

    splice_it (I* pos, I* range2)

Moves the element first2 from the other list to this list before pos.

    splice_range (I* pos, I* range2)

Moves a range of elements from the other list to this list before pos.

    size_t remove (A* self, T value)

Removes all elements binary equal to the value.

    size_t remove_if (A* self, int match(T*))

Removes all elements satisfying specific criteria.

    reverse (A* self)

reverse the list elements.

    sort (A* self)

sorts the list in-place.

    unique (A* self)

removes consecutive duplicates.

## Non-member functions

    I find (A* self, T value, int equal(T*,T*))

finds element with specific value.

    size_t erase_if (A* self, int match(T*))

erases all elements satisfying specific criteria (C++20)

    int equal (A* self, A* other, int equal(T*,T*))

Returns 0 or 1 if all elements are equal.


See [algorithm](algorithm.md) for more.
