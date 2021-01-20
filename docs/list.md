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

`I` being `list_T_it`    iterator type

`IT` being `B*`, the return type of iterators.

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

Note: `begin` and `end` return `node*` (`B*`) pointers, not iterators, with
embedding `B*` into `I*`.

    B*/I* begin (A* self)

returns a node pointer to the beginning, different to the STL.

    B*/I* end (A* self)

returns an node pointer to the end, different to the STL.

## Capacity

    int empty (A* self)

checks whether the container is empty.

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements

## Modifiers

    assign (A* self, size_t count, T value)

resizes and sets count elements to the value

    clear (A* self)

clears the contents

    B* insert (A* self, B* node, T value)

inserts value before the element.

    B* insert_count (A* self, B* pos, size_t count, T value)

inserts count values before the element. (NYI)

    B* insert_range (A* self, B* pos, I* first, I* last)

inserts values before pos from first to last. (NYI)

    B* emplace (A* self, B* pos, T* value)

Insert a copy of the value into the container before pos.

    erase (A* self, B* pos)

erases the element at pos.

    erase_range (A* self, I* first, I* last)

erases elements (NYI)

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

    merge (A* self, A* other, int T_compare(T*, T*))

merges two sorted lists.

    splice (A* self, B* pos, A* other)

Moves all elements from the other list to this list before pos.

    splice_it (A* self, B* pos, A* other, B* other_pos)

Moves elements from the other list at pos to this list before pos. (NYI)

    splice_range (A* self, B* pos, A* other, B* other_first, B* other_last)

Moves elements from the other list to this list before pos. (NYI)

    size_t remove (A* self, T* value)

Removes all elements binary equal to the value reference (not value).

    size_t remove_if (A* self, int T_match(T*))

Removes all elements satisfying specific criteria.

    reverse (A* self)

reverse the list elements.

    sort (A* self, int T_compare(T*, T*))

sorts the list in-place.

    unique (A* self, int T_equal(T*, T*))

removes consecutive duplicates.

## Non-member functions

    B* find (A* self, T value, int T_equal(T*, T*))

finds element with specific value.

    erase_if (A* self, int T_match(T*))

erases all elements satisfying specific criteria (C++20)

    int equal (A* self, A* other, int T_equal(T*, T*))

Returns 0 or 1 if all elements are equal.
