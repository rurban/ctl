# forward_list - CTL - C Container Template library

Defined in header **<ctl/forward_list.h>**, CTL prefix **slist**.

This is still in development.

## SYNOPSIS

    bool int_eq(int* a, int* b) {
       return *a == *b;
    }
    int int_is_odd(int* a) {
       return *a % 2;
    }

    #define POD
    #define T int
    #include <ctl/forward_list.h>

    int i = 0;
    slist_int a = slist_int_init ();

    for (i=0; i<100; i++)
      slist_int_push_front (&a, rand());
    for (i=0; i<50; i++)
      slist_int_pop_front (&a);

    slist_int_sort (&a);
    slist_int_reverse (&a);
    slist_int_unique (&a, int_eq);
    foreach(slist_int, &a, it) { printf "%d ", *it.ref); }
    slist_int_find (&a, 1, int_eq);
    slist_int_erase_if (&a, 1, int_is_odd);
    foreach(slist_int, &a, it) { printf "%d ", *it.ref); }

    slist_int_free(&a);

## DESCRIPTION

forward_list, a singly-linked list, is a container that supports fast insertion
and removal of elements from anywhere in the container. Fast random access is
not supported. Compared to list this container provides more space efficient
storage when bidirectional iteration is not needed.

Adding, removing and moving the elements within the list, or across several
lists, does not invalidate the iterators currently referring to other elements
in the list. However, an iterator or reference referring to an element is
invalidated when the corresponding element is removed (via `erase_after`) from the
list.

The function names are composed of the prefix **slist_**, the user-defined type
**T** and the method name. E.g `slist_int` with `#define T int`.

## Member types

`T`                       value type

`A` being `slist_T`       container type

`B` being `slist_T_node`  node type

`I` being `slist_T_it`    iterator type

## Member functions

    A init ()

constructs the list.

    free (A* self)

destructs the list.

    assign (A* self, size_t count, T value)

resizes and sets count elements to the value

    A copy (A* self)

returns a copy of the container.

## Element access

    T* front (A* self)

access the first element

## Iterators

    I begin (A* self)

returns an iterator to the beginning

    I end (A* self)

returns an iterator to the end

    I* next (I* iter)

Advances the iterator by 1 forwards. There's no prev yet.

    I* advance (I* iter, long i)

All our variants accepts negative `i` to move back. The return value may be ignored.


See [iterators](iterators.md) for more.

## Capacity

    empty (A* self)

checks whether the container is empty

    size_t max_size ()

returns the maximum possible number of elements. _(unused)_

## Modifiers

    clear (A* self)

clears the contents

    insert_after (A* self, I* pos, T value)

inserts value after pos.

    insert_count (A* self, I* pos, size_t count, T value)

inserts count values after pos.

    insert_range (A* self, I* pos, GI* range)

inserts values after pos from first to last.

    emplace_after (A* self, I* pos, T *value)

Inserts value into the container after pos.

    B* erase_after (A* self, B* node)

erases the element after node. If `node == NULL`, erases the head; similar to
the STL `before_begin()` iterator.

    erase_range (A* self, I* range)

erases ell elements after `range->node` until before `range->end`.

    push_front (A* self, T value)

inserts an element to the beginning

    emplace_front (A* self, T *value)

inserts element at the beginning

    pop_front (A* self)

removes the first element

    swap (A* self, A* other)

swaps the contents

## Operations

    A merge (A* self, A* other)

merges two sorted lists.

    splice_after (A* self, I* pos, A* other)

Moves all elements from the other list to this list after pos.

    splice_it (A* self, I* pos, I* other_pos)

Moves elements from the other list at pos to this list before pos. _(NYI)_

    splice_range (A* self, I* pos, I* other)

Moves a range of elements from the other list to this list before pos.

    remove (A* self, T value)

Removes all elements binary equal to the value.

    remove_if (A* self, int T_match(T*))

Removes all elements satisfying specific criteria.

    reverse (A* self)

reverse the list elements in place.

   sort (A* self)`

sorts the list.

    unique (A* self)

removes consecutive duplicates.

## Non-member functions

    I find (A* self, T value)

finds element with specific value

    erase_if (A* self, int T_match(T*))

erases all elements satisfying specific criteria (C++20) _(NYI)_

    int equal (A* self, A* other)

Returns 0 or 1 if all elements are equal.
