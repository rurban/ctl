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

[init](slist/init.md) `()`

constructs the list.

[free](slist/free.md) `(A* self)`

destructs the list.

[assign](slist/assign.md) `(A* self, size_t count, T value)`

resizes and sets count elements to the value

[copy](slist/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[front](slist/front.md) `(A* self)`

access the first element

## Iterators

[begin](slist/begin.md) `(A* self)`

returns an iterator to the beginning

[end](slist/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](slist/empty.md) `(A* self)`

checks whether the container is empty

    size_t max_size ()

returns the maximum possible number of elements

## Modifiers

[clear](slist/clear.md) `(A* self)`

clears the contents

[insert_after](slist/insert_after.md) `(A* self, I* pos, T value)`

inserts value after pos.

[insert_count](slist/insert_after.md) `(A* self, I* pos, size_t count, T value)`

inserts count values after pos.

[insert_range](slist/insert_after.md) `(A* self, I* pos, I* first, I* last)`

inserts values after pos from first to last.

[emplace_after](slist/emplace_after.md) `(A* self, I* pos, T values...)`

Inserts values into the container after pos.

[erase_after](slist/erase_after.md) `(A* self, I* pos)`

erases the element at pos

[erase_range](slist/erase.md) `(A* self, I* first, I* last)`

erases elements

[push_front](slist/push_front.md) `(A* self, T value)`

inserts an element to the beginning

[emplace_front](slist/emplace_front.md) `(A* self, T values...)`

inserts elements to the beginning

[pop_front](slist/pop_front.md) `(A* self)`

removes the first element

[resize](slist/resize.md) `(A* self, size_t count)`

Resizes the container to contain count elements.

[swap](slist/swap.md) `(A* self, A* other)`

swaps the contents

## Operations

[merge](slist/merge.md) `(A* self, A* other, int T_compare(T*, T*))`

merges two sorted lists.

[splice_after](slist/splice.md) `(A* self, I* pos, A* other)`

Moves all elements from the other list to this list after pos.

[splice_it](slist/splice.md) `(A* self, I* pos, A* other, I* other_pos)`

Moves elements from the other list at pos to this list before pos.

[splice_range](slist/splice.md) `(A* self, I* pos, A* other, I* other_first, I* other_last)`

Moves elements from the other list to this list before pos.

[remove](slist/remove.md) `(A* self, T value)`

Removes all elements binary equal to the value.

[remove_if](slist/remove.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[reverse](slist/reverse.md) `(A* self)`

reverse the list elements.

[sort](slist/sort.md) `(A* self, int T_compare(T*, T*))`

sorts the list.

[unique](slist/unique.md) `(A* self, int T_equal(T*, T*))`

removes consecutive duplicates.

## Non-member functions

[find](slist/find.md) `(A* self, T value, int T_equal(T*, T*))`

finds element with specific value

[erase_if](slist/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20) NYI

[equal](slist/equal.md) `(A* self, A* other, int T_equal(T*, T*))`

Returns 0 or 1 if all elements are equal.
