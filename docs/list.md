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

## Member functions

[init](list/init.md) `()`

constructs an empty list.

[free](list/free.md) `(A* self)`

destructs the list.

[copy](list/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[front](list/front.md) `(A* self)`

access the first element

[back](list/back.md) `(A* self)`

access the last element

## Iterators

Note: `begin` and `end` return `node*` (`B*`) pointers, not iterators.

[begin](list/begin.md) `(A* self)`

returns a node pointer to the beginning, different to the STL.

[end](list/end.md) `(A* self)`

returns an node pointer to the end, different to the STL.

## Capacity

[empty](list/empty.md) `(A* self)`

checks whether the container is empty

[size](list/size.md) `(A* self)`

returns the number of elements

[max_size](list/max_size.md) ()

returns the maximum possible number of elements

## Modifiers

[assign](list/assign.md) `(A* self, size_t count, T value)`

resizes and sets count elements to the value

[clear](list/clear.md) `(A* self)`

clears the contents

[insert](list/insert.md) `(A* self, B* node, T value)`

inserts value before the element.

[insert_count](list/insert.md) `(A* self, I* pos, size_t count, T value)`

inserts count values before the element. (NYI)

[insert_range](list/insert.md) `(A* self, I* pos, I* first, I* last)`

inserts values before pos from first to last. (NYI)

[emplace](list/emplace.md) `(A* self, B* pos, T* value)`

Insert a copy of the value into the container before pos.

[erase](list/erase.md) `(A* self, B* pos)`

erases the element at pos.

[erase_range](list/erase.md) `(A* self, I* first, I* last)`

erases elements (NYI)

[push_front](list/push_front.md) `(A* self, T value)`

inserts an element to the beginning.

[emplace_front](list/emplace_front.md) `(A* self, T *value)`

inserts a copy of the value at the beginning.

[push_back](list/push_back.md) `(A* self, T value)`

inserts an element to the end.

[emplace_back](map/emplace_back.md) `(A* self, T* value)`

adds a copy of the value at the end.

[pop_front](list/pop_front.md) `(A* self)`

removes the first element

[pop_back](list/pop_back.md) `(A* self)`

removes the last element

[resize](list/resize.md) `(A* self, size_t count, T default_value)`

Resizes the container to contain count elements.

[swap](list/swap.md) `(A* self, A* other)`

swaps the contents

## Operations

[merge](list/merge.md) `(A* self, A* other, int T_compare(T*, T*))`

merges two sorted lists.

[splice](list/splice.md) `(A* self, B* pos, A* other)`

Moves all elements from the other list to this list before pos.

[splice_it](list/splice.md) `(A* self, B* pos, A* other, B* other_pos)`

Moves elements from the other list at pos to this list before pos. (NYI)

[splice_range](list/splice.md) `(A* self, B* pos, A* other, B* other_first, B* other_last)`

Moves elements from the other list to this list before pos. (NYI)

[remove](list/remove.md) `(A* self, T* value)`

Removes all elements binary equal to the value reference. (not value)

[remove_if](list/remove.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[reverse](list/reverse.md) `(A* self)`

reverse the list elements.

[sort](list/sort.md) `(A* self, int T_compare(T*, T*))`

sorts the list.

[unique](list/unique.md) `(A* self, int T_equal(T*, T*))`

removes consecutive duplicates.

## Non-member functions

[find](list/find.md) `(A* self, T value, int T_equal(T*, T*))`

finds element with specific value

[erase_if](list/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20) NYI

[equal](list/equal.md) `(A* self, A* other, int T_equal(T*, T*))`

Returns 0 or 1 if all elements are equal.
