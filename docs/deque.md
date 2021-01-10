# deque - CTL - C Container Template library

Defined in header **<ctl/deque.h>**, CTL prefix **deq**,
parent for [queue](queue.md) and [stack](stack.md).

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/deque.h>

    deq_int a = deq_int_init ();
    deq_int_resize (&a, 100, 0);

    for (int i=0; i<100; i++) {
      deq_int_push_front (&a, i);
      deq_int_push_back (&a, i);
      deq_int_pop_front (&a, i);
      deq_int_pop_back (&a, i);
    }

    foreach(deq_int, &a, it) { printf "%d ", *it.ref); }

    deq_int_free(&a);

## DESCRIPTION

deque ("double-ended queue") is an indexed sequence container that allows fast
insertion and deletion at both its beginning and its end. In addition, insertion
and deletion at either end of a deque never invalidates pointers or references
to the rest of the elements.

The function names are composed of the prefix **deq_**, the user-defined type
**T** and the method name. E.g `deq_int` with `#define T int`.

As opposed to vector, the elements of a deque are not stored contiguously:
typical implementations use a sequence of individually allocated fixed-size
arrays, with additional bookkeeping, which means indexed access to deque must
perform two pointer dereferences, compared to vector's indexed access which
performs only one.

The storage of a deque is automatically expanded and contracted as
needed. Expansion of a deque is cheaper than the expansion of a vector
because it does not involve copying of the existing elements to a new memory
location. On the other hand, deques typically have large minimal memory cost; a
deque holding just one element has to allocate its full internal array (e.g. 8
times the object size on 64-bit libstdc++; 16 times the object size or 4096
bytes, whichever is larger, on 64-bit libc++).

The complexity (efficiency) of common operations on a `deque` is as follows:

* Random access - constant 𝓞(1)
* Insertion or removal of elements at the end or beginning - constant 𝓞(1)
* Insertion or removal of elements - linear 𝓞(n)

## Member types

`T`                     value type

`A` being `deq_T`       container type

`B` being `deq_T_node`  node type

`I` being `deq_T_it`    iterator type

## Member fields

with non-POD or NON_INTEGRAL types these fields must be set, if used with sort,
merge, unique, ...

[`.compare`](uset/.compare.md)

Compare method `int (*compare)(T*, T*)`

[`.equal`](uset/.equal.md)

Optional equal `int (*equal)(T*, T*)`. If not set, maximal 2x compare will be called.

## Member functions

[init](deq/init.md) `()`

constructs the deque.

[free](deq/free.md) `(A* self)`

destructs the deque.

[copy](deq/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[at](deq/at.md) `(A* self, size_t index)`

access specified element with bounds checking

[front](deq/front.md) `(A* self)`

access the first element

[back](deq/back.md) `(A* self)`

access the last element

## Iterators

[begin](deq/begin.md) `(A* self)`

returns an iterator to the beginning

[end](deq/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](deq/empty.md) `(A* self)`

checks whether the container is empty

[size](deq/size.md) `(A* self)`

returns the number of elements

[max_size](deq/max_size.md) ()

returns the maximum possible number of elements

[shrink_to_fit](deq/shrink_to_fit.md) `(A* self)`

reduces memory usage by freeing unused memory.

## Modifiers

[assign](deq/assign.md) `(A* self, size_t count, T default_value)`

resizes and sets count elements to the default value.

[clear](deq/clear.md) `(A* self)`

clears the contents

[insert](deq/insert.md) `(A* self, size_t index, T value)`

inserts the element at index.

[insert_it](deq/insert.md) `(A* self, I* pos, T value)`

inserts value before pos.

[insert_count](deq/insert.md) `(A* self, I* pos, size_t count, T value)`

inserts count values before pos.

[insert_range](deq/insert.md) `(A* self, I* pos, I* first, I* last)`

inserts values from range [first, last) before pos.

[emplace](deq/emplace.md) `(A* self, I* pos, T* value)`

Inserts the value reference into the container directly before pos.

[erase](deq/erase.md) `(A* self, size_t index)`

erases the element at index

[erase_it](deq/erase.md) `(A* self, I* pos)`

erases the element at pos

[erase_range](deq/erase.md) `(A* self, I* first, I* last)`

erases elements

[push_front](deq/push_front.md) `(A* self, T value)`

inserts an element to the beginning

[emplace_front](deq/emplace_front.md) `(A* self, T* value)`

inserts the value reference to the beginning.

[push_back](deq/push_back.md) `(A* self, T value)`

inserts an element to the end.

[emplace_back](map/emplace_back.md) `(A* self, T* value)`

adds the value reference to the end.

[pop_front](deq/pop_front.md) `(A* self)`

removes the first element

[pop_back](deq/pop_back.md) `(A* self)`

removes the last element

[resize](deq/resize.md) `(A* self, size_t count, T default_value)`

Resizes the container to contain count elements.

[swap](deq/swap.md) `(A* self, A* other)`

swaps the contents

## Non-member functions

[find](deq/find.md) `(A* self, T value)`

finds element with specific value

[find_if](algorithm/find_if.md) `(A* self, int _match(T*))`

finds element by predicate

[find_if_not](algorithm/find_if.md) `(A* self, int _match(T*))`

finds element by predicate

[remove_if](deq/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](deq/erase_if.md) `(A* self, int T_match(T*))`

erases all elements satisfying specific criteria (C++20)

[equal](deq/equal.md) `(A* self, A* other)`

Returns 0 or 1 if all elements are equal.

[sort](deq/sort.md) `(A* self)`

Sorts the elements in non-descending order.
Currently it's a stable_sort, i.e. the order of equal elements is preserved.
(merge-sort)

[sort_range](deq/sort.md) `(A* self, I* first, I* last)`

Sorts the elements in the range `[first, last)` in non-descending order.

[all_of](algorithm/all_of.md) `(A* self, int _match(T*))`

[any_of](algorithm/any_of.md) `(A* self, int _match(T*))`

[none_of](algorithm/none_of.md) `(A* self, int _match(T*))`

[all_of_range](algorithm/all_of.md) `(A* self, I* first, I* last, int _match(T*))`

[any_of_range](algorithm/any_of.md) `(A* self, I* first, I* last, int _match(T*))`

[none_of_range](algorithm/none_of.md) `(A* self, I* first, I* last, int _match(T*))`
