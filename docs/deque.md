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

**deque** ("double-ended queue") is an indexed sequence container that allows fast
insertion and deletion at both its beginning and its end. In addition, insertion
and deletion at either end of a deque never invalidates pointers or references
to the rest of the elements.

The function names are composed of the prefix **deq_**, the user-defined type
**T** and the method name. E.g `deq_int` with `#define T int`.

As opposed to vector, the elements of a deque are not stored contiguously, but
in pages of fixed-size arrays, with additional bookkeeping, which means indexed
access to deque must perform two pointer dereferences, compared to vector's
indexed access which performs only one.

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

There is a `B` node type, but iterators use the `I` type.

## Member fields

with non-POD or NON_INTEGRAL types these fields must be set, if used with sort,
merge, unique, ...

    .compare

Compare method `int (*compare)(T*, T*)`, mandatory for non-integral types.

    .equal

Optional equal `int (*equal)(T*, T*)`. If not set, maximal 2x compare will be called.

## Member functions

    A init ()

constructs the deque.

    free (A* self)

destructs the deque.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* at (A* self, size_t index)

access specified element with bounds checking

    T* front (A* self)

access the first element

    T* back (A* self)

access the last element

## Iterators

    I begin (A* self)

constructs an iterator to the beginning

    I end (A* self)

constructs an iterator to the end

    I* next (I* iter)

Advances the iterator by 1 forwards. There's no prev yet.

    I* advance (I* iter, long i)

All our variants accepts negative `i` to move back. The return value may be ignored.


See [iterators](iterators.md) for more.

## Capacity

    empty (A* self)

checks whether the container is empty

    size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

    shrink_to_fit (A* self)

reduces memory usage by freeing unused memory.

## Modifiers

    assign (A* self, size_t count, T default_value)

resizes and sets count elements to the default value.

    clear (A* self)

clears the contents

    insert_index (A* self, size_t index, T value)

inserts the element at index.

    I* insert (I* pos, T value)

inserts value before pos.

    I* insert_count (I* pos, size_t count, T value)

inserts count values before pos.

    insert_range (I* pos, I* range2)

inserts copies of values from range [first, last) before pos.

    insert_generic (A* self, GI* range2)

inserts copies of values from generic range2. _(NYI)_

    emplace (I* pos, T* value)

Inserts the value reference into the container directly before pos.

    size_t erase_index (A* self, size_t index)

erases the element at index.

    I* erase (I* pos)

erases the element at pos.

    I* erase_range (I* range)

erases elements.

    erase_generic (A* self, GI* range2)

erases elements by value from another container.

    push_front (A* self, T value)

inserts an element to the beginning

    emplace_front (A* self, T* value)

inserts the value reference to the beginning.

    push_back (A* self, T value)

inserts an element to the end.

    emplace_back (A* self, T* value)

adds the value reference to the end.

    pop_front (A* self)

removes the first element

    pop_back (A* self)

removes the last element

    resize (A* self, size_t count, T default_value)

Resizes the container to contain count elements.

    swap (A* self, A* other)

swaps the contents

## Non-member functions

    I find (A* self, T value)

finds element with specific value

    I find_if (A* self, int _match(T*))

finds element by predicate

    I find_if_not (A* self, int _match(T*))

finds element by predicate

    size_t remove_if (A* self, int T_match(T*))
    size_t erase_if (A* self, int T_match(T*)) (C++20)

Remove all elements satisfying specific criteria.

    int equal (A* self, A* other)

Returns 0 or 1 if all elements are equal.

    sort (A* self)

Sorts the elements in non-descending order.
Currently it's a `stable_sort`, i.e. the order of equal elements is preserved.
(a merge-sort)

    sort_range (I* range)

Sorts the elements in the range `[first, last)` in non-descending order.


See [algorithm](algorithm.md) for more.

