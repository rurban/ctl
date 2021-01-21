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

`IT` iterators are currently specialized (on `index`).

There is a `B` node type, but iterators use the `I*` type.

## Member fields

with non-POD or NON_INTEGRAL types these fields must be set, if used with sort,
merge, unique, ...

    .compare

Compare method `int (*compare)(T*, T*)`, mandatory for non-integral types.

    .equal

Optional equal `int (*equal)(T*, T*)`. If not set, maximal 2x compare will be called.

## Member functions

    init ()

constructs the deque.

    free (A* self)

destructs the deque.

    copy (A* self)

returns a copy of the container.

## Element access

    at (A* self, size_t index)

access specified element with bounds checking

    front (A* self)

access the first element

    back (A* self)

access the last element

## Iterators

    begin (A* self)

returns an iterator to the beginning

    end (A* self)

returns an iterator to the end

## Capacity

    empty (A* self)

checks whether the container is empty

    size (A* self)

returns the number of elements

[max_size](deq/max_size.md) ()

returns the maximum possible number of elements

    shrink_to_fit (A* self)

reduces memory usage by freeing unused memory.

## Modifiers

    assign (A* self, size_t count, T default_value)

resizes and sets count elements to the default value.

    clear (A* self)

clears the contents

    insert (A* self, size_t index, T value)

inserts the element at index. _(will be replaced by `insert_it` later)_

    I* insert_it (A* self, I* pos, T value)

inserts value before pos. _(will be removed later)_

    I* insert_count (A* self, I* pos, size_t count, T value)

inserts count values before pos.

    I* insert_range (A* self, I* pos, I* first, I* last)

inserts values from range [first, last) before pos.

    emplace (A* self, I* pos, T* value)

Inserts the value reference into the container directly before pos.

    erase (A* self, size_t index)

erases the element at index.  _(will be replaced by `erase_it` later)_

    I* erase_it (A* self, I* pos)

erases the element at pos. _(will be removed later)_

    I* erase_range (A* self, I* first, I* last)

erases elements

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

    T* find (A* self, T value)

finds element with specific value

    T* find_if (A* self, int _match(T*))

finds element by predicate

    T* find_if_not (A* self, int _match(T*))

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

    sort_range (A* self, I* first, I* last)

Sorts the elements in the range `[first, last)` in non-descending order.

See [algorithm](algorithm.md) for more.

