# queue - CTL - C Container Template library

Defined in header **<ctl/queue.h>**, CTL prefix **queue**,
derived from [deque](deque.md).

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/queue.h>

    queue_int a = queue_int_init ();
    for (int i=0; i<rand(); i++)
      queue_int_push (&a, i);
    for (int i=0; i<rand(); i++)
      queue_int_pop (&a); // ignores empty queue

    queue_int_free(&a);

## DESCRIPTION

The queue is a container adapter that gives the programmer the functionality of
a queue - specifically, a FIFO (first-in, first-out) data structure.

The header acts as a wrapper to the underlying container - only a
specific set of functions is provided. The queue pushes the elements on the back
of the underlying container and pops them from the front. 

The function names are composed of the prefix **queue_**, the user-defined type
**T** and the method name. E.g `queue_int` with `#define T int`.

As opposed to vector, the elements of a queue (ie deque) are not stored
contiguously, but in pages of fixed-size arrays, with additional bookkeeping,
which means indexed access to deque must perform two pointer dereferences,
compared to vector's indexed access which performs only one.

The storage of a queue is automatically expanded and contracted as
needed. Expansion of a queue is cheaper than the expansion of a vector
because it does not involve copying of the existing elements to a new memory
location. On the other hand, queues typically have large minimal memory cost; a
queue holding just one element has to allocate its full internal array (e.g. 8
times the object size on 64-bit libstdc++; 16 times the object size or 4096
bytes, whichever is larger, on 64-bit libc++).

## Member types

`T`                       value type

`A` being `queue_T`       container type

`B` being `queue_T_node`  node type (hidden)

`I` being `queue_T_it`    iterator type (hidden)

## Member functions

    A init ()

constructs the queue.

    free (A* self)

destructs the queue.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* front (A* self)

access the first element

    T* back (A* self)

access the last element

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

## Modifiers

    push (A* self, T value)

Push element to the end

    emplace (A* self, T* value)

Push possibly uninitialized element to the end. (C++11) _(NYI)_

    pop (A* self)

Removes the first element

    swap (A* self, A* other)

Swaps the contents of both containers.

## Non-member functions

    int equal (A* self, A* other, int T_equal(T*, T*))

Returns 0 or 1 if all elements are equal.


No [algorithm](algorithm.md) applicable, as we have no iterators.
