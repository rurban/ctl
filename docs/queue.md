# queue - CTL - C Container Template library

Defined in header **<ctl/queue.h>**, CTL prefix **queue**,
derived from [deque](deque.md).

# SYNOPSIS

    #undef POD
    #define T int
    #include <ctl/queue.h>

    queue_int a = queue_int_init ();
    for (int i=0; i<rand(); i++)
      queue_int_push (&a, i);
    for (int i=0; i<rand(); i++)
      queue_int_pop (&a); // ignores empty queue

    queue_int_free(&a);

# DESCRIPTION

The queue is a container adapter that gives the programmer the functionality of a queue - specifically, a FIFO (first-in, first-out) data structure.

The header acts as a wrapper to the underlying container - only a
specific set of functions is provided. The queue pushes the elements on the back
of the underlying container and pops them from the front. 

The function names are composed of the prefix **queue_**, the user-defined type
**T** and the method name. E.g `queue_int` with `#define T int`.

As opposed to vector, the elements of a queue are not stored contiguously:
typical implementations use a sequence of individually allocated fixed-size
arrays, with additional bookkeeping, which means indexed access to queue must
perform two pointer dereferences, compared to vector's indexed access which
performs only one.

The storage of a queue is automatically expanded and contracted as
needed. Expansion of a queue is cheaper than the expansion of a vector
because it does not involve copying of the existing elements to a new memory
location. On the other hand, queues typically have large minimal memory cost; a
queue holding just one element has to allocate its full internal array (e.g. 8
times the object size on 64-bit libstdc++; 16 times the object size or 4096
bytes, whichever is larger, on 64-bit libc++).

# Member types

`T`                       value type

`A` being `queue_T`       container type

`B` being `queue_T_node`  node type (hidden)

`I` being `queue_T_it`    iterator type (hidden)

## Member functions

[init](queue/init.md) `()`

constructs the queue.

[free](queue/free.md) `(A* self)`

destructs the queue.

[copy](queue/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[front](queue/front.md) `(A* self)`

access the first element

[back](queue/back.md) `(A* self)`

access the last element

## Capacity

[empty](queue/empty.md) `(A* self)`

checks whether the container is empty

[size](queue/size.md) `(A* self)`

returns the number of elements

[max_size](queue/max_size.md) ()

returns the maximum possible number of elements

## Modifiers

[push](queue/push.md) `(A* self, T value)`

Push element to the end

[emplace](queue/emplace.md) `(A* self, T values...)`

Push elements to the end. C++11, NYI

[pop](queue/pop.md) `(A* self)`

Removes the first element

[swap](queue/swap.md) `(A* self, A* other)`

Swaps the contents

## Non-member functions

[equal](queue/equal.md) `(A* self, A* other, int T_equal(T*, T*))`

Returns 0 or 1 if all elements are equal.
