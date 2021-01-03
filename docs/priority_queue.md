# priority_queue - CTL - C Container Template library

Defined in header **<ctl/priority_queue.h>**, CTL prefix **pqu**,
derived from [vector](vector.md).

# SYNOPSIS

    static inline int
    int_cmp(int *a, int *b) {
      return *a < *b;
    }

    #undef POD
    #define T int
    #include <ctl/priority_queue.h>

    pqu_int a = pqu_int_init (int_cmp);

    for (i=0; i<1000; i++)
      pqu_int_push(&a, rand());
    for (i=0; i<20; i++)
       pqu_int_pop(&a);

    pqu_int_free(&a);

# DESCRIPTION

A priority queue is a container adaptor that provides constant time lookup of
the largest (by default) element, at the expense of logarithmic insertion and
extraction.

The function names are composed of the prefix **pqu_**, the user-defined type
**T** and the method name. E.g `pqu_int` with `#define T int`.

A user-provided Compare can be supplied to change the ordering, e.g. using
greater<T> would cause the smallest element to appear as the top().

Working with a priority_queue is similar to managing a heap in some random
access container, with the benefit of not being able to accidentally invalidate
the heap. 

# Member types

`T`                     value type

`A` being `pqu_T`       container type

`I` being `pqu_T_it`    iterator type (hidden)

There is no `B` node type.

## Member functions

[init](pqu/init.md) `(int T_compare(T*,T*))`

constructs the priority_queue.

[free](pqu/free.md) `(A* self)`

destructs the priority_queue.

[copy](pqu/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[top](pqu/top.md) `(A* self)`

access the first element

## Capacity

[empty](pqu/empty.md) `(A* self)`

checks whether the container is empty

[size](pqu/size.md) `(A* self)`

returns the number of elements

[max_size](pqu/max_size.md) `()`

returns the maximum possible number of elements

[capacity](pqu/capacity.md) `(A* self)`

returns the number of elements that can be held in currently allocated storage

## Modifiers

[push](pqu/push.md) `(A* self, T key)`

inserts the element

[emplace](pqu/emplace.md) `(A* self, T values...)`

constructs elements in-place. (C++11, NYI)

[pop](pqu/pop.md) `(A* self)`

removes the top element

[swap](pqu/swap.md) `(A* self, A* other)`

swaps the contents
