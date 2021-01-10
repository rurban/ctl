# stack - CTL - C Container Template library

Defined in header **<ctl/stack.h>**, CTL prefix **stack**,
derived from [deque](deque.md).

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/stack.h>

    stack_int a = stack_int_init ();
    for (int i=0; i<rand(); i++)
      stack_int_push (&a, i);
    for (int i=0; i<rand(); i++)
      stack_int_pop (&a); // ignores empty stack

    stack_int_free(&a);

## DESCRIPTION

The stack is a container adapter that gives the programmer the functionality of a stack - specifically, a LIFO (last-in, first-out) data structure.

The header acts as a wrapper to the underlying container - only a
specific set of functions is provided. The stack pushes the elements on the back
of the underlying container and pops them from the front. 

The function names are composed of the prefix **stack_**, the user-defined type
**T** and the method name. E.g `stack_int` with `#define T int`.

As opposed to vector, the elements of a stack are not stored contiguously:
typical implementations use a sequence of individually allocated fixed-size
arrays, with additional bookkeeping, which means indexed access to stack must
perform two pointer dereferences, compared to vector's indexed access which
performs only one.

The storage of a stack is automatically expanded and contracted as
needed. Expansion of a stack is cheaper than the expansion of a vector
because it does not involve copying of the existing elements to a new memory
location. On the other hand, stacks typically have large minimal memory cost; a
stack holding just one element has to allocate its full internal array (e.g. 8
times the object size on 64-bit libstdc++; 16 times the object size or 4096
bytes, whichever is larger, on 64-bit libc++).

## Member types

`T`                       value type

`A` being `stack_T`       container type

`B` being `stack_T_node`  node type (hidden)

`I` being `stack_T_it`    iterator type (hidden)

## Member functions

[init](stack/init.md) `()`

constructs the stack.

[free](stack/free.md) `(A* self)`

destructs the stack.

[copy](stack/copy.md) `(A* self)`

returns a copy of the container.

## Element access

[front](stack/top.md) `(A* self)`

access the first element

## Capacity

[empty](stack/empty.md) `(A* self)`

checks whether the container is empty

[size](stack/size.md) `(A* self)`

returns the number of elements

[max_size](stack/max_size.md) ()

returns the maximum possible number of elements

## Modifiers

[push](stack/push.md) `(A* self, T value)`

Push element before top

[emplace](stack/emplace.md) `(A* self, T values...)`

Push elements before top. C++11, NYI

[pop](stack/pop.md) `(A* self)`

Removes the first element

[swap](stack/swap.md) `(A* self, A* other)`

Swaps the contents

## Non-member functions

[equal](stack/equal.md) `(A* self, A* other, int T_equal(T*, T*))`

Returns 0 or 1 if all elements are equal.
