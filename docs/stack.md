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

As opposed to vector, the elements of a stack (ie deque) are not stored
contiguously, but in pages of fixed-size arrays, with additional bookkeeping,
which means indexed access to deque must perform two pointer dereferences,
compared to vector's indexed access which performs only one.

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

    A init ()

constructs the stack.

    free (A* self)

destructs the stack.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* front (A* self)

access the first element

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

## Modifiers

    push (A* self, T value)

Push element before top

    emplace (A* self, T* value)

Push elements before top. C++11 _(NYI)_

    pop (A* self)

Removes the first element

    swap (A* self, A* other)

Swaps the contents

## Non-member functions

    int equal (A* self, A* other, int T_equal(T*, T*))

Returns 0 or 1 if all elements are equal.


No [algorithm](algorithm.md) applicable, as we have no iterators.

