# inplace_vector - CTL - C Container Template library

Defined in header **<ctl/inplace_vector.h>**, CTL prefix **inplace_vecN**.

## SYNOPSIS

    #define POD
    #define N 8
    #define T int
    #include <ctl/inplace_vector.h>

    inplace_vec8_int a = inplace_vec8_int_init();
    for (int i = 0; i < 8; i++)
      inplace_vec8_int_push_back(&a, i);
    // full: try_push_back returns NULL instead of overflowing
    assert(inplace_vec8_int_try_push_back(&a, 99) == NULL);
    inplace_vec8_int_free(&a);

## DESCRIPTION

**inplace_vector** (C++26) is a dynamically-resizable, **fixed-capacity**,
contiguous array whose elements live **inline** in the container object -- it
never touches the heap. The capacity is the compile-time constant `N`; the size
grows and shrinks in `[0, N]`.

Requires both `T` and `N`, like [array](array.md). The type name embeds `N`:
`#define N 8` / `#define T int` yields `inplace_vec8_int`. Two inplace_vectors
of different `N` are distinct types.

The function names are composed of the prefix **inplace_vec**`N`**_**, the type
**T** and the method name.

## Member types

`T`                              value type

`A` being `inplace_vecN_T`       container type

`I` being `inplace_vecN_T_it`    iterator type

## Member functions

    A init (void)
    free (A* self)
    A copy (A* self)

For non-POD `T` set `self.compare` before calling `sort`/`find`.

## Element access

    T* at (A* self, size_t index)      // bounds-checked
    T  get (A* self, size_t index)
    T* front (A* self)
    T* back (A* self)
    T* data (A* self)                  // contiguous storage

## Iterators

    I begin (A* self)
    I end (A* self)
    I* advance (I* iter, long i)

See [iterators](iterators.md).

## Capacity

    int empty (A* self)
    size_t size (A* self)
    size_t capacity (A* self)          // always N
    size_t max_size (void)             // N

## Modifiers

    push_back (A* self, T value)

appends value; asserts (and, in NDEBUG, drops the value) when already at N.

    T* try_push_back (A* self, T value)

appends value and returns its slot, or returns NULL (freeing value) when full.

    emplace_back (A* self, T* value)

    pop_back (A* self)

    insert_index (A* self, size_t index, T value)
    void insert (I* pos, T value)

inserts value at index / before pos (asserts on capacity).

    I erase_index (A* self, size_t index)
    I erase (I* pos)
    I* erase_range (I* range)

    resize (A* self, size_t size, T value)
    assign (A* self, size_t count, T value)

grow with copies of value / replace contents; both clamp/assert to `N`.

    clear (A* self)
    swap (A* self, A* other)

## Operations

    sort (A* self)                     // needs compare
    I find (A* self, T key)
    size_t remove_if (A* self, int match(T*))
    size_t erase_if  (A* self, int match(T*))
