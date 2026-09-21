# span - CTL - C Container Template library

Defined in header **<ctl/span.h>**, CTL prefix **span**.

## SYNOPSIS

    #define T int
    #include <ctl/span.h>

    int values[] = {1, 2, 3, 4, 5};
    span_int view = span_int_init(values, 5);
    span_int tail = span_int_subspan(&view, 1, 3);
    for (int *it = span_int_begin(&view); it != span_int_end(&view); it++)
      printf("%d ", *it);

## DESCRIPTION

`span` (comparable to C++20 `std::span`) is a **non-owning** view over a
contiguous run of `T`. It stores only a pointer and a size; it never
allocates, copies, or frees. The viewed storage — a plain array, a
`vector`'s `data()`, an `array`'s storage, or any other contiguous buffer —
must outlive the span.

The function names are composed of the prefix **span_**, the user-defined
type **T** and the method name. E.g. `span_int` with `#define T int`.

## Member functions

    A init (T* data, size_t size)

constructs a view over `[data, data + size)`.

## Element access

    T* data (A* self)
    T* at (A* self, size_t index)      // asserts in-range
    T* front (A* self)
    T* back (A* self)

## Iterators

    T* begin (A* self)
    T* end (A* self)

Plain pointers; usable directly in a `for` loop or with `<ctl/algorithm.h>`
pointer ranges.

## Capacity

    int empty (A* self)

`size` and `capacity` are the `size` struct field directly; there is no
growth, so no separate accessor is needed beyond reading `self->size`.

## Views

    A subspan (A* self, size_t offset, size_t count)

a view over `[offset, offset + count)`. `count` is clamped to the
available length, so passing `SIZE_MAX` yields "to the end".

    A first (A* self, size_t count)
    A last (A* self, size_t count)

the leading/trailing `count` elements.
