# numeric - CTL - C Container Template library

Defined in header **<ctl/numeric.h>**, requested via `#define INCLUDE_NUMERIC`.

## SYNOPSIS

    #define T int
    #define N 20
    #define INCLUDE_NUMERIC
    #include <ctl/array.h>

    arr20_double_iota (&a, 0);

## DESCRIPTION

The numerics library includes common mathematical functions and types, as
well as optimized numeric arrays and support for random number generation.
It is only included when you define `INCLUDE_NUMERIC` before loading the container.

## Numeric operations

    iota (A* self, T value)
    iota_range (I* range, T value)
 
fills a range with successive increments of the starting value. When T is a
struct, you need to define a `T_inc` postfix increment method, as in `tests/func/digi.hh`,
returning an old copy:

    static digi
    digi_inc(digi* a)
    {
        digi old = digi_init(*a->value);
        (*a->value)++;
        return old;
    }

equivalent to the matching C++ postfix increment operator:

    DIGI operator++(int)
    {
        DIGI old = *this;
        (*value)++;
        return old;
    }


    accumulate
 
sums up a range of elements.

    inner_product
 
computes the inner product of two ranges of elements.

    adjacent_difference
 
computes the differences between adjacent elements in a range.

    partial_sum
 
computes the partial sum of a range of elements.

    reduce (C++17)
 
similar to std::accumulate, except out of order.

    exclusive_scan (C++17)
 
similar to partial_sum, excludes the ith input element from the i-th sum.

    inclusive_scan (C++17)
 
similar to partial_sum, includes the ith input element in the i-th sum.

    transform_reduce (C++17)
 
applies an invocable, then reduces out of order.

    transform_exclusive_scan (C++17)
 
applies an invocable, then calculates exclusive scan.

    transform_inclusive_scan (C++17)
 
applies an invocable, then calculates inclusive scan.
