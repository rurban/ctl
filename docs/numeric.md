# numeric - CTL - C Container Template library

Defined in header **<ctl/numeric.h>** (NYI)

## SYNOPSIS

_TODO_

## DESCRIPTION

The numerics library includes common mathematical functions and types, as
well as optimized numeric arrays and support for random number generation.

## Numeric operations

    iota (C++11)
 
fills a range with successive increments of the starting value

    accumulate
 
sums up a range of elements

    inner_product
 
computes the inner product of two ranges of elements

    adjacent_difference
 
computes the differences between adjacent elements in a range

    partial_sum
 
computes the partial sum of a range of elements

    reduce (C++17)
 
similar to std::accumulate, except out of order

    exclusive_scan (C++17)
 
similar to partial_sum, excludes the ith input element from the ith sum

    inclusive_scan (C++17)
 
similar to partial_sum, includes the ith input element in the ith sum

    transform_reduce (C++17)
 
applies an invocable, then reduces out of order

    transform_exclusive_scan (C++17)
 
applies an invocable, then calculates exclusive scan

    transform_inclusive_scan (C++17)
 
applies an invocable, then calculates inclusive scan
