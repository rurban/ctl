# memory - CTL - C Container Template library

Defined in header **<ctl/memory.h>** (NYI)

## SYNOPSIS

_TODO_

## DESCRIPTION

The memory library implements functions on uninitialized memory.

## Operations on uninitialized memory

    uninitialized_copy
    uninitialized_copy_range (C++20)
 
copies a range of objects to an uninitialized area of memory

    uninitialized_copy_n (C++11)
    uninitialized_copy_n_range (C++20)
 
copies a number of objects to an uninitialized area of memory
 
    uninitialized_fill
    uninitialized_fill_range (C++20)
 
copies an object to an uninitialized area of memory, defined by a range
 
    uninitialized_fill_n
    uninitialized_fill_n_range (C++20)
 
copies an object to an uninitialized area of memory, defined by a start and a count

    uninitialized_move (C++17)
    uninitialized_move_range (C++20)
 
moves a range of objects to an uninitialized area of memory
 
    uninitialized_move_n (C++17)
    uninitialized_move_n_range (C++20)
 
moves a number of objects to an uninitialized area of memory
 
    uninitialized_default_construct (C++17)
    uninitialized_default_construct_range (C++20)
 
constructs objects by default-initialization in an uninitialized area of memory, defined by a range
 
    uninitialized_default_construct_n (C++17)
    uninitialized_default_construct_n_range (C++20)
 
constructs objects by default-initialization in an uninitialized area of memory, defined by a start and a count
 
    uninitialized_value_construct (C++17)
    uninitialized_value_construct_range (C++20)
 
constructs objects by value-initialization in an uninitialized area of memory, defined by a range

    uninitialized_value_construct_n (C++17)
    uninitialized_value_construct_n_range (C++20)
 
constructs objects by value-initialization in an uninitialized area of memory, defined by a start and a count

    destroy (C++17)
    destroy_range (C++20)

destroys a range of objects

    destroy_n (C++17)
    destroy_n_range (C++20)
 
destroys a number of objects in a range

    destroy_at (C++17)
    destroy_at_range (C++20)

destroys an object at a given address

    construct_at (C++20)
    construct_at_range (C++20)
 
creates an object at a given address

