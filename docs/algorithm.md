# algorithm - CTL - C Container Template library

Defined in header **<ctl/algorithm.h>**, which is always included for all containers.

## SYNOPSIS

    #include <ctl/deque.h>
    int int_is_odd(int* a) {
       return *a % 2;
    }

    deq_int a = deq_int_init ();
    deq_int_resize (&a, 100);
    for (int i=0; i<100; i++)
      deq_int_push_front (&a, rand());
      
    printf ("%zu odd members in deque\n",
      deq_int_count_if (&a, is_odd));

    deq_int_free(&a);

## DESCRIPTION

The algorithms library implements functions for a variety of purposes
(e.g. searching, sorting, counting, manipulating) that operate on all or on
ranges of elements via generic iterators. Note that a range is defined as
`[first, last)` where last refers to the element past the last element to
inspect or modify.
range variants are specified with the `_range` suffix, without they operate on
all elements on the container.

There are no execution policies yet, but I am planning a **pctl**,
i.e. `parallel_policy` and `parallel_unsequenced_policy`
for various backends like openmp or TBB.

## Member types

`T`                      value type

`A` being `list_T`       container type

`B` being `list_T_node`  node type

`I` being `list_T_it`    iterator type for `begin()` and `end()`

`IT` being either `T*` or `B*`, the return type of iterators.

## Non-modifying sequence operations

    all_of (A* self, int _match(T*)) (C++11)
    any_of `(A* self, int _match(T*)) (C++11)
    none_of (A* self, int _match(T*)) (C++11)
    all_of_range (A* self, IT first, IT last, int _match(T*)) (C++20)
    any_of_range (A* self, IT first, IT last, int _match(T*)) (C++20)
    none_of_range (A* self, IT first, IT last, int _match(T*)) (C++20)

checks if a predicate is true for all, any or none of the elements in a range

    foreach (A, IT, self, iter)
    foreach_range (A, IT, iter, first, last) (C++20)
 
applies a function to a range of elements and sets IT iter.
 
    foreach_ref (A, T, IT, self, iter, ref)
    foreach_range_ref (A, T, IT, iter, ref, first, last) (C++20)
 
applies a function to a range of elements and sets IT iter, and `T*` ref.

    foreach_n (A, T, IT, self, n, void func(T*)) (C++17)
    foreach_n_range (A, T, IT, first, n, void func(T*)) (C++20)
 
applies a function to the first n elements of a sequence. (NYI, see branch `iter-redesign`)

    count (A* self, T value)
    count_if (A* self, int _match(T*))
    count_range (I* first, I* last, T value) (C++20)
    count_if_range (I* first, I *last, int _match(T*)) (C++20)
 
returns the number of elements satisfying specific criteria

    mismatch (I* first1, I *last1, I* first2)
    mismatch_range (I* first1, I *last1, I* first2, I* last2) (C++20)
 
finds the first position where two ranges differ. _(NYI)_

    find (A* self, T* value)
    find_if (A* self, int _match(T*))
    find_if_not (A* self, int _match(T*)) (C++11)
    find_range (A* self, IT first, IT last, T value) (C++20)
    find_if_range (IT first, IT last, int _match(T*)) (C++20)
    find_if_not_range (IT first, IT last, int _match(T*)) (C++20)
 
finds the first element satisfying specific criteria. Returns IT.

    find_end
    find_end_range (C++20)
 
finds the last sequence of elements in a certain range. _(NYI)_

    find_first_of
    find_first_of_range (C++20)
 
searches for any one of a set of elements. _(NYI)_

    adjacent_find
    adjacent_find_range (C++20)
 
finds the first two adjacent items that are equal (or satisfy a given predicate). _(NYI)_

    search
    search_range (C++20)
 
searches for a range of elements. _(NYI)_

    search_n
 
searches a range for a number of consecutive copies of an element. _(NYI)_

## Modifying sequence operations

    copy
    copy_if (C++11)
    copy_range (C++20)
    copy_if_range (C++20)
 
copies a range of elements to a new location. _(NYI)_

    copy_n (C++11)
    copy_n_range (C++20)

copies a number of elements to a new location. _(NYI)_

    copy_backward
    copy_backward_range (C++20)
 
copies a range of elements in backwards order. _(NYI)_
 
    move (C++11)
    move_range (C++20)
 
moves a range of elements to a new location. _(NYI)_

    move_backward (C++11)
    move_backward_range (C++20)
 
moves a range of elements to a new location in backwards order. _(NYI)_

    fill
    fill_range (C++20)
 
copy-assigns the given value to every element in a range. _(NYI)_
assigns a range of elements a certain value.

    fill_n
    fill_n_range (C++20)
 
copy-assigns the given value to N elements in a range. _(NYI)_
assigns a value to a number of elements

    transform
    transform_range

applies a function to a range of elements, storing results in a destination range. _(NYI)_

    generate
    generate_range (C++20)
 
assigns the results of successive function calls to every element in a range. _(NYI)_
saves the result of a function in a range.

    generate_n
    generate_n_range (C++20)
 
assigns the results of successive function calls to N elements in a range. _(NYI)_
saves the result of N applications of a function

    remove
    remove_if
    remove_range (C++20)
    remove_if_range (C++20)
 
removes elements satisfying specific criteria. (_Partially implemented)_

    remove_copy
    remove_copy_if
    remove_copy_range (C++20)
    remove_copy_if_range (C++20)
 
copies a range of elements omitting those that satisfy specific criteria. _(NYI)_

    replace
    replace_if
    replace_range (C++20)
    replace_if_range (C++20)
 
replaces all values satisfying specific criteria with another value. _(NYI)_

    replace_copy
    replace_copy_if
    replace_copy_range
    replace_copy_if_range
 
copies a range, replacing elements satisfying specific criteria with another value. _(NYI)_

    swap
 
swaps the values of two objects.

    swap_ranges (C++20)
 
swaps two ranges of elements. _(NYI)_

    iter_swap
 
swaps the elements pointed to by two iterators. _(NYI)_

    reverse
    reverse_range (C++20)

reverses the order of elements in a range. _(range NYI)_

    reverse_copy
    reverse_copy_range (C++20)
 
creates a copy of a range that is reversed. _(NYI)_

    rotate
    rotate_range (C++20)
 
rotates the order of elements in a range. _(NYI)_

    rotate_copy
    rotate_copy_range (C++20)

copies and rotate a range of elements. _(NYI)_

    shift_left
    shift_right (C++20)
 
shifts elements in a range. _(NYI)_

    random_shuffle (until C++17)
    shuffle (C++11)
    shuffle_range (C++20)

randomly re-orders elements in a range. _(NYI)_

    sample (C++17)
    sample_range (C++20)
 
selects n random elements from a sequence. _(NYI)_

    unique
    unique_range (C++20)
 
removes consecutive duplicate elements in a range. _(range NYI)_

    unique_copy
    unique_copy_range (C++20)
 
creates a copy of some range of elements that contains no consecutive duplicates. _(NYI)_

## Partitioning operations

    is_partitioned (C++11)
    is_partitioned_range (C++20)
 
determines if the range is partitioned by the given predicate. _(NYI)_

    partition
    partition_range (C++20)
 
divides a range of elements into two groups. _(NYI)_

    partition_copy (C++11)
    partition_copy_range (C++20)
 
copies a range dividing the elements into two groups. _(NYI)_

    stable_partition
    stable_partition_range (C++20)
 
divides elements into two groups while preserving their relative order. _(NYI)_

    partition_point (C++11)
    partition_point_range (C++20)
 
locates the partition point of a partitioned range. _(NYI)_

## Sorting operations

    is_sorted (C++11)
    is_sorted_range (C++20)
  
checks whether a range is sorted into ascending order. _(NYI)_

    is_sorted_until (C++11)
    is_sorted_until_range (C++20)
 
finds the largest sorted subrange. _(NYI)_

    sort
    sort_range (C++20)
 
sorts a range into ascending order.

    partial_sort
    partial_sort_range (C++20)
 
sorts the first N elements of a range. _(NYI)_

    partial_sort_copy
    partial_sort_copy_range (C++20)
 
copies and partially sorts a range of elements. _(NYI)_

    stable_sort
    stable_sort_range (C++20)
 
sorts a range of elements while preserving order between equal elements. _(NYI)_
 
    nth_element
    nth_element_range (C++20)
 
partially sorts the given range making sure that it is partitioned by the given element. _(NYI)_

## Binary search operations (on sorted ranges)

    lower_bound
    lower_bound_range (C++20)
  
returns an iterator to the first element not less than the given value. _(NYI)_

    upper_bound
    upper_bound_range (C++20)

returns an iterator to the first element greater than a certain value. _(NYI)_

    binary_search
    binary_search_range (C++20)
  
determines if an element exists in a certain range. _(NYI)_

    equal_range
    equal_range_range (C++20)
  
returns range of elements matching a specific key. _(NYI)_

## Other operations on sorted ranges

    merge
    merge_range (C++20)
 
merges two sorted ranges. _(range NYI)_

    inplace_merge
    inplace_merge_range (C++20)
 
merges two ordered ranges in-place. _(NYI)_

## Set operations (on sorted ranges)

    includes
    includes_range (C++20)
 
returns true if one sequence is a subsequence of another. _(NYI)_

    difference
    difference_range (C++20)
 
computes the difference between two sets. _(range NYI)_

    intersection
    intersection_range (C++20)
 
computes the intersection of two sets. _(range NYI)_
 
    symmetric_difference
    symmetric_difference_range (C++20)
 
computes the symmetric difference between two sets. _(range NYI)_

    union
    union_range (C++20)
 
computes the union of two sets. _(range NYI)_
 
## Heap operations

    is_heap (C++11)
    is_heap_range (C++20)
 
checks if the given range is a max heap. _(NYI)_

    is_heap_until (C++11)
    is_heap_until_range (C++20)

finds the largest subrange that is a max heap. _(NYI)_

    make_heap
    make_heap_range (C++20)
 
creates a max heap out of a range of elements. _(NYI)_

    push_heap
    push_heap_range (C++20)
 
adds an element to a max heap. _(NYI)_

    pop_heap
    pop_heap_range (C++20)
 
removes the largest element from a max heap. _(NYI)_
 
    sort_heap
    sort_heap_range (C++20)
 
turns a max heap into a range of elements sorted in ascending order. _(NYI)_

# Minimum/maximum operations

    max
    max_range (C++20)
 
returns the greater of the given values. _(NYI)_

    max_element
    max_element_range (C++20)
  
returns the largest element in a range. _(NYI)_

    min
    min_range (C++20)
 
returns the smaller of the given values. _(NYI)_

    min_element
    min_element_range (C++20)
 
returns the smallest element in a range. _(NYI)_

    minmax (C++11)
    minmax_range (C++20)
 
returns the smaller and larger of two elements. _(NYI)_

    minmax_element (C++11)
    minmax_element_range (C++20)
 
returns the smallest and the largest elements in a range. _(NYI)_
 
    clamp (C++17)
    clamp_range (C++20)
 
clamps a value between a pair of boundary values. _(NYI)_

## Comparison operations

    equal
    equal_range (C++20)
 
determines if two sets of elements are the same
 
    lexicographical_compare
    lexicographical_compare_range (C++20)
 
returns true if one range is lexicographically less than another. _(NYI)_
 
    lexicographical_compare_three_way (C++20)
 
compares two ranges using three-way comparison. _(NYI)_

## Permutation operations

    is_permutation (C++11)
    is_permutation_range (C++20)
 
determines if a sequence is a permutation of another sequence. _(NYI)_

    next_permutation
    next_permutation_range (C++20)
 
generates the next greater lexicographic permutation of a range of elements. _(NYI)_

    prev_permutation
    prev_permutation_range (C++20)
 
generates the next smaller lexicographic permutation of a range of elements. _(NYI)_
 
## Numeric operations

See [numeric](numeric.md)

## Operations on uninitialized memory

See [memory](memory.md)
