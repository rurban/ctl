// Optional generic algorithms
// DO NOT STANDALONE INCLUDE, need container included before.
// SPDX-License-Identifier: MIT
//
// Might only be included once. By the child. not the parent.
#ifndef __CTL_ALGORITHM_H__
#define __CTL_ALGORITHM_H__
#define CTL_ALGORITHM

#if !defined CTL_LIST && !defined CTL_SET && !defined CTL_USET && \
    !defined CTL_VEC && !defined CTL_DEQ && \
    /* plus all children also. we dont include it for parents */ \
    !defined CTL_STACK && !defined CTL_QUEUE  && !defined CTL_PQU && \
    !defined CTL_MAP && !defined CTL_UMAP
#error "No CTL container defined for <ctl/algorithm.h>"
#endif

// Generic algorithms with ranges

#include <ctl/bits/iterators.h>

static inline IT*
JOIN(A, find_if)(A* self, int _match(T*))
{
    foreach(A, self, it)
        if(_match(it.ref))
            return iter_IT(it);
    return JOIN(A, end)(self);
}

// C++11
static inline IT*
JOIN(A, find_if_not)(A* self, int _match(T*))
{
    foreach(A, self, it)
        if(!_match(it.ref))
            return iter_IT(it);
    return JOIN(A, end)(self);
}

// C++11
static inline bool
JOIN(A, all_of)(A* self, int _match(T*))
{
    return JOIN(A, find_if_not)(self, _match) == JOIN(A, end)(self);
}

// C++11
static inline bool
JOIN(A, any_of)(A* self, int _match(T*))
{
    return JOIN(A, find_if)(self, _match) != JOIN(A, end)(self);
}

static inline bool
JOIN(A, none_of)(A* self, int _match(T*))
{
    return JOIN(A, find_if)(self, _match) == JOIN(A, end)(self);
}

#ifdef foreach_range

#include <stdbool.h>

// i.e. for LIST, SET, USET with B*
//      and VEC, DEQ with T*
static inline I*
JOIN(A, find_range)(A* self, I* first, I* last, T value)
{
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(self, it.ref, &value))
            return first;
    return last;
}

static inline IT*
JOIN(A, find_if_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, it, first, last)
        if(_match(it.ref))
            return iter_IT(it);
    return iter_IT_endp(last);
}

static inline IT*
JOIN(A, find_if_not_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, it, first, last)
        if(!_match(it.ref))
            return iter_IT(it);
    return iter_IT_endp(last);
}

#ifdef DEBUG

#if !defined(CTL_USET) && !defined(CTL_STR)
static inline bool
JOIN(A, equal_range)(I* first, I* last, T value)
{
    foreach_range(A, it, first, last)
        if(!JOIN(A, _equal)(first->container, it.ref, &value))
            return false;
    return true;
}
#endif // USET+STR

// C++20
static inline bool
JOIN(A, all_of_range)(I* first, I* last, int _match(T*))
{
    A* self = first->container;
    IT* it = JOIN(A, find_if_not_range)(first, last, _match);
    return it == JOIN(A, end)(self);
}
// C++20
static inline bool
JOIN(A, any_of_range)(I* first, I* last, int _match(T*))
{
    A* self = first->container;
    IT* it = JOIN(A, find_if_range)(first, last, _match);
    return it != JOIN(A, end)(self);
}
// C++20
static inline bool
JOIN(A, none_of_range)(I* first, I* last, int _match(T*))
{
    A* self = first->container;
    IT* it = JOIN(A, find_if_range)(first, last, _match);
    return it == JOIN(A, end)(self);
}

#if !defined(CTL_SET) && !defined(CTL_USET) && !defined(CTL_STR)

// C++20
static inline size_t
JOIN(A, count_if_range)(I* first, I* last, int _match(T*))
{
    size_t count = 0;
    foreach_range(A, it, first, last)
        if(_match(it.ref))
            count++;
    return count;
}

// C++20
static inline size_t
JOIN(A, count_range)(I* first, I* last, T value)
{
    size_t count = 0;
    A* self = first->container;
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(self, it.ref, &value))
            count++;
    return count;
}
#endif // SET/USET/STR

#endif // DEBUG

#endif // foreach_range IT

#if !defined(CTL_SET) && !defined(CTL_USET) && !defined(CTL_STR)

static inline size_t
JOIN(A, count_if)(A* self, int _match(T*))
{
    size_t count = 0;
    foreach(A, self, it)
        if(_match(it.ref))
            count++;
    return count;
}

static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, &value))
            count++;
    return count;
}

#endif // SET/USET/STR

// TODO:
// foreach_n C++17
// foreach_n_range C++20
// mismatch
// mismatch_range C++20
// find_end
// find_end_range C++20
// find_first_of
// find_first_of_range C++20
// adjacent_find
// adjacent_find_range C++20
// search
// search_range C++20
// search_n
// search_n_range C++20
// copy_range C++20
// copy_if C++11
// copy_if_range C++20
// copy_n C++11
// copy_n_range C++20
// copy_backward
// copy_backward_range C++20
// move C++11
// move_range
// move_backward C++11
// move_backward_range C++20
// fill
// fill_range C++20
// fill_n
// fill_n_range C++20
// transform
// transform_range C++20
// generate
// generate_range C++20

#undef IT
#endif
