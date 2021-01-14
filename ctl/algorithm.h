// Optional generic algorithms
// DO NOT STANDALONE INCLUDE, need container included before.
// SPDX-License-Identifier: MIT
//
// Might only be included once. By the child. not the parent.
#ifndef __CTL_ALGORITHM_H__
#define __CTL_ALGORITHM_H__
#define CTL_ALGORITHM

#if !defined CTL_LIST && \
    !defined CTL_SET && \
    !defined CTL_USET && \
    !defined CTL_VEC && \
    !defined CTL_DEQ && \
    /* plus all children also. we dont include it for parents */ \
    !defined CTL_MAP && \
    !defined CTL_UMAP
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

#include <stdbool.h>

// i.e. for LIST, SET, USET with B*
//      and VEC, DEQ with T*
// leaks T value, as with find
static inline IT*
JOIN(A, find_range)(I* first, I* last, T value)
{
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(first->container, it.ref, &value))
            return iter_IT(it);
    return iter_IT_endp(last);
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

// C++20
static inline bool
JOIN(A, all_of_range)(I* first, I* last, int _match(T*))
{
    IT* n = JOIN(A, find_if_not_range)(first, last, _match);
    return n == iter_IT_endp(last);
}
// C++20
static inline bool
JOIN(A, none_of_range)(I* first, I* last, int _match(T*))
{
    IT* n = JOIN(A, find_if_range)(first, last, _match);
    return n == iter_IT_endp(last);
}
// C++20
static inline bool
JOIN(A, any_of_range)(I* first, I* last, int _match(T*))
{
    return !JOIN(A, none_of_range)(first, last, _match);
}

#if !defined(CTL_SET) && !defined(CTL_USET) && !defined(CTL_STR)
// C++20
// uset has cached_hash optims
static inline size_t
JOIN(A, count_range)(I* first, I* last, T value)
{
    if (first->done || !first->container)
        return 0;
    A* self = first->container;
    size_t count = 0;
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(self, it.ref, &value))
            count++;
    if (self->free)
        self->free(&value);
    return count;
}
#endif //SET/USET/STR

#if !defined(CTL_SET) && !defined(CTL_STR)
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

static inline size_t
JOIN(A, count_if)(A* self, int _match(T*))
{
    size_t count = 0;
    foreach(A, self, it)
        if(_match(it.ref))
            count++;
    return count;
}

#ifndef CTL_USET
static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, &value))
            count++;
    if(self->free)
        self->free(&value);
    return count;
}
#endif // USET
#endif // SET/STR

#ifdef DEBUG
#if !defined(CTL_USET) && !defined(CTL_STR)
static inline bool
JOIN(A, equal_range)(I* first, I* last, T value)
{
    if (first->done || !first->container)
        return false;
    A* self = first->container;
    bool result = true;
    foreach_range(A, it, first, last)
        if(!JOIN(A, _equal)(self, it.ref, &value))
        {
            result = false;
            break;
        }
    if(self->free)
        self->free(&value);
    return result;
}
#endif // USET+STR
#endif // DEBUG

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
