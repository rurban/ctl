// Optional generic algorithms
// DO NOT STANDALONE INCLUDE, need container included before.
// SPDX-License-Identifier: MIT
//
// Might only be included once. By the child. not the parent.
#ifndef __CTL_ALGORITHM_H__
# define __CTL_ALGORITHM_H__
#define CTL_ALGORITHM

#if !defined CTL_LIST && \
    !defined CTL_SET && \
    !defined CTL_USET && \
    !defined CTL_VEC && \
    !defined CTL_ARR && \
    !defined CTL_DEQ && \
    /* plus all children also. we don't include it for parents */ \
    !defined CTL_STACK && \
    !defined CTL_QUEUE && \
    !defined CTL_PQU && \
    !defined CTL_MAP && \
    !defined CTL_UMAP
# error "No CTL container defined for <ctl/algorithm.h>"
#endif

#ifndef IT
# error "Iterator type IT undefined for <ctl/algorithm.h>"
#endif

// Generic algorithms with ranges

static inline I
JOIN(A, find_if)(A* self, int _match(T*))
{
    foreach(A, self, i)
        if(_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline I
JOIN(A, find_if_not)(A* self, int _match(T*))
{
    foreach(A, self, i)
        if(!_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline bool
JOIN(A, all_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if_not)(self, _match);
    return JOIN(I, done)(&pos);
}

// C++11
static inline bool
JOIN(A, any_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if)(self, _match);
    return !JOIN(I, done)(&pos);
}

static inline bool
JOIN(A, none_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if)(self, _match);
    return JOIN(I, done)(&pos);
}

#ifdef DEBUG
// TODO not for value but matching range
static inline I
JOIN(A, find_end)(A* self, T value)
{
    I* ret = NULL;
    foreach(A, self, i)
        if(JOIN(A, _equal)(self, i.ref, &value))
            ret = &i;
    return ret ? *ret : JOIN(A, end)(self);
}

static inline I
JOIN(A, find_end_if)(A* self, int _match(T*))
{
    I* ret = NULL;
    foreach(A, self, i)
        if(_match(i.ref))
            ret = &i;
    return ret ? *ret : JOIN(A, end)(self);
}
#endif

#include <stdbool.h>

static inline I
JOIN(A, find_range)(I* first, I* last, T value)
{
    A* self = first->container;
    foreach_range(A, i, first, last)
        if(JOIN(A, _equal)(self, i.ref, &value))
            return i;
    return *last;
}

#if 0
// args
static inline I
JOIN(A, find_end_range)(I* first, I* last, T value)
{
    I* ret = NULL;
    A* self = first->container;
    foreach_range(A, i, first, last)
        if(JOIN(A, _equal)(self, i.ref, &value))
            ret = &i;
    return ret ? *ret : *last;
}

static inline I
JOIN(A, find_end_if_range)(I* first, I* last, int _match(T*))
{
    I* ret = NULL;
    foreach_range(A, i, first, last)
        if(_match(i.ref))
            ret = &i;
    return ret ? *ret : *last;
}
#endif

static inline I
JOIN(A, find_if_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, i, first, last)
        if(_match(i.ref))
            return i;
    return *last;
}

static inline I
JOIN(A, find_if_not_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, i, first, last)
        if(!_match(i.ref))
            return i;
    return *last;
}

// C++20
static inline bool
JOIN(A, all_of_range)(I* first, I* last, int _match(T*))
{
    I pos = JOIN(A, find_if_not_range)(first, last, _match);
    return JOIN(I, isend)(&pos, last);
}
// C++20
static inline bool
JOIN(A, none_of_range)(I* first, I* last, int _match(T*))
{
    I pos = JOIN(A, find_if_range)(first, last, _match);
    return JOIN(I, isend)(&pos, last);
}
// C++20
static inline bool
JOIN(A, any_of_range)(I* first, I* last, int _match(T*))
{
    return !JOIN(A, none_of_range)(first, last, _match);
}

#if !defined(CTL_USET) && !defined(CTL_STR)
// C++20
// uset has cached_hash optims
static inline size_t
JOIN(A, count_range)(I* first, I* last, T value)
{
    A* self = first->container;
    size_t count = 0;
    foreach_range(A, i, first, last)
        if(JOIN(A, _equal)(self, i.ref, &value))
            count++;
    if (self->free)
        self->free(&value);
    return count;
}
#endif //USET/STR

#if !defined(CTL_STR)
// C++20
static inline size_t
JOIN(A, count_if_range)(I* first, I* last, int _match(T*))
{
    size_t count = 0;
    foreach_range(A, i, first, last)
        if(_match(i.ref))
            count++;
    return count;
}

static inline size_t
JOIN(A, count_if)(A* self, int _match(T*))
{
    size_t count = 0;
    foreach(A, self, i)
        if(_match(i.ref))
            count++;
    return count;
}

#if !defined(CTL_SET) && !defined(CTL_USET)
static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, i)
        if(JOIN(A, _equal)(self, i.ref, &value))
            count++;
    if(self->free)
        self->free(&value);
    return count;
}
#endif // SET/USET
#endif // STR

#ifdef DEBUG
#if !defined(CTL_USET) && !defined(CTL_STR)
// API? 3rd arg should be an iter, not a value
static inline bool
JOIN(A, equal_range)(A* self, I* first, I* last, T value)
{
    bool result = true;
    foreach_range(A, i, first, last)
        if(!JOIN(A, _equal)(self, i.ref, &value))
        {
            result = false;
            break;
        }
    if(self && self->free)
        self->free(&value);
    return result;
}
#endif // USET+STR
#endif // DEBUG

// TODO:
// mismatch
// mismatch_range C++20
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

#endif // only once
