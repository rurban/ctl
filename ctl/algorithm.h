// Optional algorithms
// See MIT LICENSE
// DO NOT STANDALONE INCLUDE, need container included before.
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

#if 0
#include <stdbool.h>

/* We have two major kinds of iterators:
   - returning B* nodes (list, set, uset), and
   - returning T* valuerefs directly (arrays).
*/

#if !defined IT /* && !defined foreach_range */
# if defined CTL_LIST || defined CTL_SET || defined CTL_USET
#  define CTL_B_ITER
#  define IT B
/* return it.node */
#  define foreach_range(A, it, first, last)      \
    A* other = first->container;                 \
    if (last != JOIN(A, end)(&other)             \
        first->end = last->node;                 \
    foreach(A, other, it)
# else
#  define CTL_T_ITER
#  define IT T
/* return it.ref */
#  ifdef CTL_VEC
#   define foreach_range(A, it, first, last)       \
      A* itercont = first->container;              \
      if (last != JOIN(A, end)(&itercont)          \
          first->end = last->end;                  \
      foreach(A, other, it)
#  else // DEQ
#   define foreach_range(A, it, first, last)
/* FIXME: T -> I, deque needs a container field really
#   define foreach_range(A, it, first, last)       \
      A* itercont = first->container;              \
      if (last != JOIN(A, end)(&itercont)          \
          first->index_last = last->index;         \
      foreach(A, other, it)
*/
#  endif
# endif
#endif

#ifdef foreach_range

// i.e. for LIST, SET, USET with B*
//      and VEC, DEQ with T*
static inline IT*
JOIN(A, find_range)(A* self, I* first, I* last, T value)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->equal || self->compare || !"equal or compare undefined");
#endif
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(self, it.ref, &value))
            return first;
    return last;
}

static inline IT*
JOIN(A, find_if_range)(A* self, IT* first, IT* last, int _match(T*))
{
    foreach_range(A, it, first, last)
        if(_match(it.ref))
            return first;
    return last;
}

static inline IT*
JOIN(A, find_if_not_range)(A* self, IT* first, IT* last, int _match(T*))
{
    foreach_range(A, it, first, last)
        if(!_match(it.ref))
            return first;
    return last;
}

#if !defined(CTL_USET) && !defined(CTL_STR)
static inline bool
JOIN(A, equal_range)(A* self, IT* first, IT* last)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->equal || self->compare || !"equal or compare undefined");
#endif
    foreach_range(A, it, first, last)
        if(!JOIN(A, _equal)(it.ref, first.ref))
            return false;
    return true;
}
#endif // USET+STR

static inline IT*
JOIN(A, find_if)(A* self, int _match(T*))
{
    foreach(A, self, it)
        if(_match(it.ref))
#ifdef CTL_T_ITER
            return it.ref;
#else
            return it;
#endif
    return JOIN(A, end)(self);
}

// C++11
static inline IT*
JOIN(A, find_if_not)(A* self, int _match(T*))
{
    foreach(A, self, it)
        if(!_match(it.ref))
#ifdef CTL_T_ITER
            return it.ref;
#else
            return it;
#endif
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

// C++20
static inline bool
JOIN(A, all_of_range)(A* self, IT* first, IT* last, int _match(T*))
{
    return JOIN(A, find_if_not_range)(self, first, last, _match) == JOIN(A, end)(self);
}
// C++20
static inline bool
JOIN(A, any_of_range)(A* self, IT* first, IT* last, int _match(T*))
{
    return JOIN(A, find_if_range)(self, first, last, _match) != JOIN(A, end)(self);
}
// C++20
static inline bool
JOIN(A, none_of_range)(A* self, IT* first, IT* last, int _match(T*))
{
    return JOIN(A, find_if_range)(self, first, last, _match) == JOIN(A, end)(self);
}

// C++20
static inline size_t
JOIN(A, count_if_range)(A* self, IT* first, IT* last, int _match(T*))
{
    size_t count = 0;
    foreach_range(A, it, first, last)
        if(_match(it.ref))
            count++;
    return count;
}

// C++20
static inline size_t
JOIN(A, count_range)(A* self, IT* first, IT* last, T value)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->equal || self->compare || !"equal or compare undefined");
#endif
    size_t count = 0;
    foreach_range(A, it, first, last)
        if(JOIN(A, _equal)(it.ref, &value))
            count++;
    return count;
}

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
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->equal || self->compare || !"equal or compare undefined");
#endif
    size_t count = 0;
    foreach(A, self, it)
        if(JOIN(A, _equal)(it.ref, &value))
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

#endif

#undef IT
#endif
