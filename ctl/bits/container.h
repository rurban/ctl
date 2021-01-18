/* Common bits for all containers.
   SPDX-License-Identifier: MIT */

// DO NOT STANDALONE INCLUDE.
#if !defined CTL_LIST && \
    !defined CTL_SET && \
    !defined CTL_USET && \
    !defined CTL_VEC && \
    !defined CTL_ARR && \
    !defined CTL_DEQ
# error "No CTL container defined for <ctl/bits/container.h>"
#endif

#include <stdbool.h>

#ifndef CTL_ARR
static inline int
JOIN(A, empty)(A* self)
{
    return self->size == 0;
}

static inline size_t
JOIN(A, size)(A* self)
{
    return self->size;
}

static inline size_t
JOIN(A, max_size)()
{
    return 4294967296 / sizeof(T); // 32bit at most. avoid DDOS
}
#endif

/*
static inline I
JOIN(I, each)(A* a)
{
    return JOIN(A, empty)(a)
         ? JOIN(I, range)(a, 0, 0)
         : JOIN(I, range)(a, JOIN(A, begin)(a), JOIN(A, end)(a));
}
*/

static inline T
JOIN(A, implicit_copy)(T* self)
{
    return *self;
}

// not valid for uset, str
#if !defined(CTL_USET) && !defined(CTL_STR)
static inline int
JOIN(A, equal)(A* self, A* other)
{
    if(JOIN(A, size)(self) != JOIN(A, size)(other))
        return 0;
    IT i1 = JOIN(A, begin)(self);
    IT i2 = JOIN(A, begin)(other);
    IT e1 = JOIN(A, end)(self);
    IT e2 = JOIN(A, end)(other);
    while(i1 != e1 && i2 != e2)
    {
        if(self->equal)
        {
            if(!self->equal(i1, i2))
                return 0;
        }
        else
        {
            if(self->compare(i1, i2) ||
               self->compare(i2, i1))
                return 0;
        }
        i1 = JOIN(I, next)(i1);
        i2 = JOIN(I, next)(i2);
    }
    return 1;
}
#endif

// _set_default_methods
#include <ctl/bits/integral.h>

#if !defined(CTL_USET)
static inline int
JOIN(A, _equal)(A* self, T* a, T* b)
{
    CTL_ASSERT_EQUAL
    if(self->equal)
        return self->equal(a, b);
    else
        return !self->compare(a, b) &&
               !self->compare(b, a);
}
#endif

// If parent, include only for the child later.
// parents are vec: str, pqu. deq: queue, stack. set: map, uset: umap
// ignore str: u8str, u8id for now.
#undef _IS_PARENT_CHILD_FOLLOWS
#if defined CTL_VEC && (defined CTL_PQU || defined CTL_STR  || defined CTL_U8STR)
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_DEQ && (defined CTL_QUEUE || defined CTL_STACK)
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_SET && defined CTL_MAP
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_USET && defined CTL_UMAP
#define _IS_PARENT_CHILD_FOLLOWS
#endif

#ifndef _IS_PARENT_CHILD_FOLLOWS
# include <ctl/algorithm.h>
#endif
#undef _IS_PARENT_CHILD_FOLLOWS
