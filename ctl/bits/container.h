/* Common bits for all containers.
   SPDX-License-Identifier: MIT */

// DO NOT STANDALONE INCLUDE.
#if !defined CTL_LIST && !defined CTL_SET && !defined CTL_USET && \
    !defined CTL_VEC && !defined CTL_DEQ
#error "No CTL container defined for <ctl/bits/container.h>"
#endif

#include <stdbool.h>

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

static inline I
JOIN(I, each)(A* a)
{
    return JOIN(A, empty)(a)
         ? JOIN(I, range)(a, NULL, NULL)
         : JOIN(I, range)(a, JOIN(A, begin)(a), JOIN(A, end)(a));
}

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
    if(self->size != other->size)
        return 0;
    I a = JOIN(I, each)(self);
    I b = JOIN(I, each)(other);
    while(!a.done && !b.done)
    {
        if(self->equal)
        {
            if(!self->equal(a.ref, b.ref))
                return 0;
        }
        else
        {
            if(self->compare(a.ref, b.ref) ||
               self->compare(b.ref, a.ref))
                return 0;
        }
        a.step(&a);
        b.step(&b);
    }
    return 1;
}
#endif

// _set_default_methods
#include <ctl/bits/integral.h>

#if !defined(CTL_STR) && !defined(CTL_USET)
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

// if parent, include only for the child later.
// parents are vec: str, pqu. deq: queue, stack. set: map, uset: umap
// ignore str: u8str, u8id for now.
#undef _IS_PARENT_CHILD_FOLLOWS
#if defined CTL_VEC && (defined CTL_STACK || defined CTL_STR  || defined CTL_U8STR)
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
#include <ctl/algorithm.h>
#endif
#undef _IS_PARENT_CHILD_FOLLOWS
