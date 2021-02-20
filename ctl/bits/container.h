/* Common bits for all containers.
   SPDX-License-Identifier: MIT */

// DO NOT STANDALONE INCLUDE.
#if !defined CTL_LIST && !defined CTL_SET && !defined CTL_USET && !defined CTL_VEC && !defined CTL_ARR &&              \
    !defined CTL_DEQ
#error "No CTL container defined for <ctl/bits/container.h>"
#endif

// FIXME once per A
//#ifndef CAT(HAVE, JOIN(T, it_vtable))
//#define CAT(HAVE, JOIN(T, it_vtable))
//static const struct JOIN(I, vtable_t)
//JOIN(I, vtable_g) =
//  { JOIN(I, next), JOIN(I, ref), JOIN(I, done) };
//#endif

#include <stdbool.h>

#ifndef CTL_ARR
static inline int JOIN(A, empty)(A *self)
{
    return self->size == 0;
}

static inline size_t JOIN(A, size)(A *self)
{
    return self->size;
}

static inline size_t JOIN(A, max_size)()
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

static inline T JOIN(A, implicit_copy)(T *self)
{
    return *self;
}

// not valid for uset, str.
#if !defined(CTL_USET) && !defined(CTL_STR)
static inline int JOIN(A, equal)(A *self, A *other)
{
    if (JOIN(A, size)(self) != JOIN(A, size)(other))
        return 0;
    I i1 = JOIN(A, begin)(self);
    I i2 = JOIN(A, begin)(other);
    while (!JOIN(I, done)(&i1) && !JOIN(I, done)(&i2))
    {
        T *r1 = JOIN(I, ref)(&i1);
        T *r2 = JOIN(I, ref)(&i2);
        if (self->equal)
        {
            if (!self->equal(r1, r2))
                return 0;
        }
        else
        {
            // this works with 2-way and 3-way compare
            if (self->compare(r1, r2) || self->compare(r2, r1))
                return 0;
        }
        JOIN(I, next)(&i1);
        JOIN(I, next)(&i2);
    }
    return 1;
}
#endif

// _set_default_methods
#include <ctl/bits/integral.h>

#if !defined(CTL_USET)
static inline int JOIN(A, _equal)(A *self, T *a, T *b)
{
    CTL_ASSERT_EQUAL
    if (self->equal)
        return self->equal(a, b);
    else
        return !self->compare(a, b) && !self->compare(b, a);
}
#endif

// If parent, include only for the child later.
// parents are vec: str, pqu. deq: queue, stack. set: map, uset: umap
// ignore str: u8str, u8id for now.
#undef _IS_PARENT_CHILD_FOLLOWS
#if defined CTL_VEC && (defined CTL_PQU || defined CTL_STR || defined CTL_U8STR)
//#pragma message "vec child"
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_DEQ && (defined CTL_QUEUE || defined CTL_STACK)
//#pragma message "deq child"
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_SET && defined CTL_MAP
//#pragma message "set child"
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_USET && defined CTL_UMAP
//#pragma message "uset child"
#define _IS_PARENT_CHILD_FOLLOWS
#endif

#ifndef _IS_PARENT_CHILD_FOLLOWS
#include <ctl/algorithm.h>
//#else
//# pragma message "_IS_PARENT_CHILD_FOLLOWS defined"
#endif
#undef _IS_PARENT_CHILD_FOLLOWS
