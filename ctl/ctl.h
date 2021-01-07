// See MIT LICENSE
// SPDX-License-Identifier: MIT
#ifndef __CTL_H__
#define __CTL_H__

#define CTL_VERSION 202101

#include <stdlib.h>
#include <stdint.h>

#define CAT(a, b) a##b
#define PASTE(a, b) CAT(a, b)
#define JOIN(prefix, name) PASTE(prefix, PASTE(_, name))
#define _JOIN(prefix, name) PASTE(_, PASTE(prefix, PASTE(_, name)))

/* iterator with extra B nodes */
#define CTL_B_ITER_FIELDS \
    B* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    B* end;                   \
    int done;                 \
    B* node;                  \
    A* container

/* iterator with simple arrays of T, no intermediate nodes of B */
#define CTL_T_ITER_FIELDS     \
    T* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    T* end;                   \
    int done;                 \
    A* container

#define SWAP(TYPE, a, b) { TYPE temp = *(a); *(a) = *(b); *(b) = temp; }

#define foreach(a, b, c) for(JOIN(a, it) c = JOIN(JOIN(a, it), each) (b); !c.done; c.step(&c))

#define len(a) (sizeof(a) / sizeof(*(a)))

#ifdef DEBUG
#define LOG(...) fprintf(stderr, __VA_ARGS__)
#else
#define LOG(...)
#endif

#if defined(_ASSERT_H) && !defined(NDEBUG)
#ifdef CTL_USET
# define CTL_ASSERT_EQUAL \
    assert(self->equal || !"equal undefined");
#else
# define CTL_ASSERT_EQUAL \
    assert(self->equal || self->compare || !"equal or compare undefined");
#endif
#define CTL_ASSERT_COMPARE \
    assert(self->compare || !"compare undefined");
#else
#define CTL_ASSERT_EQUAL
#define CTL_ASSERT_COMPARE
#endif

#endif
