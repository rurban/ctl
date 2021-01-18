// See MIT LICENSE
// SPDX-License-Identifier: MIT
#ifndef __CTL_H__
#define __CTL_H__

#define CTL_VERSION 202101L

#include <stdlib.h>
#include <stdint.h>

#define CAT(a, b) a##b
#define PASTE(a, b) CAT(a, b)
#define JOIN(prefix, name) PASTE(prefix, PASTE(_, name))
#define _JOIN(prefix, name) PASTE(_, PASTE(prefix, PASTE(_, name)))

#define SWAP(TYPE, a, b) { TYPE temp = *(a); *(a) = *(b); *(b) = temp; }

#define len(a) (sizeof(a) / sizeof(*(a)))

#ifndef POD
#define FREE_VALUE(self, value) \
    if(self->free)              \
        self->free(&(value))
#else
#define FREE_VALUE(self, value)
#endif

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

#if __GNUC__ >= 3
#define LIKELY(x) __builtin_expect((long)(x) != 0, 1)
#define UNLIKELY(x) __builtin_expect((long)(x) != 0, 0)
#else
#define LIKELY(x) x
#define UNLIKELY(x) x
#endif
#endif

/* Three types of iterators */
#define CTL_DEQ_TAG 0xdeadbee1
#define CTL_LIST_TAG 0xdeadbee2
#define CTL_VEC_TAG 0xdeadbee3
