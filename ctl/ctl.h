// See MIT LICENSE
// SPDX-License-Identifier: MIT
#ifndef __CTL_H__
#define __CTL_H__

#define CTL_VERSION 202102

#include <stdint.h>
#include <stdlib.h>

#define CAT(a, b) a##b
#define PASTE(a, b) CAT(a, b)
#define JOIN(prefix, name) PASTE(prefix, PASTE(_, name))
#define _JOIN(prefix, name) PASTE(_, PASTE(prefix, PASTE(_, name)))

#define SWAP(TYPE, a, b)                                                                                               \
    {                                                                                                                  \
        TYPE temp = *(a);                                                                                              \
        *(a) = *(b);                                                                                                   \
        *(b) = temp;                                                                                                   \
    }

#define len(a) (sizeof(a) / sizeof(*(a)))

#define FREE_VALUE(self, value)                                                                                        \
    if (self->free)                                                                                                    \
        self->free(&(value))

#ifdef DEBUG
#define LOG(...) fprintf(stderr, __VA_ARGS__)
#else
#define LOG(...)
#endif

#if defined(_ASSERT_H) && !defined(NDEBUG)
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

#ifdef CTL_USET
#define CTL_ASSERT_EQUAL ASSERT(self->equal || !"equal undefined");
#else
#define CTL_ASSERT_EQUAL ASSERT(self->equal || self->compare || !"equal or compare undefined");
#endif
#define CTL_ASSERT_COMPARE ASSERT(self->compare || !"compare undefined");

#if __GNUC__ >= 3
#define LIKELY(x) __builtin_expect((long)(x) != 0, 1)
#define UNLIKELY(x) __builtin_expect((long)(x) != 0, 0)
#else
#define LIKELY(x) x
#define UNLIKELY(x) x
#endif
#endif

#ifndef MAX
#define MAX(a, b) a >= b ? a : b
#endif
