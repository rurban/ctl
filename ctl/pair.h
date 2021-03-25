/* pair for map/umap
   Should not be included directly, only required by map or unordered_map
   (and friends, like swisstable, hashmap).
   pair understands POD, T for the key, and POD_VALUE, T_VALUE for the value.

   SPDX-License-Identifier: MIT */
#ifndef __CTL_PAIR__H__
#define __CTL_PAIR__H__

#ifndef T
# error "Template type T undefined for <ctl/pair.h>"
#endif
#ifndef A
# error "Template type A undefined for <ctl/pair.h>"
#endif
#ifndef T_VALUE
typedef void* voidp;
# define T_VALUE voidp
static inline void voidp_free(T_VALUE* value) { free (*value); }
static inline T_VALUE voidp_copy(T_VALUE* value) { return *value; }
#endif

//#define CTL_PAIR
#define PAIR JOIN(pair, JOIN(T, T_VALUE))

typedef struct PAIR
{
    T first;
    T_VALUE second;
    void (*free)(T*);
    T (*copy)(T*);
    void (*free_value)(T_VALUE*);
    T_VALUE (*copy_value)(T_VALUE*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*);
} PAIR;

#ifdef A
#include <ctl/bits/integral.h>
#endif

static inline T_VALUE JOIN(PAIR, implicit_value_copy)(T_VALUE *self)
{
    return *self;
}

static inline PAIR
JOIN(PAIR, make_pair)(T key, T_VALUE value)
{
    static PAIR zero;
    PAIR self = zero;
    self.first = key;
    self.second = value;

#ifdef POD
# ifdef A
    self.copy = JOIN(A, implicit_copy);
    _JOIN(A, _set_default_methods)(&self);
# endif
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif

#ifdef POD_VALUE
    self.free_value = free;
    self.copy_value = JOIN(PAIR, implicit_value_copy);
#else
    self.free_value = JOIN(T_VALUE, free);
    self.copy_value = JOIN(T_VALUE, copy);
#endif

    return self;
}

//#undef A
#endif
