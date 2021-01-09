/* pair for map/umap
   Should not be included directly, only required by map.h or unordered_map.h.
   See MIT LICENSE. */
#ifndef __CTL_PAIR__H__
#define __CTL_PAIR__H__

#ifndef T
# error "Template type T undefined for <ctl/pair.h>"
#endif
#ifndef T_VALUE
# define T_VALUE void*
#endif

#define CTL_PAIR
#define PAIR JOIN(pair, T)

typedef struct PAIR
{
    T first;
    T_VALUE second;
    void (*free)(T*);
    T (*copy)(T*);
    void (*free_value)(T_VALUE*);
    T (*copy_value)(T_VALUE*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*);
} PAIR;

#include <ctl/bits/integral.h>

static inline T_VALUE JOIN(A, implicit_value_copy)(T_VALUE *self)
{
    return *self;
}

static inline A
JOIN(A, init)(T key, T_VALUE value)
{
    static A zero;
    A self = zero;
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
    _JOIN(A, _set_default_methods)(&self);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    self.free_value = free;
    self.copy_value = JOIN(A, implicit_value_copy);
    return self;
}

#undef C
#endif
