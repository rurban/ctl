/* 
   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
#error "Template type T undefined for <ctl/bits/iterator_vtable.h>"
#endif

/* Three types of iterators. deque with index, see there */
#define CTL_T_ITER_FIELDS                                                                                              \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref; /* will be removed later */                                                                                \
    T *end;                                                                                                            \
    A *container

#define CTL_B_ITER_FIELDS                                                                                              \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref; /* will be removed later */                                                                                \
    B *end;                                                                                                            \
    A *container;                                                                                                      \
    B *node

struct I;
//static inline void JOIN(I, next)(struct I *iter);
//static inline T *JOIN(I, ref)(struct I *iter);
//static inline int JOIN(I, done)(struct I *iter);

// Iterator vtable
typedef struct JOIN(I, vtable_t)
{
    void (*next)(struct I *);
    T *(*ref)(struct I *);
    int (*done)(struct I *);
    T (*copy)(T *);
} JOIN(I, vtable_t);
