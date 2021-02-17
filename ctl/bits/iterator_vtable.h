/* 
   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
#error "Template type T undefined for <ctl/bits/iterator_vtable.h>"
#endif

/* Three types of iterators. deque with index, see there */
#define CTL_T_ITER_FIELDS                                                                                              \
    T *ref; /* will be removed later */                                                                                \
    T *end;                                                                                                            \
    A *container;                                                                                                      \
    struct JOIN(I, vtable_t) vtable

#define CTL_B_ITER_FIELDS                                                                                              \
    B *node;                                                                                                           \
    T *ref; /* will be removed later */                                                                                \
    B *end;                                                                                                            \
    A *container;                                                                                                      \
    struct JOIN(I, vtable_t) vtable

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
} JOIN(I, vtable_t);
