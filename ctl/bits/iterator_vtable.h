/* 
   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
#error "Template type T undefined for <ctl/bits/iterator_vtable.h>"
#endif

/* 2 basic types of iterators. All must have the same size, so that we can
 * struct copy them easily. */
#define CTL_T_ITER_FIELDS                                                                                              \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref; /* will be removed later */                                                                                \
    A *container;                                                                                                      \
    T *end;                                                                                                            \
    T *_padding

#define CTL_B_ITER_FIELDS                                                                                              \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref;      /* will be removed later */                                                                           \
    A *container;                                                                                                      \
    B *end;                                                                                                            \
    B *node

#define CTL_USET_ITER_FIELDS                                                                                           \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref; /* will be removed later */                                                                                \
    A *container;                                                                                                      \
    B **buckets; /* the chain. no end range needed for uset */                                                         \
    B *node

#define CTL_DEQ_ITER_FIELDS                                                                                            \
    struct JOIN(I, vtable_t) vtable;                                                                                   \
    T *ref; /* will be removed later */                                                                                \
    A *container;                                                                                                      \
    uintptr_t end;                                                                                                     \
    uintptr_t index

struct I;

// Iterator vtable
typedef struct JOIN(I, vtable_t)
{
    void (*next)(struct I *);
    T *(*ref)(struct I *);
    int (*done)(struct I *);
} JOIN(I, vtable_t);
