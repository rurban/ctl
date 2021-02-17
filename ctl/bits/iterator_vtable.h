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
static void JOIN(I, next)(struct I *iter);
static inline T *JOIN(I, ref)(struct I *iter);
static inline int JOIN(I, done)(struct I *iter);

// Iterator vtable
// FIXME once per T
//#undef have_ctl_vtable
//#define have_ctl_vtable JOIN(HAVE, JOIN(T, it_vtable))
//#ifndef JOIN(HAVE, JOIN(T, it_vtable))
struct JOIN(I, vtable_t) {
    void (*next)(struct I*);
    T*   (*ref) (struct I*);
    int  (*done)(struct I*);
};
//#endif

