/* Abstract iterators: T* value, B* node or size_t index
   foreach, foreach_range.

   We have two kinds of iterators:
   - returning B* nodes (list, set, uset)
   - returning T* valuerefs directly (vector, deque).
     deque has it's own special variant incuding the index.

   An iterator should be simply incremented:
     it++ for vectors, it = it->next for lists.

   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
#error "Template type T undefined for <ctl/bits/iterators.h>"
#endif

#if defined CTL_LIST || defined CTL_SET || defined CTL_MAP || defined CTL_USET || defined CTL_UMAP

#define CTL_B_ITER
//# undef IT
//# define IT B*
/* return B* it node. end is NULL */

#define list_foreach(A, self, pos)                                                                                     \
    if ((self)->size)                                                                                                  \
        for (JOIN(A, it) pos = JOIN(A, begin)(self); pos.node != NULL; pos.node = JOIN(JOIN(A, node), next)(pos.node))
#define list_foreach_range(A, pos, first, last)                                                                        \
    if (first && first->node)                                                                                          \
        for (JOIN(A, it) pos = *(first); pos.node != (last)->node; pos.node = JOIN(JOIN(A, node), next)(pos.node))

#define list_foreach_ref(A, self, pos)                                                                                 \
    if ((self)->size)                                                                                                  \
        for (JOIN(A, it) pos = JOIN(A, begin)(self); pos.node != NULL; JOIN(JOIN(A, it), next)(&pos))
#define list_foreach_range_ref(A, pos, first, last)                                                                    \
    if (first && first->node)                                                                                          \
        for (JOIN(A, it) pos = *(first); pos.node != (last)->node; JOIN(JOIN(A, it), next)(&pos))

#else

#define CTL_T_ITER

//# undef IT
//# define IT T*
/* array of T*. end() = size+1 */

#ifndef CTL_DEQ

/* Make simple vector iters fast */
#define vec_foreach(T, self, ref)                                                                                      \
    if ((self)->size)                                                                                                  \
        for (T *ref = &(self)->vector[0]; ref < &(self)->vector[(self)->size]; ref++)
#define vec_foreach_range(T, self, it, first, last)                                                                    \
    if ((self)->size && last.ref)                                                                                      \
        for (T *it = first.ref; it < last.ref; it++)

#endif // not deq

#endif // not list

// generic iters for algorithm
#define foreach(A, self, pos)                                                                                          \
    for (JOIN(A, it) pos = JOIN(A, begin)(self); !JOIN(JOIN(A, it), done)(&pos); JOIN(JOIN(A, it), next)(&pos))
#define foreach_range(A, pos, first, last)                                                                             \
    JOIN(A, it) pos = *first;                                                                                          \
    JOIN(JOIN(A, it), range)(&pos, last);                                                                              \
    for (; !JOIN(JOIN(A, it), done)(&pos); JOIN(JOIN(A, it), next)(&pos))
#define foreach_range_(A, pos, first)                                                                                  \
    JOIN(A, it) pos = *first;                                                                                          \
    for (; !JOIN(JOIN(A, it), done)(&pos); JOIN(JOIN(A, it), next)(&pos))

#define foreach_n(A, self, pos, n)                                                                                     \
    JOIN(A, it) pos = JOIN(A, begin)(self);                                                                            \
    {                                                                                                                  \
        JOIN(A, it) JOIN(pos, __LINE__) = JOIN(A, begin)(self);                                                        \
        JOIN(JOIN(A, it), advance)(&JOIN(pos, __LINE__), n);                                                           \
        JOIN(JOIN(A, it), range)(&pos, &JOIN(pos, __LINE__));                                                          \
    }                                                                                                                  \
    for (; !JOIN(JOIN(A, it), done)(&pos); JOIN(JOIN(A, it), next)(&pos))
#define foreach_n_range(A, first, pos, n)                                                                              \
    JOIN(A, it) pos = *first;                                                                                          \
    {                                                                                                                  \
        JOIN(A, it) JOIN(pos, __LINE__) = *first;                                                                      \
        JOIN(JOIN(A, it), advance)(&JOIN(pos, __LINE__), n);                                                           \
        JOIN(JOIN(A, it), range)(&pos, &JOIN(pos, __LINE__));                                                          \
    }                                                                                                                  \
    for (; !JOIN(JOIN(A, it), done)(&pos); JOIN(JOIN(A, it), next)(&pos))
