/* Abstract IT (T* value, B* node or size_t index)
   foreach, foreach_range.

   We have two kinds of iterators:
   - returning B* nodes (list, set, uset)
   - returning T* valuerefs directly (vector, deque).

   An iterator should be simply incremented:
     IT it; it++ for vectors, it = it->next for lists.

   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
# error "Template type T undefined for <ctl/bits/iterators.h>"
#endif

#if defined CTL_LIST || defined CTL_SET || defined CTL_MAP || \
    defined CTL_USET || defined CTL_UMAP

# define CTL_B_ITER
# undef IT
# define IT B*
/* return B* it node. end is NULL */

/* Fast typed iters */
# define list_foreach(A, IT, self, it)                  \
    if (self->size)                                     \
        for(B* it = JOIN(A, begin)(self);               \
            it;                                         \
            it = it->next)
# define list_foreach_range(A, IT, self, it, first, last)\
    if (self->size && last)                             \
        for(B* it = first;                              \
            it != last;                                 \
            it = it->next)

#else

# define CTL_T_ITER

# undef IT
# define IT T*
/* array of T*. end() = size+1 */

/* Fast typed iters */
# define vec_foreach(T, self, it)                         \
    if (self->size)                                       \
        for(T* it = JOIN(vec, JOIN(T, begin))(self);      \
            it < JOIN(vec, JOIN(T, end))(self);           \
            it++)
# define vec_foreach_range(T, self, it, first, last)      \
    if (self->size && last)                               \
        for(T* it = first;                                \
            it < last;                                    \
            it++)

#endif

// slower generic iters for algorithm
#define foreach(A, IT, self, pos)                                    \
    for(IT pos = JOIN(A, begin)(self);                               \
        ((JOIN(A, it)*)pos)->ref != JOIN(A, end)(self);              \
        pos = JOIN(JOIN(A, it), next)(pos))
#define foreach_range(A, IT, pos, first, last)                       \
    for(IT pos = first;                                              \
        ((JOIN(A, it)*)pos)->ref != last;                            \
        pos = JOIN(JOIN(A, it), next)(pos))
