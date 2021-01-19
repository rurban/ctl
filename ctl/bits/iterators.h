/* Abstract IT (T* value, B* node or size_t index)
   foreach, foreach_range.

   We have two kinds of iterators:
   - returning B* nodes (list, set, uset)
   - returning T* valuerefs directly (vector, deque).
     deq has it's own special variant incuding the index.

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

#if defined CTL_DEQ

/* Fast typed iters */
# define deq_foreach(A, T, self, pos)                 \
    if ((self)->size)                                 \
        for(T* pos = JOIN(A, begin)(self);            \
            pos != JOIN(A, end)(self);                \
            pos = JOIN(I, next)(pos))
# define deq_foreach_ref(A, T, self, i, ref)          \
    T* ref = (self)->size ? JOIN(A, at)(self, 0) : NULL; \
    for(size_t i = 0;                                 \
        i < (self)->size;                             \
        ++i, ref = JOIN(A, at)(self, i))
# define deq_foreach_range(A, T, pos, first, last)    \
    if ((self)->size)                                 \
        for(T* pos = first;                           \
            pos != last;                              \
            pos = JOIN(I, next)(pos))

# ifdef DEBUG
#  if defined(_ASSERT_H) && !defined(NDEBUG)
#  define CHECK_TAG(it,ret)                      \
     if (it->tag != CTL_DEQ_TAG)                 \
     {                                           \
         assert (it->tag == CTL_DEQ_TAG &&       \
                 "invalid deque iterator");      \
         return ret;                             \
     }
#  else
#  define CHECK_TAG(it,ret)                      \
     if (it->tag != CTL_DEQ_TAG)                 \
         return ret;
#  endif
# else
#  define CHECK_TAG(it,ret)
# endif
#else

// simplier vector iters
# ifdef DEBUG
#  if defined(_ASSERT_H) && !defined(NDEBUG)
#  define CHECK_TAG(it,ret)                      \
     if (it->tag != CTL_VEC_TAG)                 \
     {                                           \
         assert (it->tag == CTL_VEC_TAG &&       \
                 "invalid vector iterator");     \
         return ret;                             \
     }
#  else
#  define CHECK_TAG(it,ret)                      \
     if (it->tag != CTL_VEC_TAG)                 \
         return ret;
#  endif
# else
#  define CHECK_TAG(it,ret)
# endif

/* Fast typed iters */
# define vec_foreach(T, self, it)                         \
    if ((self)->size)                                     \
        for(T* it = &(self)->vector[0];                   \
            it < &(self)->vector[(self)->size];           \
            it++)
# define vec_foreach_range(T, self, it, first, last)      \
    if ((self)->size && last)                             \
        for(T* it = first;                                \
            it < last;                                    \
            it++)

#endif // not deq

#endif // not list

// slower generic iters for algorithm
#define foreach(A, IT, self, pos)                                    \
    for(IT pos = JOIN(A, begin)(self);                               \
        ((JOIN(A, it)*)pos)->ref != JOIN(A, end)(self);              \
        pos = JOIN(JOIN(A, it), next)(pos))
#define foreach_range(A, IT, pos, first, last)                       \
    for(IT pos = first;                                              \
        ((JOIN(A, it)*)pos)->ref != last;                            \
        pos = JOIN(JOIN(A, it), next)(pos))
