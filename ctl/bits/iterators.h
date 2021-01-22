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
/* list iters loose the I* property at the start of the
 * loop already and turn into simple B* */
# define list_foreach(A, self, pos)                     \
    if ((self)->size)                                   \
        for(JOIN(A, node)* pos = JOIN(A, begin)(self);  \
            pos != NULL;                                \
            pos = JOIN(JOIN(A, it), next)(pos))
# define list_foreach_ref(A, T, self, pos, ref)         \
    T* ref = JOIN(A, front)(self);                      \
    if ((self)->size)                                   \
        for(JOIN(A, node)* pos = JOIN(A, begin)(self);  \
            pos != NULL;                                \
            pos = JOIN(JOIN(A, it), next)(pos),         \
              ref = &pos->value)
# define list_foreach_range(A, pos, first, last)        \
    if (first)                                          \
        for(JOIN(A, node)* pos = first;                 \
            pos != last;                                \
            pos = JOIN(JOIN(A, it), next)(pos))
# define list_foreach_range_ref(A, T, pos, ref, first, last) \
    T* ref = first ? first->value : NULL;               \
    if (first)                                          \
        for(JOIN(A, node)* pos = first;                 \
            pos != last;                                \
            pos = JOIN(A, JOIN(A, it)->next)(pos),      \
                ref = &pos->value)

# ifdef DEBUG
#  if defined(_ASSERT_H) && !defined(NDEBUG)
#  define CHECK_TAG(it, ret)                            \
     if (it->tag != CTL_LIST_TAG)                       \
     {                                                  \
         assert (it->tag == CTL_LIST_TAG &&             \
                 "invalid list iterator");              \
         return ret;                                    \
     }
#  else
#  define CHECK_TAG(it, ret)                            \
     if (it->tag != CTL_LIST_TAG)                       \
         return ret;
#  endif
# else
#  define CHECK_TAG(it, ret)
# endif

#else

# define CTL_T_ITER

# undef IT
# define IT T*
/* array of T*. end() = size+1 */

#ifndef CTL_DEQ

/* Make simple vector iters fast */
# define vec_foreach(T, self, ref)                       \
    if ((self)->size)                                    \
        for(T* ref = &(self)->vector[0];                 \
            ref < &(self)->vector[(self)->size];         \
            ref++)
# define vec_foreach_range(T, self, it, first, last)     \
    if ((self)->size && last.ref)                        \
        for(T* it = first.ref;                           \
            it < last.ref;                               \
            it++)

#endif // not deq

#endif // not list

// generic iters for algorithm
#define foreach(A, self, pos)                                       \
    for(JOIN(A, it) pos = JOIN(A, begin)(self);                     \
        !JOIN(JOIN(A, it), done)(&pos);                             \
        JOIN(JOIN(A, it), next)(&pos))
#define foreach_range(A, pos, first, last)                          \
    JOIN(A, it) pos = *first;                                       \
    JOIN(JOIN(A, it), range)(&pos, last);                           \
    for(; !JOIN(JOIN(A, it), done)(&pos);                           \
        JOIN(JOIN(A, it), next)(&pos))

#define foreach_n(A, self, pos, n, fn)                              \
    JOIN(A, it) pos = JOIN(A, begin)(self);                         \
    {                                                               \
        JOIN(A, it) JOIN(pos,__LINE__) = JOIN(A, begin)(self);      \
        JOIN(JOIN(A, it), advance)(&JOIN(pos,__LINE__), n);         \
        pos.end = JOIN(pos,__LINE__).end;                           \
    }                                                               \
    for(fn(pos.ref);                                                \
        !JOIN(JOIN(A, it), done)(&pos);                             \
        JOIN(JOIN(A, it), next)(&pos),                              \
        fn(pos.ref))
#define foreach_n_range(A, pos, n, first, fn)                       \
    JOIN(A, it) pos = *first;                                       \
    {                                                               \
        JOIN(A, it) JOIN(pos,__LINE__) = *first;                    \
        JOIN(JOIN(A, it), advance)(&JOIN(pos,__LINE__), n);         \
        pos.end = JOIN(pos,__LINE__).end;                           \
    }                                                               \
    for(fn(pos.ref);                                                \
        !JOIN(JOIN(A, it), done)(&pos);                             \
        JOIN(JOIN(A, it), next)(&pos),                              \
        fn(pos.ref))
