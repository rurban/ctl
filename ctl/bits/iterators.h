/* Abstract IT (T* value, B* node or size_t index) and foreach_range.

   We have three major kinds of iterators:
   - returning B* nodes (list, set, uset)
   - returning T* valuerefs directly (arrays).
   - returning size_t index directly (deque).

   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
#error "Template type IT undefined for <ctl/bits/iterators.h>"
#endif

#if defined CTL_LIST || defined CTL_SET || defined CTL_USET
#  define CTL_B_ITER
/* return B* it.node. end is NULL */
#  define iter_ITp(iter) (iter)->node
#  define iter_IT_endp(iter) (iter->done ? NULL : iter->node)
#  define iter_IT(iter) (iter).node
#  define iter_IT_end(iter) (iter.done ? NULL : iter.node)
#  define foreach_range(A, it, first, last)      \
      if (last && !last->done)                   \
          first->end = last->node;               \
      if (first->node == last->node)             \
          first->done = 1;                       \
      for(JOIN(A, it) it = *first; !it.done; it.step(&it))

#else

#  define CTL_T_ITER
#  if defined CTL_VEC || defined CTL_ARR
#    define IT T*
/* return it.ref */
#    define iter_ITp(iter) (iter)->ref
#    define iter_IT_endp(iter) (iter->done ? NULL : iter->ref)
#    define iter_IT(iter) (iter).ref
#    define iter_IT_end(iter) (iter.done ? NULL : iter.ref)
#    define foreach_range(A, it, first, last)       \
     if (!last->done)                               \
          first->end = last->end;                   \
      for(JOIN(A, it) it = *first; !it.done; it.step(&it))

# else // DEQ
#   define IT size_t
/* return it.index */
#   define iter_ITp(iter) (iter)->index
#   define iter_IT_endp(iter) (iter->done ? NULL : iter->index)
#   define iter_IT(iter) (iter).index
#   define iter_IT_end(iter) (iter.done ? NULL : iter.index)
#   define foreach_range(A, it, first, last)       \
    if (!last->done)                               \
          first->index_last = last->index;         \
      for(JOIN(A, it) it = *first; !it.done; it.step(&it))

# endif

#endif // T_ITER
