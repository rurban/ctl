/* Abstract IT (T* or B*) and foreach_range.

   See MIT LICENSE
   We have two major kinds of iterators:
   - returning B* nodes (list, set, uset), and
   - returning T* valuerefs directly (arrays).
*/

#if !defined IT /* && !defined foreach_range */
# if defined CTL_LIST || defined CTL_SET || defined CTL_USET
#  define CTL_B_ITER
#  define IT B
/* return it.node. end is NULL */
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

# else

#  define CTL_T_ITER
#  define IT T
/* return it.ref */
#  define iter_ITp(iter) (iter)->ref
#  define iter_IT_endp(iter) (iter->done ? NULL : iter->ref)
#  define iter_IT(iter) (iter).ref
#  define iter_IT_end(iter) (iter.done ? NULL : iter.ref)
#  if defined CTL_VEC || defined CTL_ARR
#   define foreach_range(A, it, first, last)       \
    if (!last->done)                               \
          first->end = last->end;                  \
      for(JOIN(A, it) it = *first; !it.done; it.step(&it))

#  else // DEQ
    /*  T -> I, deque needs the container
        TODO: maybe switch to pointers */
#   define foreach_range(A, it, first, last)       \
    if (!last->done)                               \
          first->index_last = last->index;         \
      for(JOIN(A, it) it = *first; !it.done; it.step(&it))

#  endif

# endif // T_ITER
#endif // IT
