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
#  define iter_IT_endp(iter) ((iter)->done ? NULL : (iter)->node)
#  define iter_IT(iter) (iter).node
#  define iter_IT_end(iter) ((iter).done ? NULL : (iter).node)
#  define foreach_range(A, it, first, last)      \
    A* _itercont = first->container;             \
    if (last)                                    \
        first->end = last->node;                 \
    foreach(A, _itercont, it)

# else

#  define CTL_T_ITER
#  define IT T
/* return it.ref */
#  define iter_ITp(iter) (iter)->ref
#  define iter_IT_endp(iter) ((iter)->done ? NULL : (iter)->ref)
#  define iter_IT(iter) (iter).ref
#  define iter_IT_end(iter) ((iter).done ? NULL : (iter).ref)
#  ifdef CTL_VEC
#   define foreach_range(A, it, first, last)       \
      A* _itercont = first->container;             \
      if (last != JOIN(A, end)(_itercont))         \
          first->end = last->end;                  \
      foreach(A, _itercont, it)
#  else // DEQ
    /*  T -> I, deque needs the container
        TODO: maybe switch to pointers */
#   define foreach_range(A, it, first, last)       \
      A* _itercont = first->container;             \
      if (last != JOIN(A, end)(_itercont))         \
          first->index_last = last->index;         \
      foreach(A, _itercont, it)
#  endif

# endif // T_ITER
#endif // IT
