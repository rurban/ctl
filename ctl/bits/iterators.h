/* Abstract IT (T* value, B* node or size_t index)
   foreach, foreach_range.

   We have three major kinds of iterators:
   - returning B* nodes (list, set, uset)
   - returning T* valuerefs directly (arrays).
   - returning size_t index directly (deque).

   An iterator should be simply incremented:
     IT it; it++ resp. it = it->next for lists.

   Copyright 2021 Reini Urban
   See MIT LICENSE
*/

#ifndef T
# error "Template type T undefined for <ctl/bits/iterators.h>"
#endif

/* Old iterator with extra B nodes */
#define CTL_B_ITER_FIELDS     \
    B* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    B* end;                   \
    int done;                 \
    B* node;                  \
    A* container

/* Old iterator with simple arrays of T, no intermediate nodes of B */
#define CTL_T_ITER_FIELDS     \
    T* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    T* end;                   \
    int done;                 \
    A* container

#if defined CTL_LIST || defined CTL_SET || defined CTL_MAP
#  define CTL_B_ITER
#  undef IT
#  define IT B*
/* return B* it node. end is NULL */

B* JOIN(B, next)(B*);

#ifndef foreach
# define foreach(C, T, self, it) \
    T* ref; \
    for(JOIN(C, JOIN(T, node)) *it = JOIN(C, JOIN(T, begin))(self); \
        it; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(it))
# define foreach_ref(C, T, self, it, ref) \
    for(JOIN(C, JOIN(T, node)) *it = JOIN(C, JOIN(T, begin))(self), ref = &it->value; \
        it;                                                             \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(it), ref = &it->value)
# define foreach_range(C, T, self, it, first, last) \
    for(JOIN(C, JOIN(T, node)) *it = first; \
        it; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(it))
# define foreach_ref_range(C, T, self, it, ref, first, last) \
    T* ref; \
    for(JOIN(C, JOIN(T, node)) *it = first, ref = &first->value; \
        last == NULL ? it != NULL : it != last; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(it), ref = &it->value)
# endif

#elif defined CTL_USET || defined CTL_UMAP
// different bucket next method
#  define CTL_B_ITER
#  undef IT
#  define IT B*
/* return B* it node. end is NULL */

//B* JOIN(B, next)(A*, B*);

#ifndef foreach
# define foreach(C, T, self, it) \
    for(JOIN(C, JOIN(T, node)) *it = JOIN(C, JOIN(T, begin))(self); \
        it; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(self, it))
# define foreach_ref(C, T, self, it, ref) \
    T* ref; \
    for(JOIN(C, JOIN(T, node)) *it = JOIN(C, JOIN(T, begin))(self), ref = &(it->value); \
        it; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(self, it), ref = &(it->value))
# define foreach_range(C, T, self, it, first, last)  \
    for(JOIN(C, JOIN(T, node)) *it = first; \
        it; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(self, it))
# define foreach_ref_range(C, T, self, it, ref, first, last) \
    T* ref; \
    for(JOIN(C, JOIN(T, node)) *it = first, ref = &first->value; \
        last == NULL ? it != NULL : it != last; \
        it = JOIN(JOIN(C, JOIN(T, node)), next)(self, it), ref = &(it->value))
# endif

#else

# define CTL_T_ITER

# if defined CTL_VEC || defined CTL_ARR
#  undef IT
#  define IT T*
/* array of T*. end() = size+1 */

#ifndef foreach
# define foreach(C, T, self, it) \
    if (!JOIN(C, JOIN(T, empty))(self)) \
      for(T* it = JOIN(C, JOIN(T, begin))(self); \
          it < JOIN(C, JOIN(T, end))(self); \
          it++)
# define foreach_ref(C, T, self, it, ref) \
    T* ref; \
    if (!JOIN(C, JOIN(T, empty))(self)) \
        for(T* it = ref = JOIN(C, JOIN(T, begin))(self); \
            it < JOIN(C, JOIN(T, end))(self);            \
            it++, ref = it)
# define foreach_range(C, T, self, it, first, last) \
    if (last) \
        for(T* it = first; \
            it < last; \
            it++)
# define foreach_ref_range(C, T, self, it, ref, first, last) \
    T* ref; \
    if (last) \
        for(T* it = ref = first; \
            it < last; \
            it++, ref = it)
# endif

# else // DEQ

#  undef IT
#  define IT size_t
/* return it index */

#ifndef foreach
# define foreach(C, T, self, it) \
    for(size_t it = JOIN(C, JOIN(T, begin))(self); it < JOIN(C, JOIN(T, end))(self); it++)
# define foreach_ref(C, T, self, it, ref) \
    T* ref = JOIN(C, JOIN(T, at))(self, 0); \
    for(size_t it = JOIN(C, JOIN(T, begin))(self); \
        it < JOIN(C, JOIN(T, end))(self); \
        ref = JOIN(C, JOIN(T, at))(self, it), it++)
# define foreach_range(C, T, self, it, first, last) \
    for(size_t it = first; it < last; it++)
# define foreach_ref_range(C, T, self, it, ref, first, last) \
    T* ref = JOIN(C, JOIN(T, at))(self, first); \
    for(size_t it = first; \
        it < last; \
        ref = JOIN(C, JOIN(T, at))(self, it), it++)
# endif
# endif

#endif // T_ITER
