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

#if defined CTL_LIST || defined CTL_SET || defined CTL_USET
#  define CTL_B_ITER
#  undef IT
#  define IT B*
/* return B* it node. end is NULL */

#ifndef foreach
# define foreach(A, T, self, it) \
    JOIN(A, node) *it; \
    for(it = JOIN(A, begin)(self); it; it = it->next)
# define foreach_ref(A, T, self, it, ref) \
    JOIN(A, node) *it; \
    T* ref; \
    for(it = JOIN(A, begin)(self), ref = &it->value; it; it = JOIN(B, next)(it), ref = &it->value)
# define foreach_range(A, T, self, it, first, last) \
    JOIN(A, node) *it; \
    for(it = first; it; it = JOIN(B, next)(it))
# define foreach_ref_range(A, T, self, it, ref, first, last) \
    JOIN(A, node) *it; \
    T* ref; \
    for(it = first, ref = &first->value; \
        last == NULL ? it != NULL : it != last; \
        it = JOIN(B, next)(it), ref = &it->value)
# endif

#else

# define CTL_T_ITER

# if defined CTL_VEC || defined CTL_ARR
#  undef IT
#  define IT T*
/* array of T*. end() = size+1 */

#ifndef foreach
# define foreach(A, T, self, it) \
    T *it; \
    T* _JOIN(A, __endvar) = JOIN(A, end)(self); \
    for(it = JOIN(A, begin)(self); it < _JOIN(A, __endvar); it++)
# define foreach_ref(A, T, self, it, ref) \
    T *it; \
    T *ref; \
    T* _JOIN(A, __endvar) = JOIN(A, end)(self); \
    for(ref = it = JOIN(A, begin)(self); it < _JOIN(A, __endvar); it++, ref = it)
# define foreach_range(A, T, self, it, first, last) \
    T *it; \
    for(it = first; it < last; it++)
# define foreach_ref_range(A, T, self, it, ref, first, last) \
    T* it; \
    T* ref; \
    for(ref = it = first; it < last; it++, ref = it)
# endif

# else // DEQ

#  undef IT
#  define IT size_t
/* return it index */

#ifndef foreach
# define foreach(A, T, self, it) \
    size_t _JOIN(A, __endvar) = JOIN(A, end)(self); \
    for(size_t it = JOIN(A, begin)(self); it < _JOIN(A, __endvar); it++)
# define foreach_ref(A, T, self, it, ref) \
    T* ref = JOIN(A, at)(self, 0); \
    size_t _JOIN(A, __endvar) = JOIN(A, end)(self); \
    for(size_t it = JOIN(A, begin)(self); it < _JOIN(A, __endvar); ref = JOIN(A, at)(self, it), it++)
# define foreach_range(A, T, self, it, first, last) \
    for(size_t it = first; it < last; it++)
# define foreach_ref_range(A, T, self, it, ref, first, last)    \
    T* ref = JOIN(A, at)(self, first); \
    for(size_t it = first; it < last; ref = JOIN(A, at)(self, it), it++)
# endif
# endif

#endif // T_ITER
