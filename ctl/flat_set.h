/* flat_set (C++23): a sorted associative container backed by a single
   contiguous vector, holding unique keys ordered by `compare`.
   Search is O(log n), insert/erase are O(n) (shifting the tail).
   Derives from vector.h, hiding the vector methods whose set semantics differ.

   With CTL_FLAT_MULTI defined it becomes a flat_multiset (duplicate keys kept,
   equal keys ordered by insertion). map.h-style children (flat_map,
   flat_multimap) remap the `fset` prefix and add key/value methods.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/flat_set.h>"
#endif

#include <ctl/ctl.h>
#include <assert.h>

#define CTL_FLAT_SET

/* Remember whether an outer child (flat_map) wants us to preserve T/A. */
#ifdef HOLD
#define _FLAT_SET_HOLD
#endif

/* The vector layer auto-includes algorithm.h on INCLUDE_ALGORITHM, but it
   references the very methods (find/erase/insert) we hide below.  Suppress it
   across the vector include and restore the caller's setting afterwards. */
#ifdef INCLUDE_ALGORITHM
#define _FLAT_SET_HAD_ALGORITHM
#undef INCLUDE_ALGORITHM
#endif

/* Derive from vector.h.  `vec` becomes our prefix (fset, or fmap/fmset/fmmap
   when a child remapped it), HOLD preserves T for our own code below. */
#define vec fset
#define HOLD
#define init __INIT
#define insert __INSERT
#define find __FIND
#define erase __ERASE
#define emplace __EMPLACE
#include <ctl/vector.h>
#undef init
#undef insert
#undef find
#undef erase
#undef emplace
#undef vec

#ifdef _FLAT_SET_HAD_ALGORITHM
#define INCLUDE_ALGORITHM
#undef _FLAT_SET_HAD_ALGORITHM
#endif

#define A JOIN(fset, T)
#define I JOIN(A, it)
#define GI JOIN(A, it)

/* index of the first element not less than *key (lower bound) */
static inline size_t JOIN(A, _lower_bound_i)(A *self, T *key)
{
    size_t lo = 0, hi = self->size;
    while (lo < hi)
    {
        size_t mid = lo + ((hi - lo) >> 1);
        if (self->compare(&self->vector[mid], key))
            lo = mid + 1;
        else
            hi = mid;
    }
    return lo;
}

/* index of the first element greater than *key (upper bound) */
static inline size_t JOIN(A, _upper_bound_i)(A *self, T *key)
{
    size_t lo = 0, hi = self->size;
    while (lo < hi)
    {
        size_t mid = lo + ((hi - lo) >> 1);
        if (self->compare(key, &self->vector[mid]))
            hi = mid;
        else
            lo = mid + 1;
    }
    return lo;
}

static inline A JOIN(A, init)(int _compare(T *, T *))
{
    A self = JOIN(A, __INIT)();
    if (_compare)
        self.compare = _compare;
    else
        _JOIN(A, _set_default_methods)(&self);
    return self;
}

/* lookups borrow the key; they never free it (see set.h find/erase) */
static inline I JOIN(A, lower_bound)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    return JOIN(I, iter)(self, JOIN(A, _lower_bound_i)(self, &key));
}

static inline I JOIN(A, upper_bound)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    return JOIN(I, iter)(self, JOIN(A, _upper_bound_i)(self, &key));
}

/* does not consume/free the key (like set.find) */
static inline I JOIN(A, find)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    size_t i = JOIN(A, _lower_bound_i)(self, &key);
    if (i < self->size && !self->compare(&key, &self->vector[i]))
        return JOIN(I, iter)(self, i);
    return JOIN(A, end)(self);
}

static inline size_t JOIN(A, count)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    size_t lo = JOIN(A, _lower_bound_i)(self, &key);
#ifdef CTL_FLAT_MULTI
    size_t n = JOIN(A, _upper_bound_i)(self, &key) - lo;
#else
    size_t n = (lo < self->size && !self->compare(&key, &self->vector[lo])) ? 1 : 0;
#endif
    return n;
}

static inline int JOIN(A, contains)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    size_t i = JOIN(A, _lower_bound_i)(self, &key);
    int found = i < self->size && !self->compare(&key, &self->vector[i]);
    return found;
}

/* fills lower/upper with the [first,last) range equal to key */
static inline void JOIN(A, equal_range)(A *self, T key, I *lower, I *upper)
{
    CTL_ASSERT_COMPARE
    size_t lo = JOIN(A, _lower_bound_i)(self, &key);
#ifdef CTL_FLAT_MULTI
    size_t hi = JOIN(A, _upper_bound_i)(self, &key);
#else
    size_t hi = (lo < self->size && !self->compare(&key, &self->vector[lo])) ? lo + 1 : lo;
#endif
    *lower = JOIN(I, iter)(self, lo);
    *upper = JOIN(I, iter)(self, hi);
}

static inline I JOIN(A, insert)(A *self, T value)
{
    CTL_ASSERT_COMPARE
#ifdef CTL_FLAT_MULTI
    size_t i = JOIN(A, _upper_bound_i)(self, &value);
    JOIN(A, insert_index)(self, i, value);
    return JOIN(I, iter)(self, i);
#else
    size_t i = JOIN(A, _lower_bound_i)(self, &value);
    if (i < self->size && !self->compare(&value, &self->vector[i]))
    {
        if (self->free)
            self->free(&value);
        return JOIN(I, iter)(self, i);
    }
    JOIN(A, insert_index)(self, i, value);
    return JOIN(I, iter)(self, i);
#endif
}

static inline I JOIN(A, insert_found)(A *self, T value, int *foundp)
{
    CTL_ASSERT_COMPARE
    size_t i = JOIN(A, _lower_bound_i)(self, &value);
    int found = i < self->size && !self->compare(&value, &self->vector[i]);
    *foundp = found;
#ifdef CTL_FLAT_MULTI
    if (found)
        i = JOIN(A, _upper_bound_i)(self, &value);
    JOIN(A, insert_index)(self, i, value);
    return JOIN(I, iter)(self, i);
#else
    if (found)
    {
        if (self->free)
            self->free(&value);
        return JOIN(I, iter)(self, i);
    }
    JOIN(A, insert_index)(self, i, value);
    return JOIN(I, iter)(self, i);
#endif
}

static inline I JOIN(A, emplace)(A *self, T *value)
{
    return JOIN(A, insert)(self, *value);
}

/* erases all elements equal to key, returns the count removed */
static inline size_t JOIN(A, erase)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    size_t lo = JOIN(A, _lower_bound_i)(self, &key);
#ifdef CTL_FLAT_MULTI
    size_t n = JOIN(A, _upper_bound_i)(self, &key) - lo;
    for (size_t k = 0; k < n; k++)
        JOIN(A, erase_index)(self, lo);
#else
    size_t n = 0;
    if (lo < self->size && !self->compare(&key, &self->vector[lo]))
    {
        JOIN(A, erase_index)(self, lo);
        n = 1;
    }
#endif
    return n;
}

static inline I JOIN(A, erase_it)(I *pos)
{
    A *self = pos->container;
    return JOIN(A, erase_index)(self, JOIN(I, index)(pos));
}

#ifndef _FLAT_SET_HOLD
#undef A
#undef I
#undef GI
#undef T
#undef POD
#undef NOT_INTEGRAL
#undef CTL_FLAT_SET
#ifdef CTL_FLAT_MULTI
#undef CTL_FLAT_MULTI
#endif
#else
#undef _FLAT_SET_HOLD
/* keep A, I, GI, T, CTL_FLAT_SET and CTL_FLAT_MULTI for the child */
#endif
