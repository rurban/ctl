/* Fixed-size.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/array.h>"
#endif
#ifndef N
#error "Size N undefined for <ctl/array.h>"
#endif
#if N < 0 || N > (4294967296 / 8)
#error "Size N invalid for <ctl/array.h>"
#endif

#include <ctl/ctl.h>

// stack allocated if N < 2048, else heap. FIXME: 4k / sizeof(T)
#define CUTOFF 2047
#define CTL_ARR
#define C PASTE(arr, N)
#define A JOIN(C, T)
#define I JOIN(A, it)
#define GI JOIN(A, it)

typedef struct A
{
#if N > CUTOFF
    T *vector;
#else
    T vector[N];
#endif
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *); // 2-way operator<
    int (*equal)(T *, T *);   // optional
} A;

typedef int (*JOIN(A, compare_fn))(T *, T *);

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_T_ITER_FIELDS;
} I;

#include <ctl/bits/iterators.h>

static inline I JOIN(I, iter)(A *self, size_t index);

static inline size_t JOIN(A, size)(A *self)
{
    (void)self;
    return N;
}

static inline int JOIN(A, empty)(A *self)
{
    (void)self;
    return N == 0;
}

static inline size_t JOIN(A, max_size)()
{
    return N;
}

static inline T *JOIN(A, at)(A *self, size_t index)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(index < N || !"out of range");
#endif
    return index < N ? &self->vector[index] : NULL;
}

static inline T JOIN(A, get)(A *self, size_t index)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(index < N || !"out of range");
#endif
    return self->vector[index];
}

static inline T *JOIN(A, front)(A *self)
{
    return &self->vector[0]; // not bounds-checked
}

static inline T *JOIN(A, back)(A *self)
{
    return &self->vector[N - 1];
}

static inline I JOIN(A, begin)(A *self)
{
    return JOIN(I, iter)(self, 0);
}

static inline I JOIN(A, end)(A *self)
{
    return JOIN(I, iter)(self, N);
}

static inline T *JOIN(I, ref)(I *iter)
{
    return iter->ref;
}

static inline size_t JOIN(I, index)(I *iter)
{
    return (iter->ref - JOIN(A, front)(iter->container)) / sizeof(T);
}

static inline int JOIN(I, done)(I *iter)
{
    return iter->ref == iter->end;
}

static inline void JOIN(I, set_done)(I *iter)
{
    iter->ref = iter->end;
}

static inline void JOIN(I, next)(I *iter)
{
    iter->ref++;
}

static inline void JOIN(I, prev)(I *iter)
{
    iter->ref--;
}

static inline void JOIN(I, range)(I *first, I *last)
{
    last->end = first->end = last->ref;
}

static inline void JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->ref;
}

static inline I *JOIN(I, advance)(I *iter, long i)
{
    // error case: overflow => end or NULL?
    if (iter->ref + i > iter->end || iter->ref + i < JOIN(A, front)(iter->container))
        iter->ref = iter->end;
    else
        iter->ref += i;
    return iter;
}

// advance end only (*_n algos)
static inline void JOIN(I, advance_end)(I *iter, long n)
{
    if (iter->ref + n <= iter->end && iter->ref + n >= JOIN(A, front)(iter->container))
        iter->end += n;
}

static inline long JOIN(I, distance)(I *iter, I *other)
{
    return other->ref - iter->ref;
}

static inline long JOIN(I, distance_range)(I *range)
{
    return range->end - range->ref;
}

static inline A JOIN(A, init_from)(A *copy);
static inline A JOIN(A, copy)(A *self);

#include <ctl/bits/container.h>

static inline I JOIN(I, iter)(A *self, size_t index)
{
    static I zero;
    I iter = zero;
    iter.ref = &self->vector[index];
    iter.end = &self->vector[N];
    iter.container = self;
    //iter.vtable = { JOIN(I, next), JOIN(I, ref), JOIN(I, done) };
    iter.vtable.next = JOIN(I, next);
    iter.vtable.ref = JOIN(I, ref);
    iter.vtable.done = JOIN(I, done);
    return iter;
}

static inline A JOIN(A, init)(void)
{
    static A zero;
    A self = zero;
#if N > CUTOFF
    self.vector = (T *)calloc(N, sizeof(T));
#else
    memset(self.vector, 0, N * sizeof(T));
#endif
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
    _JOIN(A, _set_default_methods)(&self);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    return self;
}

static inline A JOIN(A, init_from)(A *copy)
{
    static A zero;
    A self = zero;
    self.free = copy->free;
    self.copy = copy->copy;
    self.compare = copy->compare;
    self.equal = copy->equal;
    return self;
}

static inline int JOIN(A, zero)(T *ref)
{
#ifndef POD
    static T zero;
    return memcmp(ref, &zero, sizeof(T)) == 0;
#else
    (void)ref;
    return 1;
#endif
}

// not bounds-checked. like operator[]
static inline void JOIN(A, set)(A *self, size_t index, T value)
{
    T *ref = &self->vector[index];
#ifndef POD
    if (self->free && !JOIN(A, zero)(ref))
        self->free(ref);
#endif
    *ref = value;
}

static inline void JOIN(A, fill)(A *self, T value)
{
#if defined(POD) && !defined(NOT_INTEGRAL)
    if (sizeof(T) <= sizeof(char)) // only for bytes
        memset(self->vector, value, N * sizeof(T));
    else
        for (size_t i = 0; i < N; i++)
            self->vector[i] = value;
#else
    for (size_t i = 0; i < N; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#endif
#ifndef POD
    if (self->free)
        self->free(&value);
#endif
}

static inline void JOIN(A, fill_n)(A *self, size_t n, T value)
{
    if (n >= N)
        return;
#if defined(POD) && !defined(NOT_INTEGRAL)
    if (sizeof(T) <= sizeof(char))
        memset(self->vector, value, n * sizeof(T));
    else
        for (size_t i = 0; i < n; i++)
            self->vector[i] = value;
#else
    for (size_t i = 0; i < n; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#endif
#ifndef POD
    if (self->free)
        self->free(&value);
#endif
}

#ifdef POD
static inline void JOIN(A, clear)(A *self)
{
#ifndef NOT_INTEGRAL
    memset(self->vector, 0, N * sizeof(T));
#else
    static T zero;
    JOIN(A, fill)(self, zero);
#endif
}
#endif

static inline void JOIN(A, free)(A *self)
{
#ifndef POD
    if (self->free)
        for (size_t i = 0; i < N; i++)
        {
            T *ref = &self->vector[i];
            if (!JOIN(A, zero)(ref))
                self->free(ref);
        }
#endif
        // for security reasons?
        // memset (self->vector, 0, N * sizeof(T));
#if N > CUTOFF
    free(self->vector); // heap allocated
    self->vector = NULL;
#else
    (void)self;
#endif
}

static inline void JOIN(A, assign)(A *self, size_t count, T value)
{
    for (size_t i = 0; i < count; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#ifndef POD
    if (self->free)
        self->free(&value);
#endif
}

static inline void JOIN(A, assign_range)(A *self, T *from, T *last)
{
    size_t l = last - JOIN(A, front)(self);
    for (size_t i = from - JOIN(A, front)(self); i < l; i++)
        JOIN(A, set)(self, i, *JOIN(A, at)(self, i));
}

static inline T *JOIN(A, data)(A *self)
{
    return JOIN(A, front)(self);
}

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline void JOIN(A, _ranged_sort)(A *self, size_t a, size_t b, int _compare(T *, T *))
{
    if (UNLIKELY(a >= b))
        return;
    // TODO insertion_sort cutoff
    // long mid = (a + b) / 2; // overflow!
    // Dietz formula http://aggregate.org/MAGIC/#Average%20of%20Integers
    size_t mid = ((a ^ b) >> 1) + (a & b);
    // LOG("sort \"%s\" %ld, %ld\n", self->vector, a, b);
    SWAP(T, &self->vector[a], &self->vector[mid]);
    size_t z = a;
    // check overflow of a + 1
    if (LIKELY(a + 1 > a))
        for (size_t i = a + 1; i <= b; i++)
            if (_compare(&self->vector[i], &self->vector[a]))
            {
                z++;
                SWAP(T, &self->vector[z], &self->vector[i]);
            }
    SWAP(T, &self->vector[a], &self->vector[z]);
    if (LIKELY(z))
        JOIN(A, _ranged_sort)(self, a, z - 1, _compare);
    // check overflow of z + 1
    if (LIKELY(z + 1 > z))
        JOIN(A, _ranged_sort)(self, z + 1, b, _compare);
}

static inline void JOIN(A, sort)(A *self)
{
    CTL_ASSERT_COMPARE
    // TODO insertion_sort cutoff
    if (LIKELY(N > 1))
        JOIN(A, _ranged_sort)(self, 0, N - 1, self->compare);
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init)();
#ifdef POD
    memcpy(other.vector, self->vector, N * sizeof(T));
#else
    for (size_t i = 0; i < N; i++)
        JOIN(A, set)(&other, i, self->copy(&self->vector[i]));
#endif
    return other;
}

static inline T *JOIN(A, find)(A *self, T key)
{
    foreach (A, self, it)
        if (JOIN(A, _equal)(self, it.ref, &key))
            return it.ref;
    return NULL;
}

static inline A JOIN(A, transform_it)(A *self, I *pos, T _binop(T *, T *))
{
    A other = JOIN(A, init)();
    size_t i = 0;
    foreach (A, self, it)
    {
        if (pos->ref == pos->end)
            break;
#ifdef POD
        JOIN(A, set)(&other, i, _binop(it.ref, pos->ref));
#else
        T copy = self->copy(it.ref);
        T tmp = _binop(&copy, pos->ref);
        JOIN(A, set)(&other, i, tmp);
        if (self->free)
            self->free(&copy);
#endif
        i++;
        pos->ref++;
    }
    return other;
}

static inline A JOIN(A, copy_if_range)(I *range, int _match(T*))
{
    A out = JOIN(A, init_from)(range->container);
    size_t i = JOIN(I, index)(range);
    while (!JOIN(I, done)(range))
    {
        if (_match(range->ref))
            JOIN(A, set)(&out, i, out.copy(range->ref));
        i++;
        JOIN(I, next)(range);
    }
    return out;
}

static inline A JOIN(A, copy_if)(A *self, int _match(T*))
{
    A out = JOIN(A, init_from)(self);
    I range = JOIN(A, begin)(self);
    size_t i = 0;
    while (!JOIN(I, done)(&range))
    {
        if (_match(range.ref))
            JOIN(A, set)(&out, i, out.copy(range.ref));
        i++;
        JOIN(I, next)(&range);
    }
    return out;
}

#undef A
#undef I
#undef GI
#undef N
#undef CUTOFF

#undef C
#undef T
#undef POD
#undef NOT_INTEGRAL
#undef CTL_ARR
