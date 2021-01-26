/* Fixed-size.
   SPDX-License-Identifier: MIT */

#ifndef T
# error "Template type T undefined for <ctl/array.h>"
#endif
#ifndef N
# error "Size N undefined for <ctl/array.h>"
#endif
#if N < 0 || N > (4294967296 / 8)
# error "Size N invalid for <ctl/array.h>"
#endif

#include <ctl/ctl.h>

// stack allocated if N < 2048, else heap
#define CUTOFF 2047
#define CTL_ARR
#define C PASTE(arr, N)
#define A JOIN(C, T)
#define I JOIN(A, it)

typedef struct A
{
#if N > CUTOFF
    T* vector;
#else
    T vector[N];
#endif
    void (*free)(T*);
    T (*copy)(T*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*); // optional
} A;

typedef int (*JOIN(A, compare_fn))(T*, T*);

typedef struct I
{
    CTL_T_ITER_FIELDS;
} I;

static inline size_t
JOIN(A, size)(A* self)
{
    (void) self;
    return N;
}

static inline int
JOIN(A, empty)(A* self)
{
    (void) self;
    return N == 0;
}

static inline size_t
JOIN(A, max_size)()
{
    return N;
}

static inline T*
JOIN(A, at)(A* self, size_t index)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (index < N || !"out of range");
#endif
    return index < N ? &self->vector[index] : NULL;
}

static inline T
JOIN(A, get)(A* self, size_t index)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (index < N || !"out of range");
#endif
    return self->vector[index];
}

static inline T*
JOIN(A, front)(A* self)
{
    return &self->vector[0]; // not bounds-checked
}

static inline T*
JOIN(A, back)(A* self)
{
    return &self->vector[N-1];
}

static inline T*
JOIN(A, begin)(A* self)
{
    return JOIN(A, front)(self);
}

static inline T*
JOIN(A, end)(A* self)
{
    return JOIN(A, back)(self) + 1;
}

static inline void
JOIN(I, step)(I* self)
{
    if(self->next >= self->end)
        self->done = 1;
    else
    {
        self->ref = self->next;
        self->next++;
    }
}

static inline I
JOIN(I, range)(A* container, T* begin, T* end)
{
    (void) container;
    static I zero;
    I self = zero;
    if(begin && end)
    {
        self.step = JOIN(I, step);
        self.end = end;
        self.next = begin + 1;
        self.ref = begin;
    }
    else
        self.done = 1;
    return self;
}

#include <ctl/bits/container.h>

static inline A
JOIN(A, init)(void)
{
    static A zero;
    A self = zero;
#if N > CUTOFF
    self.vector = (T*) calloc(N, sizeof(T));
//#else
//    memset(self.vector, 0, N * sizeof(T));
#endif
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
# ifndef NOT_INTEGRAL
    if (_JOIN(A, _type_is_integral)())
    {
        self.compare = _JOIN(A, _default_integral_compare);
        self.equal = _JOIN(A, _default_integral_equal);
    }
# endif
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    return self;
}

static inline A
JOIN(A, init_from)(A* copy)
{
    static A zero;
    A self = zero;
    self.free = copy->free;
    self.copy = copy->copy;
    self.compare = copy->compare;
    self.equal = copy->equal;
    return self;
}

static inline int
JOIN(A, zero)(T* ref)
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
static inline void
JOIN(A, set)(A* self, size_t index, T value)
{
    T* ref = &self->vector[index];
#ifndef POD
    if(self->free && !JOIN(A, zero)(ref))
        self->free(ref);
#endif
    *ref = value;
}

static inline void
JOIN(A, fill)(A* self, T value)
{
#if defined(POD) && !defined(NOT_INTEGRAL)
    if (sizeof(T) <= sizeof(char)) // only for bytes
        memset(self->vector, value, N * sizeof(T));
    else
        for(size_t i=0; i<N; i++)
            self->vector[i] = value;
#else
    for(size_t i=0; i<N; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#endif
#ifndef POD
    if(self->free)
        self->free(&value);
#endif
}

static inline void
JOIN(A, fill_n)(A* self, size_t n, T value)
{
    if (n >= N)
        return;
#if defined(POD) && !defined(NOT_INTEGRAL)
    if (sizeof(T) <= sizeof(char))
        memset(self->vector, value, n * sizeof(T));
    else
        for(size_t i=0; i<n; i++)
            self->vector[i] = value;
#else
    for(size_t i=0; i<n; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#endif
#ifndef POD
    if(self->free)
        self->free(&value);
#endif
}

#ifdef POD
static inline void
JOIN(A, clear)(A* self)
{
#ifndef NOT_INTEGRAL
    memset(self->vector, 0, N * sizeof(T));
#else
    static T zero;
    JOIN(A, fill)(self, zero);
#endif
}
#endif

static inline void
JOIN(A, free)(A* self)
{
#ifndef POD
    if (self->free)
        for (size_t i = 0; i < N; i++)
        {
            T* ref = &self->vector[i];
            if(!JOIN(A, zero)(ref))
                self->free(ref);
        }
#endif
    // for security reasons?
    // memset (self->vector, 0, N * sizeof(T));
#if N > CUTOFF
    free(self->vector); // heap allocated
    self->vector = NULL;
#else
    (void) self;
#endif
}

static inline void
JOIN(A, assign)(A* self, size_t count, T value)
{
    for(size_t i = 0; i < count; i++)
        JOIN(A, set)(self, i, self->copy(&value));
#ifndef POD
    if(self->free)
        self->free(&value);
#endif
}

static inline void
JOIN(A, assign_range)(A* self, T* from, T* last)
{
    //size_t count = last - from;
    JOIN(A, it) it = JOIN(I, range)(self, from, last);
    for(size_t i=0; !it.done; it.step(&it), i++)
        JOIN(A, set)(self, i, self->copy(it.ref));
}

static inline T*
JOIN(A, data)(A* self)
{
    return JOIN(A, front)(self);
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline void
JOIN(A, _ranged_sort)(A* self, long a, long b, int _compare(T*, T*))
{
    if(a >= b)
        return;
    long mid = (a + b) / 2;
    //printf("sort \"%s\" %ld, %ld\n", self->vector, a, b);
    SWAP(T, &self->vector[a], &self->vector[mid]);
    long z = a;
    for(long i = a + 1; i <= b; i++)
        if(_compare(&self->vector[a], &self->vector[i]))
        {
            z++;
            SWAP(T, &self->vector[z], &self->vector[i]);
        }
    SWAP(T, &self->vector[a], &self->vector[z]);
    if (z)
        JOIN(A, _ranged_sort)(self, a, z - 1, _compare);
    JOIN(A, _ranged_sort)(self, z + 1, b, _compare);
}

static inline void
JOIN(A, sort)(A* self)
{
    CTL_ASSERT_COMPARE
    if (N)
        JOIN(A, _ranged_sort)(self, 0, N - 1, self->compare);
//#ifdef CTL_STR
//    self->vector[self->size] = '\0';
//#endif
}

static inline A
JOIN(A, copy)(A* self)
{
    A other = JOIN(A, init)();
#ifdef POD
    memcpy(other.vector, self->vector, N * sizeof(T));
#else
    for(size_t i=0; i<N; i++)
        JOIN(A, set)(&other, i, self->copy(&self->vector[i]));
#endif
    return other;
}

static inline T*
JOIN(A, find)(A* self, T key)
{
    foreach(A, self, it)
        if (JOIN(A, _equal)(self, it.ref, &key))
            return it.ref;
    return NULL;
}

#include <ctl/algorithm.h>

#undef A
#undef I
#undef N
#undef CUTOFF

#undef C
#undef T
#undef POD
#undef NOT_INTEGRAL
#undef CTL_ARR
