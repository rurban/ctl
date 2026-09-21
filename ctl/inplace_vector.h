/* inplace_vector (C++26): a dynamically-resizable, fixed-capacity, contiguous
   array whose elements live inline in the container object -- it never touches
   the heap.  Capacity is the compile-time constant N; size grows and shrinks in
   [0, N].  Requires both T and N, like array.h.

   The function names use the prefix inplace_vec<N>_<T>, e.g. with
   `#define N 8` / `#define T int` the type is `inplace_vec8_int`.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/inplace_vector.h>"
#endif
#ifndef N
#error "Capacity N undefined for <ctl/inplace_vector.h>"
#endif
#if N < 1 || N > (4294967296 / 8)
#error "Capacity N invalid for <ctl/inplace_vector.h>"
#endif

#include <assert.h>
#include <ctl/ctl.h>

#define CTL_ARR /* inline storage, we provide our own size/empty/max_size */
#define CTL_IPLVEC
#define C PASTE(inplace_vec, N)
#define A JOIN(C, T)
#define I JOIN(A, it)
#define GI JOIN(A, it)

typedef struct A
{
    T vector[N];
    size_t size;
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

static inline size_t JOIN(A, size)(A *self)
{
    return self->size;
}

static inline int JOIN(A, empty)(A *self)
{
    return self->size == 0;
}

static inline size_t JOIN(A, capacity)(A *self)
{
    (void)self;
    return N;
}

static inline size_t JOIN(A, max_size)(void)
{
    return N;
}

static inline T *JOIN(A, at)(A *self, size_t index)
{
    ASSERT(index < self->size || !"out of range");
    return index < self->size ? &self->vector[index] : NULL;
}

static inline T JOIN(A, get)(A *self, size_t index)
{
    ASSERT(index < self->size || !"out of range");
    return self->vector[index];
}

static inline T *JOIN(A, front)(A *self)
{
    return &self->vector[0]; // not bounds-checked
}

static inline T *JOIN(A, back)(A *self)
{
    return self->size ? &self->vector[self->size - 1] : NULL;
}

static inline T *JOIN(A, data)(A *self)
{
    return &self->vector[0];
}

static inline I JOIN(I, iter)(A *self, size_t index);

static inline I JOIN(A, begin)(A *self)
{
    return JOIN(I, iter)(self, 0);
}

static inline I JOIN(A, end)(A *self)
{
    return JOIN(I, iter)(self, self->size);
}

static inline T *JOIN(I, ref)(I *iter)
{
    return iter->ref;
}

static inline size_t JOIN(I, index)(I *iter)
{
    return iter->ref - JOIN(A, front)(iter->container);
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

static inline void JOIN(I, set_pos)(I *iter, I *other)
{
    iter->ref = other->ref;
}

static inline void JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->ref;
}

static inline I *JOIN(I, advance)(I *iter, long i)
{
    if (iter->ref + i > iter->end || iter->ref + i < JOIN(A, front)(iter->container))
        iter->ref = iter->end;
    else
        iter->ref += i;
    return iter;
}

static inline void JOIN(I, advance_end)(I *iter, long n)
{
    if (iter->ref + n <= iter->end && iter->ref + n >= JOIN(A, front)(iter->container))
        iter->end += n;
}

static inline long JOIN(I, distance)(I *iter, I *other)
{
    return other->ref - iter->ref;
}

static inline size_t JOIN(I, distance_range)(I *range)
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
    iter.end = &self->vector[self->size];
    iter.container = self;
    iter.vtable.next = JOIN(I, next);
    iter.vtable.ref = JOIN(I, ref);
    iter.vtable.done = JOIN(I, done);
    return iter;
}

static inline A JOIN(A, init)(void)
{
    static A zero;
    A self = zero;
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

static inline int JOIN(A, _zero)(T *ref)
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
    if (self->free && !JOIN(A, _zero)(ref))
        self->free(ref);
#endif
    *ref = value;
}

static inline void JOIN(A, push_back)(A *self, T value)
{
    ASSERT(self->size < N || !"inplace_vector capacity exceeded");
    if (self->size < N)
        self->vector[self->size++] = value;
    else if (self->free)
        self->free(&value);
}

// checked push: returns the slot, or NULL (freeing value) when full
static inline T *JOIN(A, try_push_back)(A *self, T value)
{
    if (self->size < N)
    {
        T *ref = &self->vector[self->size++];
        *ref = value;
        return ref;
    }
    if (self->free)
        self->free(&value);
    return NULL;
}

static inline void JOIN(A, emplace_back)(A *self, T *value)
{
    ASSERT(self->size < N || !"inplace_vector capacity exceeded");
    if (self->size < N)
        self->vector[self->size++] = *value;
}

static inline void JOIN(A, pop_back)(A *self)
{
    static T zero;
    ASSERT(self->size > 0 || !"pop_back on empty");
    if (!self->size)
        return;
    self->size--;
    JOIN(A, set)(self, self->size, zero);
}

static inline void JOIN(A, wipe)(A *self, size_t n)
{
    while (n != 0 && self->size)
    {
        JOIN(A, pop_back)(self);
        n--;
    }
}

static inline void JOIN(A, clear)(A *self)
{
    if (self->size > 0)
        JOIN(A, wipe)(self, self->size);
}

static inline void JOIN(A, free)(A *self)
{
    JOIN(A, clear)(self);
    JOIN(A, compare_fn) compare = self->compare;
    JOIN(A, compare_fn) equal = self->equal;
    *self = JOIN(A, init)();
    self->compare = compare;
    self->equal = equal;
}

static inline void JOIN(A, insert_index)(A *self, size_t index, T value)
{
    ASSERT(self->size < N || !"inplace_vector capacity exceeded");
    if (self->size >= N)
    {
        if (self->free)
            self->free(&value);
        return;
    }
    if (self->size > 0 && index < self->size)
    {
        self->size++;
        for (size_t i = self->size - 1; i > index; i--)
            self->vector[i] = self->vector[i - 1];
        self->vector[index] = value;
    }
    else
        self->vector[self->size++] = value;
}

static inline I JOIN(A, erase_index)(A *self, size_t index)
{
    static T zero;
    ASSERT(index < self->size || !"out of range");
    if (self->free)
        self->free(&self->vector[index]);
    if (index < self->size - 1)
        memmove(&self->vector[index], &self->vector[index + 1], (self->size - index - 1) * sizeof(T));
    self->vector[self->size - 1] = zero;
    self->size--;
    return JOIN(I, iter)(self, index);
}

static inline void JOIN(A, insert)(I *pos, T value)
{
    A *self = pos->container;
    if (!JOIN(I, done)(pos))
    {
        size_t index = pos->ref - self->vector;
        size_t end = pos->end - self->vector;
        JOIN(A, insert_index)(self, index, value);
        pos->ref = &self->vector[index];
        pos->end = &self->vector[end < self->size ? end + 1 : self->size];
    }
    else
    {
        JOIN(A, push_back)(self, value);
        pos->end = pos->ref = &self->vector[self->size];
    }
}

static inline I JOIN(A, erase)(I *pos)
{
    A *self = pos->container;
    return JOIN(A, erase_index)(self, JOIN(I, index)(pos));
}

static inline I *JOIN(A, erase_range)(I *range)
{
    if (JOIN(I, done)(range))
        return range;
    A *self = range->container;
    T *end = &self->vector[self->size];
    size_t count = range->end - range->ref;
#ifndef POD
    if (self->free)
        for (T *ref = range->ref; ref < range->end; ref++)
            self->free(ref);
#endif
    if (range->end != end)
        memmove(range->ref, range->end, (end - range->end) * sizeof(T));
    memset(end - count, 0, count * sizeof(T));
    self->size -= count;
    return range;
}

static inline void JOIN(A, resize)(A *self, size_t size, T value)
{
    ASSERT(size <= N || !"inplace_vector capacity exceeded");
    if (size > N)
        size = N;
    if (size < self->size)
        JOIN(A, wipe)(self, self->size - size);
    else
        while (self->size < size)
            JOIN(A, push_back)(self, self->copy(&value));
    if (self->free)
        self->free(&value);
}

static inline void JOIN(A, assign)(A *self, size_t count, T value)
{
    ASSERT(count <= N || !"inplace_vector capacity exceeded");
    if (count > N)
        count = N;
    JOIN(A, clear)(self);
    for (size_t i = 0; i < count; i++)
        JOIN(A, push_back)(self, self->copy(&value));
    if (self->free)
        self->free(&value);
}

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init_from)(self);
    for (size_t i = 0; i < self->size; i++)
        JOIN(A, push_back)(&other, other.copy(&self->vector[i]));
    return other;
}

static inline void JOIN(A, _ranged_sort)(A *self, long a, long b, int _compare(T *, T *))
{
    if (a >= b)
        return;
    long mid = ((a ^ b) >> 1) + (a & b);
    SWAP(T, &self->vector[a], &self->vector[mid]);
    long z = a;
    for (long i = a + 1; i <= b; i++)
        if (_compare(&self->vector[i], &self->vector[a]))
        {
            z++;
            SWAP(T, &self->vector[z], &self->vector[i]);
        }
    SWAP(T, &self->vector[a], &self->vector[z]);
    JOIN(A, _ranged_sort)(self, a, z - 1, _compare);
    JOIN(A, _ranged_sort)(self, z + 1, b, _compare);
}

static inline void JOIN(A, sort)(A *self)
{
    CTL_ASSERT_COMPARE
    if (self->size > 1)
        JOIN(A, _ranged_sort)(self, 0, (long)self->size - 1, self->compare);
}

static inline I JOIN(A, find)(A *self, T key)
{
    vec_foreach(T, self, ref) if (JOIN(A, _equal)(self, ref, &key)) return JOIN(I, iter)(self, ref - &self->vector[0]);
    return JOIN(A, end)(self);
}

static inline size_t JOIN(A, remove_if)(A *self, int (*_match)(T *))
{
    size_t erases = 0;
    for (size_t i = 0; i < self->size;)
    {
        if (_match(&self->vector[i]))
        {
            JOIN(A, erase_index)(self, i);
            erases++;
        }
        else
            i++;
    }
    return erases;
}

static inline size_t JOIN(A, erase_if)(A *self, int (*_match)(T *))
{
    return JOIN(A, remove_if)(self, _match);
}

#undef A
#undef I
#undef GI
#undef C
#undef CTL_ARR
#undef CTL_IPLVEC
#undef N
#undef T
#undef POD
#undef NOT_INTEGRAL
