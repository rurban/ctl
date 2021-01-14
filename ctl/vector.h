/* Arrays that can change in size.
   SPDX-License-Identifier: MIT */

// TODO emplace, emplace_back

#ifndef T
#error "Template type T undefined for <ctl/vector.h>"
#endif

#include <ctl/ctl.h>

#define CTL_VEC
#define A JOIN(vec, T)
#define I JOIN(A, it)

// only for short strings, not vec_uint8_t
#ifndef MUST_ALIGN_16
# define MUST_ALIGN_16(T) 0
# define INIT_SIZE 1
#else
# define INIT_SIZE 15
#endif

typedef struct A
{
    T* value;
    void (*free)(T*);
    T (*copy)(T*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*); // optional
    size_t size;
    size_t capacity;
} A;

typedef int (*JOIN(A, compare_fn))(T*, T*);

typedef struct I
{
    CTL_T_ITER_FIELDS;
} I;

static inline size_t
JOIN(A, capacity)(A* self)
{
    return self->capacity;
}

static inline T*
JOIN(A, at)(A* self, size_t index)
{
    return &self->value[index];
}

static inline T*
JOIN(A, front)(A* self)
{
    return JOIN(A, at)(self, 0);
}

static inline T*
JOIN(A, back)(A* self)
{
    return JOIN(A, at)(self, self->size - 1);
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
JOIN(A, _init)(A* copy)
{
    static A zero;
    A self = zero;
    self.free = copy->free;
    self.copy = copy->copy;
    self.compare = copy->compare;
    self.equal = copy->equal;
    return self;
}

static inline void
JOIN(A, set)(A* self, size_t index, T value)
{
    T* ref = JOIN(A, at)(self, index);
    if(self->free)
        self->free(ref);
    *ref = value;
}

static inline void
JOIN(A, pop_back)(A* self)
{
    static T zero;
    self->size--;
    JOIN(A, set)(self, self->size, zero);
}

static inline void
JOIN(A, wipe)(A* self, size_t n)
{
    while(n != 0)
    {
        JOIN(A, pop_back)(self);
        n--;
    }
}

static inline void
JOIN(A, clear)(A* self)
{
    if(self->size > 0)
        JOIN(A, wipe)(self, self->size);
}

static inline void
JOIN(A, free)(A* self)
{
    JOIN(A, clear)(self);
    JOIN(A, compare_fn) *compare = &self->compare;
    JOIN(A, compare_fn) *equal = &self->equal;
    free(self->value);
    *self = JOIN(A, init)();
    self->compare = *compare;
    self->equal = *equal;
}

static inline void
JOIN(A, fit)(A* self, size_t capacity)
{
    size_t overall = capacity;
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (capacity < JOIN(A, max_size)() || !"max_size overflow");
#endif
    if(MUST_ALIGN_16(T)) // reserve terminating \0 for strings
        overall++;
    self->value = (T*) realloc(self->value, overall * sizeof(T));
    if(MUST_ALIGN_16(T))
    {
#if 0
        static T zero;
        for(size_t i = self->capacity; i < overall; i++)
            self->value[i] = zero;
#else
        if (overall > self->capacity)
            memset (&self->value[self->capacity], 0, overall - self->capacity);
#endif
    }
    self->capacity = capacity;
}

static inline void
JOIN(A, reserve)(A* self, const size_t n)
{
    const size_t max_size = JOIN(A, max_size)();
    if(n > max_size)
    {
#if defined(_ASSERT_H) && !defined(NDEBUG)
        assert (n < max_size || !"max_size overflow");
#endif
        return;
    }
#ifdef CTL_STR
    if(self->capacity != n)
#else
    // never shrink vectors with reserve
    if(self->capacity < n)
#endif
    {
        // don't shrink, but shrink_to_fit
        size_t actual = n < self->size ? self->size : n;
        if(actual > 0)
        {
#ifdef CTL_STR
            // reflecting gcc libstdc++ with __cplusplus >= 201103L < 2021 (gcc-10)
            if (actual > self->capacity) // double it
            {
                if (actual < 2 * self->capacity)
                    actual = 2 * self->capacity;
                if (actual > max_size)
                    actual = max_size;
# ifdef _LIBCPP_STD_VER
                // with libc++ round up to 16
                // which versions? this is 18 (being 2018 for clang 10)
                // but I researched it back to the latest change in __grow_by in
                // PR17148, 2013
                // TODO: Is there a _LIBCPP_STD_VER 13?
                if (actual > 30)
                    actual = ((actual & ~15) == actual)
                        ? (actual + 15)
                        : ((actual + 15) & ~15)- 1;
# endif
                JOIN(A, fit)(self, actual);
            }
            else
#endif
                JOIN(A, fit)(self, actual);
        }
    }
}

static inline void
JOIN(A, push_back)(A* self, T value)
{
    if(self->size == self->capacity)
        JOIN(A, reserve)(self,
            self->capacity == 0 ? INIT_SIZE : 2 * self->capacity);
    *JOIN(A, at)(self, self->size) = value;
    self->size++;
//#ifdef CTL_STR
//    self->value[self->size] = '\0';
//#endif
}

static inline void
JOIN(A, resize)(A* self, size_t size, T value)
{
    if(size < self->size)
    {
        int64_t less = self->size - size;
        if(less > 0)
            JOIN(A, wipe)(self, less);
    }
    else
    {
        if(size > self->capacity)
        {
#ifdef CTL_STR
            size_t capacity = 2 * self->capacity;
            if(size > capacity)
                capacity = size;
            JOIN(A, reserve)(self, capacity);
#else       // different vector growth policy. double or just grow as needed.
            size_t capacity;
            size_t n = size > self->size ? size - self->size : 0;
            LOG("  grow vector by %zu with size %zu\n", n, self->size);
            capacity = self->size + (self->size > n ? self->size : n);
            JOIN(A, fit)(self, capacity);
#endif
        }
        for(size_t i = 0; self->size < size; i++)
            JOIN(A, push_back)(self, self->copy(&value));
    }
    if(self->free)
        self->free(&value);
}

static inline void
JOIN(A, assign)(A* self, size_t count, T value)
{
    JOIN(A, resize)(self, count, self->copy(&value));
    for(size_t i = 0; i < count; i++)
        JOIN(A, set)(self, i, self->copy(&value));
    if(self->free)
        self->free(&value);
}

static inline void
JOIN(A, assign_range)(A* self, T* from, T* last)
{
    size_t count = last - from;
    JOIN(A, resize)(self, count, self->copy(self->value)); // TODO
    JOIN(A, it) it = JOIN(I, range)(self, from, last);
    for(size_t i=0; !it.done; it.step(&it), i++)
        JOIN(A, set)(self, i, *it.ref);
}

static inline void
JOIN(A, shrink_to_fit)(A* self)
{
    if(MUST_ALIGN_16(T) && self->size <= 15)
    {
        size_t size = ((self->size + 15) & ~15) - 1;
        JOIN(A, fit)(self, size);
    }
    else
        JOIN(A, fit)(self, self->size);
}

static inline T*
JOIN(A, data)(A* self)
{
    return JOIN(A, front)(self);
}

static inline void
JOIN(A, insert)(A* self, size_t index, T value)
{
    if(self->size > 0)
    {
        JOIN(A, push_back)(self, *JOIN(A, back)(self));
        for(size_t i = self->size - 2; i > index; i--)
            self->value[i] = self->value[i - 1];
        self->value[index] = value;
    }
    else
        JOIN(A, push_back)(self, value);
}

static inline T*
JOIN(A, erase)(A* self, size_t index)
{
    static T zero;
    JOIN(A, set)(self, index, zero);
    // TODO memmove
    for(size_t i = index; i < self->size - 1; i++)
    {
        self->value[i] = self->value[i + 1];
        self->value[i + 1] = zero;
    }
    self->size--;
    return &self->value[self->size - 1];
}

static inline T*
JOIN(A, erase_range)(A* self, T* from, T* to)
{
    static T zero;
    if (from >= to)
        return to;
    T* end = &self->value[self->size];
    // TODO memmove
    *from = zero;
    for(T* pos = from; pos < to - 1; pos++)
    {
        *pos = *(pos + 1);
        *(pos + 1) = zero;
        self->size--;
    }
    if (to < end)
        return to + 1;
    else
        return to;
}

static inline T*
JOIN(A, erase_it)(A* self, T* pos)
{
    return JOIN(A, erase_range)(self, pos, JOIN(A, end)(self));
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
    JOIN(A, shrink_to_fit)(self);
}

static inline void
JOIN(A, _ranged_sort)(A* self, long a, long b, int _compare(T*, T*))
{
    if(a >= b)
        return;
    long mid = (a + b) / 2;
    //printf("sort \"%s\" %ld, %ld\n", self->value, a, b);
    SWAP(T, &self->value[a], &self->value[mid]);
    long z = a;
    for(long i = a + 1; i <= b; i++)
        if(_compare(&self->value[a], &self->value[i]))
        {
            z++;
            SWAP(T, &self->value[z], &self->value[i]);
        }
    SWAP(T, &self->value[a], &self->value[z]);
    if (z)
        JOIN(A, _ranged_sort)(self, a, z - 1, _compare);
    JOIN(A, _ranged_sort)(self, z + 1, b, _compare);
}

static inline void
JOIN(A, sort)(A* self)
{
    CTL_ASSERT_COMPARE
    if (self->size)
        JOIN(A, _ranged_sort)(self, 0, self->size - 1, self->compare);
//#ifdef CTL_STR
//    self->value[self->size] = '\0';
//#endif
}

static inline A
JOIN(A, copy)(A* self)
{
    A other = JOIN(A, _init)(self);
    JOIN(A, reserve)(&other, self->size); // i.e shrink to fit
    while(other.size < self->size)
        JOIN(A, push_back)(&other, other.copy(&self->value[other.size]));
    return other;
}

static inline size_t
JOIN(A, remove_if)(A* self, int (*_match)(T*))
{
    size_t erases = 0;
    foreach(A, self, it)
    {
        if(_match(it.ref))
        {
            size_t index = it.ref - JOIN(A, begin)(self);
            JOIN(A, erase)(self, index);
            it.end = JOIN(A, end)(self);
            it.next = it.ref;
            erases++;
        }
    }
    return erases;
}

#ifndef CTL_STR
static inline T*
JOIN(A, find)(A* self, T key)
{
    foreach(A, self, it)
        if (JOIN(A, _equal)(self, it.ref, &key))
            return it.ref;
    return NULL;
}
#endif

#if defined(CTL_STR) || \
    defined(CTL_U8STR)
# include <ctl/algorithm.h>
#endif

#undef A
#undef I
#undef MUST_ALIGN_16
#undef INIT_SIZE

// Hold preserves `T` if other containers
// (eg. `priority_queue.h`) wish to extend `vector.h`.
#ifdef HOLD
#undef HOLD
#else
#undef T
#undef POD
#undef NOT_INTEGRAL
#endif
#undef CTL_VEC
