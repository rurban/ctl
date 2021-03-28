/* vector kept sorted on insertion.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/sorted_vector.h>"
#endif

#define CTL_SVEC
#define HOLD
#define vec svec
//#define _vec _svec
// undefined:
#define set            __SET
#define push_back      __PUSH_BACK
#define push_front     __PUSH_FRONT
#define emplace_back   __EMPLACE_BACK
#define sort           __SORT
// replaced:
#define insert         __INSERT
#define erase          __ERASE
#define emplace        __EMPLACE
#define assign_range   __ASSIGN_RANGE
#define assign_generic __ASSIGN_GENERIC
#define copy           __COPY

#include <ctl/vector.h>

#undef vec
#undef _vec
#undef set
#undef push_back
#undef push_front
#undef emplace_back
#undef sort
#undef insert
#undef erase
#undef emplace
#undef assign_range
#undef assign_generic

#define A JOIN(svec, T)

// FIXME sorted
static inline void JOIN(A, emplace)(I *pos, T *value)
{
    A *self = pos->container;
    if (!JOIN(I, done)(pos))
    {
        size_t index = pos->ref - self->vector;
        //JOIN(A, emplace_back)(self, JOIN(A, back)(self));
        for (size_t i = self->size - 2; i > index; i--)
            self->vector[i] = self->vector[i - 1];
        self->vector[index] = *value;
    }
    else
        JOIN(A, emplace_back)(self, value);
}

// FIXME sorted
static inline void JOIN(A, assign_range)(A *self, T *from, T *last)
{
    size_t i = 0;
    const size_t orig_size = self->size;
    assert(last >= from);
    while(from != last)
    {
        if (i >= orig_size) // grow
            JOIN(A, push_back)(self, self->copy(from));
        else
        {
            T *ref = &self->vector[i];
            if (self->free && i < orig_size)
                self->free(ref);
            *ref = self->copy(from);
        }
        from++;
        i++;
    }
    if (i < orig_size) // shrink
        while (i != self->size)
            JOIN(A, pop_back)(self);
}

// FIXME sorted
static inline void JOIN(A, assign_generic)(A *self, GI *range)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;
    size_t i = 0;
    const size_t orig_size = self->size;
    while(!done(range))
    {
        if (i >= orig_size) // grow
            JOIN(A, push_back)(self, self->copy(ref(range)));
        else
        {
            T *sref = &self->vector[i];
            if (self->free && i < orig_size)
                self->free(sref); // replace
            *sref = self->copy(ref(range));
        }
        next(range);
        i++;
    }
    if (i < orig_size) // shrink
        while (i != self->size)
            JOIN(A, pop_back)(self);
}

static inline void JOIN(A, insert_index)(A *self, size_t index, T value)
{
    if (self->size > 0)
    {
        JOIN(A, push_back)(self, *JOIN(A, back)(self));
        // TODO memmove with POD
        for (size_t i = self->size - 2; i > index; i--)
            self->vector[i] = self->vector[i - 1];
        self->vector[index] = value;
    }
    else
        JOIN(A, push_back)(self, value);
}

static inline I JOIN(A, erase_index)(A *self, size_t index)
{
    static T zero;
#if 1
    if (self->free)
        self->free(&self->vector[index]);
    if (index < self->size - 1)
        memmove(&self->vector[index], &self->vector[index] + 1, (self->size - index - 1) * sizeof(T));
    self->vector[self->size - 1] = zero;
#else
    JOIN(A, set)(self, index, zero);
    for (size_t i = index; i < self->size - 1; i++)
    {
        self->vector[i] = self->vector[i + 1];
        self->vector[i + 1] = zero;
    }
#endif
    self->size--;
    return JOIN(I, iter)(self, index);
}

static inline I *JOIN(A, erase_range)(I *range)
{
    if (JOIN(I, done)(range))
        return range;
    A *self = range->container;
    T *end = &self->vector[self->size];
#if 1
    size_t size = (range->end - range->ref);
#ifndef POD
    if (self->free)
        for (T *ref = range->ref; ref < range->end; ref++)
            self->free(ref);
#endif
    if (range->end != end)
        memmove(range->ref, range->end, (end - range->end) * sizeof(T));
    memset(end - size, 0, size * sizeof(T)); // clear the slack?
    // range->end = range->ref;
    self->size -= size;
#else
    static T zero;
    *range->ref = zero;
    T *pos = range->ref;
    for (; pos < range->end - 1; pos++)
    {
        *pos = *(pos + 1);
        *(pos + 1) = zero;
        self->size--;
    }
    self->size--;
    if (range->end < end)
        *pos = *(pos + 1);
#endif
    return range;
}

static inline void JOIN(A, insert)(A *self, T value)
{
    // TODO binary_search pos
    {
    size_t index = pos->ref - self->vector;
    size_t end = pos->end - self->vector;
    // TODO memmove with POD
    JOIN(A, push_back)(self, *JOIN(A, back)(self));
    for (size_t i = self->size - 2; i > index; i--)
        self->vector[i] = self->vector[i - 1];
    self->vector[index] = value;
    pos->ref = &self->vector[index];
    pos->end = &self->vector[end];
    }
    else
    {
        // or at end
        JOIN(A, push_back)(self, value);
        pos->end = pos->ref = &self->vector[self->size];
    }
}

static inline void JOIN(A, insert_count)(A *self, size_t count, T value)
{
    // TODO binary_search pos
    size_t index = pos->ref - self->vector;
    JOIN(A, reserve)(self, self->size + count);
    if (!JOIN(I, done)(pos))
    {
        for (size_t i = 0; i < count; i++)
            JOIN(A, insert_index)(self, index++, self->copy(&value));
    }
    else
    {
        for (size_t i = 0; i < count; i++)
            JOIN(A, push_back)(self, self->copy(&value));
    }
#if defined CTL_STR
    JOIN(A, reserve)(self, self->size);
#endif
    if (self->free)
        self->free(&value);
}

static inline void JOIN(A, insert_range)(A *self, I *range2)
{
    // TODO binary_search pos
    size_t index = pos->ref - self->vector;
    size_t f2 = range2->ref - range2->container->vector;
    size_t l2 = range2->end - range2->container->vector;
    // only if not overlapping, and resize does no realloc
    if (f2 < l2)
    {
        JOIN(A, reserve)(self, self->size + (l2 - f2));
        if (self == range2->container)
        {
            range2->ref = &range2->container->vector[f2];
            range2->end = &range2->container->vector[l2];
        }
    }
    if (!JOIN(I, done)(pos))
    {
        foreach_range_(A, it, range2) if (it.ref) JOIN(A, insert_index)(self, index++, self->copy(it.ref));
    }
    else
    {
        foreach_range_(A, it, range2) if (it.ref) JOIN(A, push_back)(self, self->copy(it.ref));
    }
#if defined CTL_STR
    JOIN(A, reserve)(self, self->size);
#endif
}

static inline I JOIN(A, erase)(A* self, T value)
{
    // TODO binary_search pos
    return JOIN(A, erase_index)(self, JOIN(I, index)(pos));
}

static inline void JOIN(A, insert_generic)(A* self, GI *range)
{
    // TODO binary_search pos
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;

    // JOIN(A, reserve)(self, self->size + JOIN(GI, distance_range)(range));
    size_t index = JOIN(I, index)(pos);
    while (!done(range))
    {
        JOIN(A, insert)(pos, self->copy(ref(range)));
        pos->ref = &self->vector[++index];
        next(range);
    }
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

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init_from)(self);
    JOIN(A, reserve)(&other, self->size);
    memcpy(other.vector, self->vector, self->size * sizeof(T));
    return other;
}

static inline I JOIN(A, find)(A *self, T key)
{
    // FIXME binary_search
    //vec_foreach(T, self, ref)
    // if (JOIN(A, _equal)(self, ref, &key))
    //   return JOIN(I, iter)(self, ref - &self->vector[0]);
    return JOIN(A, end(self));
}

// move elements from range to the end of out.
// different to C++ where the deletion is skipped.
// the STL does no move, just does assignment. (like our at)
static inline A *JOIN(A, move_range)(I *range, A *out)
{
    static T zero;
    A *self = range->container;
    T *ref = range->ref;
    while (ref != range->end)
    {
        JOIN(A, push_back)(out, *ref);
        // erase without free
        size_t index = ref - &self->vector[0];
        memmove(ref, ref + 1, (self->size - index - 1) * sizeof(T));
        self->vector[self->size - 1] = zero;
        self->size--;
        ref++;
    }
    return out;
}

#ifdef INCLUDE_ALGORITHM
#include <ctl/algorithm.h>
#endif

#undef INCLUDE_ALGORITHM
#undef A
#undef I
#undef T
#undef POD
#undef NOT_INTEGRAL
#undef MUST_ALIGN_16
#undef INIT_SIZE
#undef CTL_SVEC
