// Optional generic algorithms
// requested via #define INCLUDE_ALGORITHM before loading the container
// SPDX-License-Identifier: MIT
//
// Might only be included once. By the child. not the parent.
//#ifndef __CTL_ALGORITHM_H__
//#define __CTL_ALGORITHM_H__

// clang-format off
#if !defined CTL_LIST && \
    !defined CTL_SLIST && \
    !defined CTL_SET && \
    !defined CTL_USET && \
    !defined CTL_VEC && \
    !defined CTL_ARR && \
    !defined CTL_DEQ && \
    /* plus all children also. we don't include it for parents */ \
    !defined CTL_STACK && \
    !defined CTL_QUEUE && \
    !defined CTL_PQU && \
    !defined CTL_STR && \
    !defined CTL_U8STR && \
    !defined CTL_HMAP && \
    !defined CTL_MAP && \
    !defined CTL_UMAP
# error "No CTL container defined for <ctl/algorithm.h>"
#endif
// clang-format on
#undef CTL_ALGORITHM
#define CTL_ALGORITHM

// Generic algorithms with ranges

static inline I JOIN(A, find_if)(A *self, int _match(T *))
{
    foreach (A, self, i)
        if (_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline I JOIN(A, find_if_not)(A *self, int _match(T *))
{
    foreach (A, self, i)
        if (!_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline bool JOIN(A, all_of)(A *self, int _match(T *))
{
    I pos = JOIN(A, find_if_not)(self, _match);
    return JOIN(I, done)(&pos);
}

// C++11
static inline bool JOIN(A, any_of)(A *self, int _match(T *))
{
    I pos = JOIN(A, find_if)(self, _match);
    return !JOIN(I, done)(&pos);
}

static inline bool JOIN(A, none_of)(A *self, int _match(T *))
{
    I pos = JOIN(A, find_if)(self, _match);
    return JOIN(I, done)(&pos);
}

#include <stdbool.h>

#if !defined CTL_USET && !defined CTL_SET

static inline bool JOIN(A, find_range)(I *range, T value)
{
    A *self = range->container;
    foreach_range_(A, i, range)
    {
        if (JOIN(A, _equal)(self, i.ref, &value))
        {
            *range = i;
            return true;
        }
    }
    JOIN(I, set_done)(range);
    return false;
}

#endif // USET, SET
#if !defined CTL_USET

static inline I JOIN(A, find_if_range)(I *range, int _match(T *))
{
    foreach_range_(A, i, range)
    {
        if (_match(i.ref))
            return i;
    }
    JOIN(I, set_done)(range);
    return *range;
}

static inline I JOIN(A, find_if_not_range)(I *range, int _match(T *))
{
    foreach_range_(A, i, range)
    {
        if (!_match(i.ref))
            return i;
    }
    JOIN(I, set_done)(range);
    return *range;
}

// C++20
static inline bool JOIN(A, all_of_range)(I *range, int _match(T *))
{
    I pos = JOIN(A, find_if_not_range)(range, _match);
    if (JOIN(I, done)(range))
        return true;
    return JOIN(I, done)(&pos);
}
// C++20
static inline bool JOIN(A, none_of_range)(I *range, int _match(T *))
{
    I pos = JOIN(A, find_if_range)(range, _match);
    if (JOIN(I, done)(range))
        return true;
    return JOIN(I, done)(&pos);
}
// C++20
static inline bool JOIN(A, any_of_range)(I *range, int _match(T *))
{
    return !JOIN(A, none_of_range)(range, _match);
}

#endif // USET (ranges)

static inline void JOIN(I, iter_swap)(I *a, I* b)
{
    //TODO: for integer literals we would need no temporaries
    T tmp = *JOIN(I, ref)(a);
    *JOIN(I, ref)(a) = *JOIN(I, ref)(b);
    *JOIN(I, ref)(b) = tmp;
}

#if !defined(CTL_ARR)
#if !(defined CTL_USET || defined CTL_UMAP)

// default inserter (add at front, back or middle)
static inline void JOIN(A, inserter)(A *self, T value)
{
#if defined CTL_LIST || defined CTL_VEC || defined CTL_ARR || defined CTL_DEQ
    JOIN(A, push_back)(self, value);
#elif defined CTL_SET || defined CTL_MAP
    // USET natively
    JOIN(A, insert)(self, value);
#elif defined CTL_SLIST
    JOIN(A, push_front)(self, value);
#elif defined CTL_PQU || defined CTL_STACK || defined CTL_QUEUE
    JOIN(A, push)(self, value);
#else
    #error "undefined container"
#endif
}
#endif // USET/UMAP have their own outside of algorithm

#if !defined CTL_SLIST
// slist needs to do some reversing
static inline A *JOIN(A, copy_range)(GI *range, A *out)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;
    while (!done(range))
    {
        JOIN(A, inserter)(out, out->copy(ref(range)));
        next(range);
    }
    return out;
}
#endif // SLIST
#endif // ARR

#if defined(CTL_LIST) || defined(CTL_VEC) || defined(CTL_STR) || defined(CTL_DEQ)
// set/uset have optimized implementations.

static inline int JOIN(A, _found)(A *a, T *ref)
{
#ifdef CTL_STR
    return strchr(a->vector, *ref) ? 1 : 0;
#else
    JOIN(A, it) iter = JOIN(A, find)(a, *ref);
    return !JOIN(I, done)(&iter);
#endif
}

/* These require sorted containers via operator< and push_back. */

/*
static inline A
JOIN(A, union)(A* a, A* b)
{
    A self = JOIN(A, init_from)(a);
    JOIN(A, it) it1 = JOIN(A, begin)(a);
    JOIN(A, it) it2 = JOIN(A, begin)(b);
    while(!JOIN(I, done)(&it1))
    {
        if (JOIN(I, done)(&it2))
            return *JOIN(A, copy_range)(&it1, &self);
        if (self.compare(it2.ref, it1.ref))
        {
            JOIN(A, inserter)(&self, self.copy(it2.ref));
            JOIN(I, next)(&it2);
        }
        else
        {
            JOIN(A, inserter)(&self, self.copy(it1.ref));
            if (!self.compare(it1.ref, it2.ref))
                JOIN(I, next)(&it2);
            JOIN(I, next)(&it1);
        }
    }
    return *JOIN(A, copy_range)(&it2, &self);
}
*/

static inline A JOIN(A, union_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;
 
    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
            return *JOIN(A, copy_range)(r1, &self);
        if (self.compare(ref2(r2), r1->ref))
        {
            JOIN(A, inserter)(&self, self.copy(ref2(r2)));
            next2(r2);
        }
        else
        {
            JOIN(A, inserter)(&self, self.copy(r1->ref));
            if (!self.compare(r1->ref, ref2(r2)))
                next2(r2);
            JOIN(I, next)(r1);
        }
    }
    JOIN(A, copy_range)(r2, &self);
#if defined CTL_STR
    // JOIN(A, reserve)(&self, self.size);
#endif
    return self;
}

static inline A JOIN(A, union)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, union_range)(&r1, &r2);
}

// FIXME str
static inline A JOIN(A, intersection_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!JOIN(I, done)(r1) && !done2(r2))
    {
        if (self.compare(r1->ref, ref2(r2)))
            JOIN(I, next)(r1);
        else
        {
            if (!self.compare(ref2(r2), r1->ref))
            {
                JOIN(A, inserter)(&self, self.copy(r1->ref));
                JOIN(I, next)(r1);
            }
            next2(r2);
        }
    }
#if defined CTL_STR
    // JOIN(A, reserve)(&self, self.size);
#elif defined CTL_VEC
    JOIN(A, shrink_to_fit)(&self);
#endif
    return self;
}

static inline A JOIN(A, intersection)(A *a, A *b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it)
        if(JOIN(A, _found)(b, it.ref))
            JOIN(A, inserter)(&self, self.copy(it.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, intersection_range)(&r1, &r2);
#endif
}
#endif // LIST, VEC, STR, DEQ

#if !defined(CTL_ARR) && !defined(CTL_USET) && !defined(CTL_SLIST)

// Warning: fails with 3-way compare! And with generic r2 also.
static inline A JOIN(A, difference_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
            return *JOIN(A, copy_range)(r1, &self);
        // r1 < r2 (fails with 3-way compare)
        if (self.compare(r1->ref, ref2(r2)))
        {
            JOIN(A, inserter)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (!self.compare(ref2(r2), r1->ref))
                JOIN(I, next)(r1);
            next2(r2);
        }
    }
    return self;
}

static inline A JOIN(A, symmetric_difference_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
            return *JOIN(A, copy_range)(r1, &self);

        if (self.compare(r1->ref, ref2(r2)))
        {
            JOIN(A, inserter)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (self.compare(ref2(r2), r1->ref))
                JOIN(A, inserter)(&self, self.copy(ref2(r2)));
            else
                JOIN(I, next)(r1);
            next2(r2);
        }
    }
    JOIN(A, copy_range)(r2, &self);
#if defined CTL_STR
    // JOIN(A, reserve)(&self, self.size);
#endif
    return self;
}
#endif // !ARR, USET, SLIST

#if defined(CTL_LIST) || defined(CTL_VEC) || defined(CTL_STR) || defined(CTL_DEQ)
static inline A JOIN(A, difference)(A *a, A *b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it)
        if(!JOIN(A, _found)(b, it.ref))
            JOIN(A, inserter)(&self, self.copy(it.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, difference_range)(&r1, &r2);
#endif
}
static inline A JOIN(A, symmetric_difference)(A *a, A *b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it1)
        if(!JOIN(A, _found)(b, it1.ref))
            JOIN(A, inserter)(&self, self.copy(it1.ref));
    foreach(A, b, it2)
        if(!JOIN(A, _found)(a, it2.ref))
            JOIN(A, inserter)(&self, self.copy(it2.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, symmetric_difference_range)(&r1, &r2);
#endif
}

#endif // LIST, VEC, STR, DEQ
#if !defined CTL_USET

static inline bool JOIN(A, includes_range)(I *r1, GI *r2)
{
    A *self = r1->container;
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!done2(r2))
    {
        if (JOIN(I, done)(r1) || self->compare(ref2(r2), r1->ref))
            return false;
        if (!self->compare(r1->ref, ref2(r2)))
            next2(r2);
        JOIN(I, next)(r1);
    }
    return true;
}

static inline bool JOIN(A, includes)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, includes_range)(&r1, &r2);
}
#else // !USET
static inline bool JOIN(A, is_sorted)(I *range)
{
    (void)range;
    return false;
}
static inline I* JOIN(A, is_sorted_until)(I *first, I *last)
{
    (void)last;
    return first;
}
#endif // USET

#ifdef CTL_SET
static inline bool JOIN(A, is_sorted)(I *range)
{
    (void)range;
    return true;
}
static inline I* JOIN(A, is_sorted_until)(I *first, I *last)
{
    (void)first;
    return last;
}
#endif

// generate and transform have no inserter support yet,
// so we cannot yet use it for set nor uset. we want to call inserter/push_back on them.
// for list and vector we just set/replace the elements.
#if !defined(CTL_USET) && !defined(CTL_SET)

// not as range, just normal iters, ignoring their end
static inline I* JOIN(A, is_sorted_until)(I *first, I *last)
{
    A* self = first->container;
    JOIN(I, set_end)(first, last);
    if (!JOIN(I, done)(first)) {
        I next = *first;
        JOIN(I, next)(&next);
        while (!JOIN(I, done)(&next)) {
            if (self->compare(next.ref, first->ref))
            {
                *first = next;
                return first;
            }
            JOIN(I, next)(first);
            JOIN(I, next)(&next);
        }
    }
    JOIN(I, set_end)(last, last); // moves last->end to pos, so it's done
    return last;
}

static inline bool JOIN(A, is_sorted)(I *range)
{
    I end = *range;
    JOIN(I, set_done)(&end);
    return JOIN(I, done)(JOIN(A, is_sorted_until)(range, &end));
}

static inline void JOIN(A, generate)(A *self, T _gen(void))
{
    foreach (A, self, i)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

static inline void JOIN(A, generate_range)(I *range, T _gen(void))
{
#ifndef POD
    A *self = range->container;
#endif
    foreach_range_(A, i, range)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

static inline A JOIN(A, transform)(A *self, T _unop(T *))
{
    A other = JOIN(A, copy)(self);
    foreach (A, &other, i)
    {
#ifndef POD
        T tmp = _unop(i.ref);
        if (self->free)
            self->free(i.ref);
        *i.ref = tmp;
#else
        *i.ref = _unop(i.ref);
#endif
    }
    return other;
}

#if !defined(CTL_ARR) && !defined(CTL_SLIST)
static inline A JOIN(A, transform_it)(A *self, I *pos, T _binop(T *, T *))
{
    A other = JOIN(A, init_from)(self);
#ifdef CTL_VEC
    if (self->size > 1)
        JOIN(A, fit)(&other, self->size - 1);
#endif
    foreach (A, self, i)
    {
        if (JOIN(I, done)(pos))
            break;
        T tmp = _binop(i.ref, pos->ref);
        JOIN(A, inserter)(&other, tmp);
        JOIN(I, next)(pos);
    }
#if defined(CTL_VEC) && !defined(CTL_STR)
    JOIN(A, shrink_to_fit)(&other);
#endif
    return other;
}
#endif // ARR,SLIST

// std::deque has a different idea
static inline void JOIN(A, generate_n)(A *self, size_t count, T _gen(void))
{
    foreach_n(A, self, i, count)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

// And here std::deque is a travesty. Or right.
static inline void JOIN(A, generate_n_range)(I *first, size_t count, T _gen(void))
{
#ifndef POD
    A *self = first->container;
#endif
    foreach_n_range(A, first, i, count)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

// not inserted, dest container with size must exist
static inline I JOIN(A, transform_range)(I *range, I dest, T _unop(T *))
{
    foreach_range_(A, i, range)
    {
        if (JOIN(I, done)(&dest))
            break;
#ifndef POD
        if (dest.container->free)
            dest.container->free(dest.ref);
#endif
        *dest.ref = _unop(i.ref);
        JOIN(I, next)(&dest);
    }
    return dest;
}

// not inserted, dest container with size must exist
static inline I JOIN(A, transform_it_range)(I *range, I *pos, I dest, T _binop(T *, T *))
{
    foreach_range_(A, i, range)
    {
        if (JOIN(I, done)(pos) || JOIN(I, done)(&dest))
            break;
#ifndef POD
        if (dest.container->free)
            dest.container->free(dest.ref);
#endif
        *dest.ref = _binop(i.ref, pos->ref);
        JOIN(JOIN(A, it), next)(pos);
        JOIN(JOIN(A, it), next)(&dest);
    }
    return dest;
}

#if defined CTL_ARR || defined CTL_VEC || defined CTL_DEQ

static inline void JOIN(A, shuffle)(A *self)
{
    size_t n = JOIN(A, size)(self);
    if (n < 2)
        return;
    for (size_t i = n-1; i > 0; i--)
    {
        int r = rand() % (i+1);
        T tmp = *JOIN(A, at)(self, i);
        *JOIN(A, at)(self, i) = *JOIN(A, at)(self, r);
        *JOIN(A, at)(self, r) = tmp;
    }
}

static inline void JOIN(A, shuffle_range)(I *range)
{
    A* self = range->container;
    if (JOIN(I, done)(range))
        return;
    const size_t b = JOIN(I, index)(range);
    const size_t e = b + JOIN(I, distance_range)(range);
    for (size_t i = e-1; i > b; i--)
    {
        int r = b + (rand() % ((i-b)+1));
        T tmp = *JOIN(A, at)(self, i);
        *JOIN(A, at)(self, i) = *JOIN(A, at)(self, r);
        *JOIN(A, at)(self, r) = tmp;
    }
}
#endif // with at

#endif // USET,SET

#if !defined(CTL_ARR)

#if !defined(CTL_USET) && !defined(CTL_UMAP) && !defined(CTL_SLIST)
// both are better be sorted
static inline A JOIN(A, merge_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
            return *JOIN(A, copy_range)(r1, &self);
        if (self.compare(ref2(r2), r1->ref))
        {
            JOIN(A, inserter)(&self, self.copy(ref2(r2)));
            next2(r2);
        }
        else
        {
            JOIN(A, inserter)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
    }
    JOIN(A, copy_range)(r2, &self);
    return self;
}

#if !defined(CTL_LIST)
static inline A JOIN(A, merge)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, merge_range)(&r1, &r2);
}
#endif // LIST
#endif // USET,SLIST

#if 0
// TODO
static inline A* JOIN(A, inplace_merge)(I *first, I *middle, I *last)
{
    //A* self = first->container;
    if (JOIN(I, index)(first) == JOIN(I, index)(middle) ||
        JOIN(I, index)(middle) == JOIN(I, index)(last))
        return;
    size_t len1 = JOIN(I, distance)(first, middle);
    size_t len2 = JOIN(I, distance)(middle, last);
    /* TODO */
    if (JOIN(I, index)(first) == 0)
    {
    }
    else
    {
    }
    return NULL;
}
#endif

static inline A JOIN(A, copy_if_range)(I *range, int _match(T*))
{
    A out = JOIN(A, init_from)(range->container);
    while (!JOIN(I, done)(range))
    {
        if (_match(range->ref))
            JOIN(A, inserter)(&out, out.copy(range->ref));
        JOIN(I, next)(range);
    }
    return out;
}

static inline A JOIN(A, copy_if)(A *self, int _match(T*))
{
    A out = JOIN(A, init_from)(self);
    I range = JOIN(A, begin)(self);
    while (!JOIN(I, done)(&range))
    {
        if (_match(range.ref))
            JOIN(A, inserter)(&out, out.copy(range.ref));
        JOIN(I, next)(&range);
    }
    return out;
}
#endif // ARR

#if !defined(CTL_USET)
/// uset has cached_hash optims
static inline size_t JOIN(A, count_range)(I *range, T value)
{
    A *self = range->container;
    size_t count = 0;
    foreach_range_(A, i, range) if (JOIN(A, _equal)(self, i.ref, &value)) count++;
    if (self->free)
        self->free(&value);
    return count;
}
#if !defined(CTL_SET) && !defined(CTL_STR)
// str has its own variant via faster find. set/uset do not need it.
static inline size_t JOIN(A, count)(A *self, T value)
{
    size_t count = 0;
    foreach (A, self, i)
        if (JOIN(A, _equal)(self, i.ref, &value))
            count++;
    if (self->free)
        self->free(&value);
    return count;
}
#endif // SET/STR

static inline bool JOIN(A, mismatch)(I *range1, GI *range2)
{
    A *self = range1->container;
    CTL_ASSERT_EQUAL
    void (*next2)(struct I*) = range2->vtable.next;
    T* (*ref2)(struct I*) = range2->vtable.ref;
    int (*done2)(struct I*) = range2->vtable.done;

    int done1 = JOIN(I, done)(range1);
    if (!done2(range2))
        while (!done1 && JOIN(A, _equal)(self, range1->ref, ref2(range2)))
        {
            JOIN(I, next)(range1);
            next2(range2);
            done1 = JOIN(I, done)(range1);
            if (done2(range2))
            {
                done1 = 1;
                break;
            }
        }
    return done1 ? false : true;
}

static inline bool JOIN(A, lexicographical_compare)(I *range1, GI *range2)
{
    A *self = range1->container;
    CTL_ASSERT_COMPARE
    void (*next2)(struct I*) = range2->vtable.next;
    T* (*ref2)(struct I*) = range2->vtable.ref;
    int (*done2)(struct I*) = range2->vtable.done;

    for ( ; !JOIN(I, done)(range1) && !done2(range2); JOIN(I, next)(range1), next2(range2)) {
        if (self->compare(range1->ref, ref2(range2))) return true;
        if (self->compare(ref2(range2), range1->ref)) return false;
    }
    return JOIN(I, done)(range1) && !done2(range2);
}

#if 0
static inline int (*compare)(T *, T *)
JOIN(A, lexicographical_compare_three_way)(I *range1, GI *range2, int (*compare)(T *, T *))
{
    void (*next2)(struct I *) = range2->vtable.next;
    T *(*ref2)(struct I *) = range2->vtable.ref;
    int (*done2)(struct I *) = range2->vtable.done;

    for (; !JOIN(I, done)(range1) && !done2(range2); JOIN(I, next)(range1), next2(range2))
    {
        int cmp = compare(range1->ref, ref2(range2));
        if (cmp != 0)
            return cmp;
    }
    return !JOIN(I, done)(range1) ? !compare(range1->ref, ref2(range2))
                                  : !done2(range2) ? compare(range1->ref, ref2(range2)) : 0;
}
#endif

#endif // USET

//#if !defined(CTL_STR)
// C++20
static inline size_t JOIN(A, count_if_range)(I *range, int _match(T *))
{
    size_t count = 0;
    foreach_range_(A, i, range)
    {
        if (_match(i.ref))
            count++;
    }
    return count;
}

static inline size_t JOIN(A, count_if)(A *self, int _match(T *))
{
    size_t count = 0;
    foreach (A, self, i)
    {
        if (_match(i.ref))
            count++;
    }
    return count;
}
//#endif // STR

#if !defined CTL_STR && !defined CTL_SET

// i.e. like strcspn, but returning the first found match
// has better variants for STR and SET
static inline bool JOIN(A, find_first_of_range)(I *range1, GI *range2)
{
    void (*next2)(struct I*) = range2->vtable.next;
    T* (*ref2)(struct I*) = range2->vtable.ref;
    int (*done2)(struct I*) = range2->vtable.done;

    if (JOIN(I, done)(range1) || done2(range2))
        return false;
    A *self = range1->container;
    // TODO: sort range2 and binary_search
    while (1)
    {
        // TODO unroll it into slices of 4, as strcspn does
        for (I it = *range2; !done2(&it); next2(&it))
        {
            if (JOIN(A, _equal)(self, range1->ref, ref2(&it)))
                return true;
        }
        JOIN(I, next)(range1);
        if (JOIN(I, done)(range1))
            break;
    }
    JOIN(I, set_done)(range1);
    return false;
}
#endif // STR,SET

#ifndef CTL_STR
static inline I JOIN(A, find_first_of)(A *self, GI *range2)
{
    I begin = JOIN(A, begin)(self);
    if (JOIN(A, find_first_of_range)(&begin, range2))
        return begin;
    else
        return JOIN(A, end)(self);
}
#endif // STR

// Sets range1 (the haystack) to the found pointer if found.
// Naive r1*r2 cost, no Boyer-Moore yet.
static inline bool JOIN(A, search_range)(I *range1, GI *range2)
{
    T* (*ref2)(struct I*) = range2->vtable.ref;
    int (*done2)(struct I*) = range2->vtable.done;

    if (JOIN(I, done)(range1))
        return false;
    if (done2(range2))
        return true;
#ifdef CTL_STR
    // Note: strstr is easily beatable. See
    // http://0x80.pl/articles/simd-strfind.html
    if ((range1->ref = strstr(range1->ref, ref2(range2)))
        && range1->ref < range1->end)
    {
        return true;
    }
    else
    {
        range1->ref = range1->end;
        return false;
    }
#else
    A *self = range1->container;
    void (*next2)(struct I*) = range2->vtable.next;
    for (;; JOIN(I, next)(range1))
    {
        I it = *range1;
        I s_it = *range2;
        for (;;)
        {
            if (done2(&s_it))
                return true;
            if (JOIN(I, done)(&it))
            {
                *range1 = it;
                return false;
            }
            if (!JOIN(A, _equal)(self, it.ref, ref2(&s_it)))
                break;
            JOIN(I, next)(&it);
            next2(&s_it);
        }
    }
    return false;
#endif
}

// Returns iterator to the found pointer or end
static inline I JOIN(A, search)(A *self, I *subseq)
{
    I begin = JOIN(A, begin)(self);
    if (JOIN(A, search_range)(&begin, subseq))
        return begin;
    else
        return JOIN(A, end)(self);
}

static inline I JOIN(A, find_end_range)(I *range1, GI *range2)
{
    if (range2->vtable.done(range2) || JOIN(I, done)(range1))
    {
        JOIN(I, set_done)(range1);
        return *range1;
    }
    I result = *range1;
    JOIN(I, set_done)(&result);
    while (1)
    {
        if (JOIN(A, search_range)(range1, range2))
        {
            result = *range1;
            JOIN(I, next)(range1);
        }
        else
            break;
    }
    return result;
}

static inline I JOIN(A, find_end)(A *self, I *s_range)
{
    I begin = JOIN(A, begin)(self);
    if (JOIN(I, done)(s_range))
    {
        JOIN(I, set_done)(&begin);
        return begin;
    }
    if (JOIN(A, search_range)(&begin, s_range))
        return begin;
    else
        return JOIN(A, end)(self);
}

static inline I *JOIN(A, search_n_range)(I *range, size_t count, T value)
{
    A *self = range->container;
    if (JOIN(I, done)(range) || !count)
    {
        if (self->free)
            self->free(&value);
        return range;
    }
    for (; !JOIN(I, done)(range); JOIN(I, next)(range))
    {
        if (!JOIN(A, _equal)(self, range->ref, &value))
            continue;
        I it = *range;
        size_t i = 0;
        while (1)
        {
            if (++i >= count)
            {
                if (self->free)
                    self->free(&value);
                *range = it;
                return range;
            }
            JOIN(I, next)(range);
            if (JOIN(I, done)(range))
            {
                if (self->free)
                    self->free(&value);
                return range;
            }
            if (!JOIN(A, _equal)(self, range->ref, &value))
                break;
        }
    }
    if (self->free)
        self->free(&value);
    return range;
}

static inline I JOIN(A, search_n)(A *self, size_t count, T value)
{

    if (JOIN(A, size)(self) < count)
    {
        if (self->free)
            self->free(&value);
        return count ? JOIN(A, end)(self) : JOIN(A, begin)(self);
    }
    I range = JOIN(A, begin)(self);
    return *JOIN(A, search_n_range)(&range, count, value);
}

static inline I *JOIN(A, adjacent_find_range)(I *range)
{

    if (JOIN(I, done)(range))
        return range;
    A *self = range->container;
    I next = *range;
    JOIN(I, next)(&next);
    for (; !JOIN(I, done)(&next); *range = next, JOIN(I, next)(&next))
    {
        if (JOIN(A, _equal)(self, range->ref, next.ref))
            return range;
    }
    *range = next;
    return range;
}

static inline I JOIN(A, adjacent_find)(A *self)
{

    if (JOIN(A, size)(self) < 2)
        return JOIN(A, end)(self);
    I range = JOIN(A, begin)(self);
    return *JOIN(A, adjacent_find_range)(&range);
}

#if !defined CTL_USET

// if all values in the range are the same as value
static inline bool JOIN(A, equal_value)(I *range, T value)
{
    bool result = !JOIN(I, done)(range);
    A *self = range->container;
    foreach_range_(A, i, range)
    {
        if (!JOIN(A, _equal)(self, i.ref, &value))
        {
            result = false;
            break;
        }
    }
    if (self && self->free)
        self->free(&value);
    return result;
}
#endif // USET

#if !defined CTL_USET && !defined CTL_SET

// Note: set.equal_range does interval search for key, returning the
// lower_bound/upper_bound pair.

static inline bool JOIN(A, equal_range)(I *range1, GI *range2)
{
    A *self = range1->container;
    CTL_ASSERT_EQUAL
    void (*next2)(struct I*) = range2->vtable.next;
    T* (*ref2)(struct I*) = range2->vtable.ref;
    int (*done2)(struct I*) = range2->vtable.done;

    while (!JOIN(I, done)(range1))
    {
        if (done2(range2) || !JOIN(A, _equal)(self, range1->ref, ref2(range2)))
            return false;
        JOIN(I, next)(range1);
        next2(range2);
    }
    return done2(range2) ? true : false;
}

#endif // USET, SET

#ifndef CTL_USET

// Binary search operations (on sorted ranges)
// Slow on non-random access iters

static inline I *JOIN(A, lower_bound_range)(I *range, T value)
{
    A *self = range->container;
    CTL_ASSERT_COMPARE
    I it;
    size_t count = JOIN(I, distance_range)(range);
    while (count > 0)
    {
        size_t step = count / 2;
        it = *range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            *range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    if (self->free)
        self->free(&value);
    return range;
}

static inline I *JOIN(A, upper_bound_range)(I *range, T value)
{
    A *self = range->container;
    CTL_ASSERT_COMPARE
    I it;
    size_t count = JOIN(I, distance_range)(range);
    while (count > 0)
    {
        size_t step = count / 2;
        it = *range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (!self->compare(&value, it.ref))
        {
            JOIN(I, next)(&it);
            *range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    if (self->free)
        self->free(&value);
    return range;
}

static inline I JOIN(A, lower_bound)(A *self, T value)
{
    CTL_ASSERT_COMPARE
    I it = JOIN(A, begin)(self);
    I range = it;
    size_t count = JOIN(A, size)(self);
    while (count > 0)
    {
        size_t step = count / 2;
        it = range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    if (self->free)
        self->free(&value);
    return range;
}

static inline I JOIN(A, upper_bound)(A *self, T value)
{
    CTL_ASSERT_COMPARE
    I it = JOIN(A, begin)(self);
    I range = it;
    size_t count = JOIN(A, size)(self);
    while (count > 0)
    {
        size_t step = count / 2;
        it = range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (!self->compare(&value, it.ref))
        {
            JOIN(I, next)(&it);
            range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    if (self->free)
        self->free(&value);
    return range;
}

static inline bool JOIN(A, binary_search_range)(I *range, T value)
{
    A *self = range->container;
    size_t count = JOIN(I, distance_range)(range);
    if (!count)
    {
        if (self->free)
            self->free(&value);
        return false;
    }
    CTL_ASSERT_COMPARE
    bool result;
    I it;
    while (count > 0)
    {
        size_t step = count / 2;
        it = *range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            *range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    result = !JOIN(I, done)(range) && !self->compare(&value, range->ref);
    if (self->free)
        self->free(&value);
    return result;
}

static inline bool JOIN(A, binary_search)(A *self, T value)
{
    size_t count = JOIN(A, size)(self);
    if (!count)
    {
        if (self->free)
            self->free(&value);
        return false;
    }
    CTL_ASSERT_COMPARE
    bool result;
    I it = JOIN(A, begin)(self);
    I range = it;
    while (count > 0)
    {
        size_t step = count / 2;
        it = range;
        JOIN(I, advance)(&it, (long)step);
        // requires 2way compare
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            range = it;
            count -= step + 1;
        }
        else
            count = step;
    }
    result = !JOIN(I, done)(&range) && !self->compare(&value, range.ref);
    if (self->free)
        self->free(&value);
    return result;
}

#endif // USET

#ifdef CTL_SET

// set.equal_range does interval search for key, returning the
// lower_bound/upper_bound pair.
static inline void JOIN(A, equal_range)(A *self, T key, I *lower_bound, I *upper_bound)
{
    *lower_bound = JOIN(A, lower_bound)(self, self->copy(&key));
    *upper_bound = JOIN(A, upper_bound)(self, key);
}

#endif // SET

// uset, set don't need it.
#if !defined CTL_USET && !defined CTL_SET

// list has its own
#if defined CTL_VEC || defined CTL_DEQ
static inline I JOIN(A, unique_range)(I *range)
{
    if (JOIN(I, done)(range))
        return *range;
    I prev = *range;
    JOIN(I, next)(range);
    A *self = range->container;
    while (!JOIN(I, done)(range))
    {
        if (JOIN(A, _equal)(self, prev.ref, range->ref))
        {
            JOIN(A, erase)(range);
            range->end--;
        }
        else
        {
            JOIN(I, next)(range);
            JOIN(I, next)(&prev);
        }
    }
    return *range;
}
#elif !defined CTL_ARR
static inline I JOIN(A, unique_range)(I *range);
#endif // VEC, DEQ

// not sure yet about array. maybe with POD array.
#if !defined CTL_LIST && !defined CTL_SLIST && !defined CTL_ARR
static inline I JOIN(A, unique)(A *self)
{
    if (JOIN(A, size)(self) < 2)
        return JOIN(A, end)(self);
    I range = JOIN(A, begin)(self);
    return JOIN(A, unique_range)(&range);
}
#endif // LIST, SLIST, ARR

#if !defined(CTL_SLIST)
static inline void JOIN(A, reverse_range)(I *first)
{
    I last = *first;
    JOIN(I, set_done)(&last);
    while (!JOIN(I, done)(first))
    {
        JOIN(I, prev)(&last);
        if (JOIN(I, ref)(first) == JOIN(I, ref)(&last))
            break;
        JOIN(I, iter_swap)(first, &last);
        JOIN(I, next)(first);
        if (JOIN(I, ref)(first) == JOIN(I, ref)(&last))
            break;
    }
}

#if !defined(CTL_LIST)
// list has a specialized method
static inline void JOIN(A, reverse)(A *a)
{
    I first = JOIN(A, begin)(a);
    I last = JOIN(A, end)(a);
    while (JOIN(I, ref)(&first) != JOIN(I, ref)(&last))
    {
        JOIN(I, prev)(&last);
        if (JOIN(I, ref)(&first) == JOIN(I, ref)(&last))
            break;
        JOIN(I, iter_swap)(&first, &last);
        JOIN(I, next)(&first);
    }
}
#endif //!LIST
#endif //!SLIST

#endif // USET, SET

#ifdef INCLUDE_NUMERIC
#include <ctl/numeric.h>
#endif
#undef INCLUDE_NUMERIC
#undef INCLUDE_ALGORITHM

// TODO:
// copy_n C++11
// copy_n_range C++20
// copy_backward
// copy_backward_range C++20
// move_backward C++11
// move_backward_range C++20

//#endif // only once
