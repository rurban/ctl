// Optional generic algorithms
// DO NOT STANDALONE INCLUDE, need container included before.
// SPDX-License-Identifier: MIT
//
// Might only be included once. By the child. not the parent.
//#ifndef __CTL_ALGORITHM_H__
//#define __CTL_ALGORITHM_H__

#if !defined CTL_LIST && \
    !defined CTL_SET && \
    !defined CTL_USET && \
    !defined CTL_VEC && \
    !defined CTL_ARR && \
    !defined CTL_DEQ && \
    /* plus all children also. we don't include it for parents */ \
    !defined CTL_STACK && \
    !defined CTL_QUEUE && \
    !defined CTL_PQU && \
    !defined CTL_MAP && \
    !defined CTL_UMAP
# error "No CTL container defined for <ctl/algorithm.h>"
#endif
#undef CTL_ALGORITHM
#define CTL_ALGORITHM

// Generic algorithms with ranges

static inline I
JOIN(A, find_if)(A* self, int _match(T*))
{
    foreach(A, self, i)
        if(_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline I
JOIN(A, find_if_not)(A* self, int _match(T*))
{
    foreach(A, self, i)
        if(!_match(i.ref))
            return i;
    return JOIN(A, end)(self);
}

// C++11
static inline bool
JOIN(A, all_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if_not)(self, _match);
    return JOIN(I, done)(&pos);
}

// C++11
static inline bool
JOIN(A, any_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if)(self, _match);
    return !JOIN(I, done)(&pos);
}

static inline bool
JOIN(A, none_of)(A* self, int _match(T*))
{
    I pos = JOIN(A, find_if)(self, _match);
    return JOIN(I, done)(&pos);
}

#include <stdbool.h>

#ifndef CTL_USET // no ranges

static inline I
JOIN(A, find_range)(I* first, I* last, T value)
{
    A* self = first->container;
    foreach_range(A, i, first, last)
        if(JOIN(A, _equal)(self, i.ref, &value))
            return i;
    return *last;
}

static inline I
JOIN(A, find_if_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, i, first, last)
        if(_match(i.ref))
            return i;
    return *last;
}

static inline I
JOIN(A, find_if_not_range)(I* first, I* last, int _match(T*))
{
    foreach_range(A, i, first, last)
        if(!_match(i.ref))
            return i;
    return *last;
}

// C++20
static inline bool
JOIN(A, all_of_range)(I* first, I* last, int _match(T*))
{
    I pos = JOIN(A, find_if_not_range)(first, last, _match);
    if (JOIN(I, done)(first))
        return true;
    return JOIN(I, done)(&pos);
}
// C++20
static inline bool
JOIN(A, none_of_range)(I* first, I* last, int _match(T*))
{
    I pos = JOIN(A, find_if_range)(first, last, _match);
    if (JOIN(I, done)(first))
        return true;
    return JOIN(I, done)(&pos);
}
// C++20
static inline bool
JOIN(A, any_of_range)(I* first, I* last, int _match(T*))
{
    return !JOIN(A, none_of_range)(first, last, _match);
}

#endif // USET (ranges)


// set/uset have optimized implementations.
// These require now sorted containers via operator< and push_back.
#if defined(CTL_LIST) || \
    defined(CTL_VEC) || \
    defined(CTL_STR) || \
    defined(CTL_DEQ)

static inline A*
JOIN(A, copy_range)(I* range, A* out)
{
    while(!JOIN(I, done)(range))
    {
        JOIN(A, push_back)(out, out->copy(range->ref));
        JOIN(I, next)(range);
    }
    return out;
}

static inline int
JOIN(A, _found)(A* a, T* ref)
{
#ifdef CTL_STR
    return strchr(a->vector, *ref) ? 1 : 0;
#else
    JOIN(A, it) iter = JOIN(A, find)(a, *ref);
    return !JOIN(I, done)(&iter);
#endif
}

// requires sorted containers (via operator<) and push_back
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
            JOIN(A, push_back)(&self, self.copy(it2.ref));
            JOIN(I, next)(&it2);
        }
        else
        {
            JOIN(A, push_back)(&self, self.copy(it1.ref));
            if (!self.compare(it1.ref, it2.ref))
                JOIN(I, next)(&it2);
            JOIN(I, next)(&it1);
        }
    }
    return *JOIN(A, copy_range)(&it2, &self);
}
*/

static inline A
JOIN(A, union_range)(I* r1, I* r2)
{
    A self = JOIN(A, init_from)(r1->container);
    while(!JOIN(I, done)(r1))
    {
        if (JOIN(I, done)(r2))
            return *JOIN(A, copy_range)(r1, &self);
        if (self.compare(r2->ref, r1->ref))
        {
            JOIN(A, push_back)(&self, self.copy(r2->ref));
            JOIN(I, next)(r2);
        }
        else
        {
            JOIN(A, push_back)(&self, self.copy(r1->ref));
            if (!self.compare(r1->ref, r2->ref))
                JOIN(I, next)(r2);
            JOIN(I, next)(r1);
        }
    }
    JOIN(A, copy_range)(r2, &self);
    return self;
}

static inline A
JOIN(A, union)(A* a, A* b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, union_range)(&r1, &r2);
}

static inline A
JOIN(A, intersection_range)(I* r1, I* r2)
{
    A self = JOIN(A, init_from)(r1->container);
    while(!JOIN(I, done)(r1) && !JOIN(I, done)(r2))
    {
        if (self.compare(r1->ref, r2->ref))
            JOIN(I, next)(r1);
        else
        {
            if (!self.compare(r2->ref, r1->ref))
                JOIN(A, push_back)(&self, self.copy(r1->ref));
            JOIN(I, next)(r2);
        }
    }
#if defined(CTL_VEC) && !defined(CTL_STR)
    JOIN(A, shrink_to_fit)(&self);
#endif
    return self;
}

static inline A
JOIN(A, intersection)(A* a, A* b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it)
        if(JOIN(A, _found)(b, it.ref))
            JOIN(A, push_back)(&self, self.copy(it.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, intersection_range)(&r1, &r2);
#endif
}

static inline A
JOIN(A, difference_range)(I* r1, I* r2)
{
    A self = JOIN(A, init_from)(r1->container);
    while(!JOIN(I, done)(r1))
    {
        if (JOIN(I, done)(r2))
            return *JOIN(A, copy_range)(r1, &self);

        if (self.compare(r1->ref, r2->ref))
        {
            JOIN(A, push_back)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (!self.compare(r2->ref, r1->ref))
                JOIN(I, next)(r1);
            JOIN(I, next)(r2);
        }
    }
    return self;
}

static inline A
JOIN(A, difference)(A* a, A* b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it)
        if(!JOIN(A, _found)(b, it.ref))
            JOIN(A, push_back)(&self, self.copy(it.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, difference_range)(&r1, &r2);
#endif
}

static inline A
JOIN(A, symmetric_difference_range)(I* r1, I* r2)
{
    A self = JOIN(A, init_from)(r1->container);
    while(!JOIN(I, done)(r1))
    {
        if (JOIN(I, done)(r2))
            return *JOIN(A, copy_range)(r1, &self);

        if (self.compare(r1->ref, r2->ref))
        {
            JOIN(A, push_back)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (self.compare(r2->ref, r1->ref))
                JOIN(A, push_back)(&self, self.copy(r2->ref));
            else
                JOIN(I, next)(r1);
            JOIN(I, next)(r2);
        }
    }
    JOIN(A, copy_range)(r2, &self);
#ifdef CTL_VEC
    //JOIN(A, shrink_to_fit)(&self);
#endif
    return self;
}

static inline A
JOIN(A, symmetric_difference)(A* a, A* b)
{
#if 0
    A self = JOIN(A, init_from)(a);
    foreach(A, a, it1)
        if(!JOIN(A, _found)(b, it1.ref))
            JOIN(A, push_back)(&self, self.copy(it1.ref));
    foreach(A, b, it2)
        if(!JOIN(A, _found)(a, it2.ref))
            JOIN(A, push_back)(&self, self.copy(it2.ref));
    return self;
#else
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, symmetric_difference_range)(&r1, &r2);
#endif
}

static inline bool
JOIN(A, includes_range)(I* r1, I* r2)
{
    A* self = r1->container;
    while(!JOIN(I, done)(r2))
    {
        if (JOIN(I, done)(r1) || self->compare(r2->ref, r1->ref))
            return false;
        if (!self->compare(r1->ref, r2->ref))
            JOIN(I, next)(r2);
        JOIN(I, next)(r1);
    }
    return true;
}

static inline bool
JOIN(A, includes)(A* a, A* b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, includes_range)(&r1, &r2);
}

#endif // !USET/SET

// generate and transform have no inserter support yet,
// so we cannot yet use it for set nor uset. we want to call insert/push_back on them.
// for list and vector we just set/replace the elements.
#if !defined(CTL_USET) && !defined(CTL_SET)

static inline void
JOIN(A, generate)(A* self, T _gen(void))
{
    foreach(A, self, i)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

static inline void
JOIN(A, generate_range)(I* first, I* last, T _gen(void))
{
#ifndef POD
    A* self = first->container;
#endif
    foreach_range(A, i, first, last)
    {
#ifndef POD
        if (self->free)
            self->free(i.ref);
#endif
        *i.ref = _gen();
    }
}

static inline A
JOIN(A, transform)(A* self, T _unop(T*))
{
    A other = JOIN(A, copy)(self);
    foreach(A, &other, i)
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

#ifndef CTL_ARR
static inline A
JOIN(A, transform_it)(A* self, I* pos, T _binop(T*, T*))
{
    A other = JOIN(A, init_from)(self);
#ifdef CTL_VEC
    if (self->size > 1)
        JOIN(A, fit)(&other, self->size - 1);
#endif
    foreach(A, self, i)
    {
        if (JOIN(I, done)(pos))
            break;
        T tmp = _binop(i.ref, pos->ref);
        JOIN(A, push_back)(&other, tmp);
        JOIN(I, next)(pos);
    }
#if defined(CTL_VEC) && !defined(CTL_STR)
    JOIN(A, shrink_to_fit)(&other);
#endif
    return other;
}
#endif // ARR

// std::deque has a different idea
static inline void
JOIN(A, generate_n)(A* self, size_t count, T _gen(void))
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
static inline void
JOIN(A, generate_n_range)(I* first, size_t count, T _gen(void))
{
#ifndef POD
    A* self = first->container;
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
static inline I
JOIN(A, transform_range)(I* first1, I* last1, I dest, T _unop(T*))
{
    foreach_range(A, i, first1, last1)
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
static inline I
JOIN(A, transform_it_range)(I* first1, I* last1, I* pos, I dest, T _binop(T*, T*))
{
    foreach_range(A, i, first1, last1)
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

#else // USET/SET
// no push_back, but insert
static inline A*
JOIN(A, copy_range)(I* range, A* out)
{
    while(!JOIN(I, done)(range))
    {
        JOIN(A, insert)(out, out->copy(range->ref));
        JOIN(I, next)(range);
    }
    return out;
}
#endif // USET/SET inserter

#if !defined(CTL_USET)
/// uset has cached_hash optims
static inline size_t
JOIN(A, count_range)(I* first, I* last, T value)
{
    A* self = first->container;
    size_t count = 0;
    foreach_range(A, i, first, last)
        if(JOIN(A, _equal)(self, i.ref, &value))
            count++;
    if (self->free)
        self->free(&value);
    return count;
}
#if !defined(CTL_SET) && !defined(CTL_STR)
// str has its own variant via faster find. set/uset do not need it.
static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, i)
        if(JOIN(A, _equal)(self, i.ref, &value))
            count++;
    if(self->free)
        self->free(&value);
    return count;
}
#endif // SET/STR

static inline bool
JOIN(A, mismatch)(I* range1, I* range2)
{
    A* self = range1->container;
    CTL_ASSERT_EQUAL
    int done = JOIN(I, done)(range1);
    if (!JOIN(I, done)(range2))
        while(!done && JOIN(A, _equal)(self, range1->ref, range2->ref))
        {
            JOIN(I, next)(range1);
            JOIN(I, next)(range2);
            done = JOIN(I, done)(range1);
            if (JOIN(I, done)(range2))
            {
                done = 1;
                break;
            }
        }
    return done ? false : true;
}
#endif // USET

//#if !defined(CTL_STR)
// C++20
static inline size_t
JOIN(A, count_if_range)(I* first, I* last, int _match(T*))
{
    size_t count = 0;
    foreach_range(A, i, first, last)
        if(_match(i.ref))
            count++;
    return count;
}

static inline size_t
JOIN(A, count_if)(A* self, int _match(T*))
{
    size_t count = 0;
    foreach(A, self, i)
        if(_match(i.ref))
            count++;
    return count;
}
//#endif // STR

// use strstr or provide a better SIMD optimized variant.
// strstr is easily beatable. see http://0x80.pl/articles/simd-strfind.html
#if !defined(CTL_STR)

// Sets range1 (the haystack) to the found pointer if found.
// Naive r1*r2 cost, no Boyer-Moore yet.
static inline bool
JOIN(A, search_range)(I *range1, I* range2)
{

    if (JOIN(I, done)(range1))
        return false;
    if (JOIN(I, done)(range2))
        return true;
    A* self = range1->container;
    for (; ; JOIN(I, next)(range1))
    {
        I it = *range1;
        I s_it = *range2;
        for (;;)
        {
            if (JOIN(I, done)(&s_it))
                return true;
            if (JOIN(I, done)(&it))
                return false;
            if (!JOIN(A, _equal)(self, it.ref, s_it.ref))
                break;
            JOIN(I, next)(&it);
            JOIN(I, next)(&s_it);
        }
    }
    return false;
}

// Returns iterator to the found pointer or end
static inline I
JOIN(A, search)(A* self, I* first2, I* last2)
{
    I begin = JOIN(A, begin)(self);
    JOIN(I, range)(first2, last2);
    if (JOIN(A, search_range)(&begin, first2))
        return begin;
    else
        return JOIN(A, end)(self);
}
#if 0
static inline I
JOIN(A, find_end_range)(I* range1, I* range2)
{
    A* self = range1->container;
    if (JOIN(I, done)(range2))
    {
        JOIN(I, set_end)(range1);
        return *range1;
    }
    I result = *range1;
    JOIN(I, set_end)(&result);
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
#endif // 0, need set_end
#endif // STR

static inline I*
JOIN(A, adjacent_find_range)(I *range)
{

    if (JOIN(I, done)(range))
        return range;
    A* self = range->container;
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

static inline I
JOIN(A, adjacent_find)(A *self)
{

    if (JOIN(A, size)(self) < 2)
        return JOIN(A, end)(self);
    I range = JOIN(A, begin)(self);
    return *JOIN(A, adjacent_find_range)(&range);
}

#ifdef DEBUG

// TODO not for value but matching range
static inline I
JOIN(A, find_end)(A* self, T value)
{
    I ret = JOIN(A, end)(self);
    foreach(A, self, i)
        if(JOIN(A, _equal)(self, i.ref, &value))
            ret = i;
    return ret;
}

#if !defined(CTL_USET) && !defined(CTL_STR)
// API? 3rd arg should be an iter, not a value
static inline bool
JOIN(A, equal_range)(A* self, I* first, I* last, T value)
{
    bool result = true;
    foreach_range(A, i, first, last)
        if(!JOIN(A, _equal)(self, i.ref, &value))
        {
            result = false;
            break;
        }
    if(self && self->free)
        self->free(&value);
    return result;
}
#endif // USET+STR

#ifndef CTL_USET

static inline I
JOIN(A, lower_bound)(A* self, T value)
{
    CTL_ASSERT_COMPARE
    JOIN(A, it) it = JOIN(A, begin)(self);
    size_t count = JOIN(A, size)(self);
    while (count > 0)
    {
        size_t step = count / 2;
        JOIN(I, advance)(&it, step);
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            count -= step + 1;
        } else
            count = step;
    }
    if(self->free)
        self->free(&value);
    return it;
}

static inline I
JOIN(A, upper_bound)(A* self, T value)
{
    CTL_ASSERT_COMPARE
    JOIN(A, it) it = JOIN(A, begin)(self);
    size_t count = JOIN(A, size)(self);
    while (count > 0)
    {
        size_t step = count / 2;
        JOIN(I, advance)(&it, step);
        if (!self->compare(&value, it.ref))
        {
            JOIN(I, next)(&it);
            count -= step + 1;
        } else
            count = step;
    }
    if(self->free)
        self->free(&value);
    return it;
}

static inline I
JOIN(A, lower_bound_range)(I* first, I* last, T value)
{
    A* self = first->container;
    CTL_ASSERT_COMPARE
    JOIN(A, it) it = *first;
    size_t count = JOIN(I, distance)(first, last);
    while (count > 0)
    {
        size_t step = count / 2;
        JOIN(I, advance)(&it, step);
        if (self->compare(it.ref, &value))
        {
            JOIN(I, next)(&it);
            count -= step + 1;
        } else
            count = step;
    }
    if(self->free)
        self->free(&value);
    return it;
}
static inline I
JOIN(A, upper_bound_range)(I* first, I* last, T value)
{
    A* self = first->container;
    CTL_ASSERT_COMPARE
    JOIN(A, it) it = *first;
    size_t count = JOIN(I, distance)(first, last);
    while (count > 0)
    {
        size_t step = count / 2;
        JOIN(I, advance)(&it, step);
        if (!self->compare(&value, it.ref))
        {
            JOIN(I, next)(&it);
            count -= step + 1;
        } else
            count = step;
    }
    if(self->free)
        self->free(&value);
    return it;
}

#endif // USET

#endif // DEBUG

// TODO:
// find_first_of
// find_first_of_range C++20
// adjacent_find
// adjacent_find_range C++20
// search
// search_range C++20
// search_n
// search_n_range C++20
// copy_if C++11
// copy_if_range C++20
// copy_n C++11
// copy_n_range C++20
// copy_backward
// copy_backward_range C++20
// move C++11
// move_range
// move_backward C++11
// move_backward_range C++20

//#endif // only once
