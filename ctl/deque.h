/* Double-ended queues are sequence containers with dynamic sizes
   that can be expanded or contracted on both ends.
   SPDX-License-Identifier: MIT
*/
/* It should be possible to do it thread-safe. Not yet. */

#ifndef T
#error "Template type T undefined for <ctl/deque.h>"
#endif

#define CTL_DEQ
#define A JOIN(deq, T)
#define B JOIN(A, bucket)
#define I JOIN(A, it)
#define GI JOIN(A, it)

#include <ctl/ctl.h>

#ifndef DEQ_BUCKET_SIZE
#define DEQ_BUCKET_SIZE (512)
#endif

typedef struct B
{
    T value[DEQ_BUCKET_SIZE];
    int16_t a;
    int16_t b;
} B;

typedef struct A
{
    B **pages;
    size_t mark_a;
    size_t mark_b;
    size_t capacity;
    size_t size;
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *); // 2-way operator<
    int (*equal)(T *, T *);
} A;

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_DEQ_ITER_FIELDS;
} I;

#include <ctl/bits/iterators.h>

static inline B **JOIN(A, first)(A *self)
{
    return &self->pages[self->mark_a];
}

static inline B **JOIN(A, last)(A *self)
{
    return &self->pages[self->mark_b - 1];
}

static inline T *JOIN(A, at)(A *self, size_t index)
{
    // allow accessing end (for iters)
    if (index == self->size)
        return NULL;
    else if (UNLIKELY(self->size == 0 || index > self->size))
    {
        ASSERT(index <= self->size || !"invalid deque index");
        self->capacity = 1;
        self->pages = (B **)calloc(1, sizeof(B *));
        if (!self->pages)
            return NULL;
        self->pages[0] = (B *)calloc(1, sizeof(B));
        if (!self->pages[0])
            return NULL;
        return &self->pages[0]->value[0];
    }
    else
    {
        const B *first = *JOIN(A, first)(self);
        const size_t actual = index + first->a;
        const size_t q = actual / DEQ_BUCKET_SIZE;
        const size_t r = actual % DEQ_BUCKET_SIZE;
        B *page = self->pages[self->mark_a + q];
        return &page->value[r];
    }
}

static inline void JOIN(A, shrink_to_fit)(A *self)
{
    if (self->capacity > self->size)
    {
        LOG("TODO shrink_to_fit %zu to %zu\n", self->capacity, self->size);
    }
    // Not needed. pop_back and pop_front are self-shrinking
    return;
}

// create an iter from an index
static inline I JOIN(B, iter)(A *self, size_t index);

static inline T *JOIN(A, front)(A *self)
{
    return JOIN(A, at)(self, 0);
}

static inline T *JOIN(A, back)(A *self)
{
    return self->size ? JOIN(A, at)(self, self->size - 1) : NULL;
}

static inline I JOIN(A, begin)(A *self)
{
    return JOIN(B, iter)(self, 0);
}

// We support `it.advance(a.end(), -1)`, so we must create a fresh iter.
static inline I JOIN(A, end)(A *self)
{
    return JOIN(B, iter)(self, self->size);
}

static inline T *JOIN(I, ref)(I *iter)
{
    return iter->ref;
}

static inline size_t JOIN(I, index)(I *iter)
{
    return iter->index;
}

static inline int JOIN(I, done)(I *iter)
{
    return iter->index == iter->end;
}

static inline void JOIN(I, set_done)(I *iter)
{
    iter->index = iter->end;
}

static void JOIN(I, next)(I *iter)
{
    iter->index++;
    if (iter->index < iter->end)
        iter->ref = JOIN(A, at)(iter->container, iter->index);
    ASSERT(iter->end >= iter->index);
}

static inline void JOIN(I, prev)(I *iter)
{
    if (iter->index)
    {
        iter->index--;
        iter->ref = JOIN(A, at)(iter->container, iter->index);
    }
}

static inline void JOIN(I, range)(I *first, I *last)
{
    last->end = first->end = last->index;
    ASSERT(first->end >= first->index);
}

static inline void JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->index;
    ASSERT(iter->end >= iter->index);
}

static inline I *JOIN(I, advance)(I *iter, long i)
{
    // error case: overflow => end or NULL?
    if (iter->index + i >= iter->end || iter->index + i >= iter->container->size || (long)iter->index + i < 0)
    {
        iter->index = iter->end;
        iter->ref = NULL;
    }
    else
    {
        iter->index += i;
        iter->ref = JOIN(A, at)(iter->container, iter->index);
    }
    ASSERT(iter->end >= iter->index);
    return iter;
}

static inline void JOIN(I, advance_end)(I *iter, long i)
{
    // error case: overflow => end or NULL?
    if (!(iter->index + i >= iter->end || iter->index + i >= iter->container->size || (long)iter->index + i < 0))
    {
        iter->end += i;
    }
    ASSERT(iter->end >= iter->index);
}

static inline long JOIN(I, distance)(I *iter, I *other)
{
    // wrap around?
    return other->index - iter->index;
}

static inline size_t JOIN(I, distance_range)(I *range)
{
    ASSERT(range->end >= range->index);
    return range->end - range->index;
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

// forwards for algorithm
static inline A JOIN(A, copy)(A *self);
static inline A JOIN(A, init)(void);
static inline I JOIN(A, find)(A *self, T key);
static inline void JOIN(A, push_back)(A *self, T value);
static inline I *JOIN(A, erase)(I *pos);

#include <ctl/bits/container.h>

static inline I JOIN(B, iter)(A *self, size_t index)
{
    static I zero;
    I iter = zero;
    if (index < self->size)
        iter.ref = JOIN(A, at)(self, index); // bounds-checked
    else
        iter.ref = JOIN(A, back)(self);
    iter.index = index;
    iter.end = self->size;
    iter.container = self;
    //iter.vtable = { JOIN(I, next), JOIN(I, ref), JOIN(I, done) };
    iter.vtable.next = JOIN(I, next);
    iter.vtable.ref = JOIN(I, ref);
    iter.vtable.done = JOIN(I, done);
    return iter;
}

static inline B *JOIN(B, init)(size_t cut)
{
    B *self = (B *)malloc(sizeof(B));
    self->a = self->b = cut;
    return self;
}

static inline B *JOIN(B, next)(B *self)
{
    return self;
}

static inline void JOIN(A, set)(A *self, size_t index, T value)
{
    T *ref = JOIN(A, at)(self, index);
#ifndef POD
    if (self->free)
        self->free(ref);
#endif
    *ref = value;
}

static inline void JOIN(A, alloc)(A *self, size_t capacity, size_t shift_from)
{
    self->capacity = capacity;
    self->pages = (B **)realloc(self->pages, capacity * sizeof(B *));
    size_t shift = (self->capacity - shift_from) / 2;
    size_t i = self->mark_b;
    while (i != 0)
    {
        i--;
        self->pages[i + shift] = self->pages[i];
    }
    self->mark_a += shift;
    self->mark_b += shift;
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

static inline void JOIN(A, push_front)(A *self, T value)
{
    if (JOIN(A, empty)(self))
    {
        self->mark_a = 0;
        self->mark_b = 1;
        JOIN(A, alloc)(self, 1, 0);
        *JOIN(A, last)(self) = JOIN(B, init)(DEQ_BUCKET_SIZE);
    }
    else
    {
        B *page = *JOIN(A, first)(self);
        if (page->a == 0)
        {
            if (self->mark_a == 0)
                JOIN(A, alloc)(self, 2 * self->capacity, self->mark_a);
            self->mark_a--;
            *JOIN(A, first)(self) = JOIN(B, init)(DEQ_BUCKET_SIZE);
        }
    }
    B *page = *JOIN(A, first)(self);
    page->a--;
    self->size++;
    page->value[page->a] = value;
}

static inline void JOIN(A, pop_front)(A *self)
{
    B *page = *JOIN(A, first)(self);
#ifndef POD
    if (self->free)
    {
        T *ref = &page->value[page->a];
        self->free(ref);
    }
#endif
    page->a++;
    self->size--;
    if (page->a == page->b)
    {
        free(page);
        self->mark_a++;
    }
}

static inline void JOIN(A, push_back)(A *self, T value)
{
    if (JOIN(A, empty)(self))
    {
        self->mark_a = 0;
        self->mark_b = 1;
        JOIN(A, alloc)(self, 1, 0);
        *JOIN(A, last)(self) = JOIN(B, init)(0);
    }
    else
    {
        B *page = *JOIN(A, last)(self);
        if (page->b == DEQ_BUCKET_SIZE)
        {
            if (self->mark_b == self->capacity)
                JOIN(A, alloc)(self, 2 * self->capacity, self->mark_b);
            self->mark_b++;
            *JOIN(A, last)(self) = JOIN(B, init)(0);
        }
    }
    B *page = *JOIN(A, last)(self);
    page->value[page->b] = value;
    page->b++;
    self->size++;
}

static inline void JOIN(A, pop_back)(A *self)
{
    B *page = *JOIN(A, last)(self);
    page->b--;
    self->size--;
#ifndef POD
    if (self->free)
    {
        T *ref = &page->value[page->b];
        self->free(ref);
    }
#endif
    if (page->b == page->a)
    {
        free(page);
        self->mark_b--;
    }
}

static inline size_t JOIN(A, erase_index)(A *self, size_t index)
{
    static T zero;
    JOIN(A, set)(self, index, zero);
#ifndef POD
    void (*saved)(T *) = self->free;
    self->free = NULL;
#endif
    if (index < self->size / 2)
    {
        for (size_t i = index; i > 0; i--)
            *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i - 1);
        JOIN(A, pop_front)(self);
    }
    else
    {
        for (size_t i = index; i < self->size - 1; i++)
            *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i + 1);
        JOIN(A, pop_back)(self);
    }
#ifndef POD
    self->free = saved;
#endif
    return index;
}

static inline I *JOIN(A, erase)(I *pos)
{
    pos->index = JOIN(A, erase_index)(pos->container, pos->index);
    return pos;
}

static inline void JOIN(A, insert_index)(A *self, size_t index, T value)
{
    if (self->size > 0)
    {
#ifndef POD
        void (*saved)(T *) = self->free;
        self->free = NULL;
#endif
        if (index < self->size / 2)
        {
            JOIN(A, push_front)(self, *JOIN(A, at)(self, 0));
            for (size_t i = 0; i < index; i++)
                *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i + 1);
        }
        else
        {
            JOIN(A, push_back)(self, *JOIN(A, at)(self, self->size - 1));
            for (size_t i = self->size - 1; i > index; i--)
                *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i - 1);
        }
        *JOIN(A, at)(self, index) = value;
#ifndef POD
        self->free = saved;
#endif
    }
    else
        JOIN(A, push_back)(self, value);
}

static inline void JOIN(A, insert)(I *pos, T value)
{
    A *self = pos->container;
    if (self->size > 0)
    {
        JOIN(A, insert_index)(self, pos->index, value);
    }
    else
    {
        JOIN(A, push_back)(self, value);
    }
    /*
    if (pos->index)
        pos->index--;
    pos->ref = JOIN(A, at)(self, pos->index); // bounds-checked (not at end)
    */
}

static inline void JOIN(A, clear)(A *self)
{
    while (!JOIN(A, empty)(self))
        JOIN(A, pop_back)(self);
}

static inline void JOIN(A, free)(A *self)
{
    JOIN(A, clear)(self);
    free(self->pages);
    *self = JOIN(A, init)();
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init)();
    while (other.size < self->size)
    {
        T *value = JOIN(A, at)(self, other.size);
        JOIN(A, push_back)(&other, other.copy(value));
    }
    return other;
}

static inline void JOIN(A, resize)(A *self, size_t size, T value)
{
    if (size != self->size)
    {
        // TODO optimize POD with realloc and memset
        while (size != self->size)
            if (size < self->size)
                JOIN(A, pop_back)(self);
            else
                JOIN(A, push_back)(self, self->copy(&value));
    }
    if (self->free)
        self->free(&value);
}

static inline I *JOIN(A, erase_range)(I *range)
{
    if (JOIN(I, done)(range))
        return range;
    A *self = range->container;
    size_t i = range->index;
    size_t e = range->end;
    if (i >= self->size || i >= e)
        return range;
    for (; i < e; e--)
        JOIN(A, erase_index)(self, i);
    return range;
}

static inline void JOIN(A, emplace)(I *pos, T *value)
{
    JOIN(A, insert)(pos, *value);
}

static inline void JOIN(A, emplace_front)(A *self, T *value)
{
    JOIN(A, push_front)(self, *value);
}

static inline void JOIN(A, emplace_back)(A *self, T *value)
{
    JOIN(A, push_back)(self, *value);
}

static inline void /* I* */
    JOIN(A, insert_range)(I *pos, I *range)
{
    A *self = pos->container;
    size_t index = pos->index;
    // safe against realloc within same container: relative indices only.
    // The STL cannot do that.
    if (!JOIN(I, done)(pos))
    {
        foreach_range_(A, iter, range)
            if (iter.ref)
                JOIN(A, insert_index)(self, index++, self->copy(iter.ref));
        pos->index = index;
        pos->end += JOIN(I, distance_range)(range);
    }
    else
    {
        foreach_range_(A, iter, range)
            if (iter.ref)
                JOIN(A, push_back)(self, self->copy(iter.ref));
        pos->end += JOIN(I, distance_range)(range);
    }
    /*
    if (pos->index)
        pos->index--;
    pos->ref = JOIN(A, at)(self, pos->index); // bounds-checked (not at end)
    //return pos;
    */
}

static inline I *JOIN(A, insert_count)(I *pos, size_t count, T value)
{
    A *self = pos->container;
    // detect overflows, esp. silent signed conversions, like -1
    size_t index = pos->index;
    if (self->size + count < self->size || index + count < count || self->size + count > JOIN(A, max_size)())
    {
        ASSERT(self->size + count >= self->size || !"count overflow");
        ASSERT(index + count >= count || !"pos overflow");
        ASSERT(self->size + count < JOIN(A, max_size)() || !"max_size overflow");
        if (self->free)
            self->free(&value);
        return NULL;
    }
    for (size_t i = index; i < count + index; i++)
        JOIN(A, insert_index)(self, i, self->copy(&value));
    if (self->free)
        self->free(&value);
    pos->end += count;
    return pos;
}

static inline void JOIN(A, assign)(A *self, size_t size, T value)
{
    JOIN(A, resize)(self, size, self->copy(&value));
    for (size_t i = 0; i < size; i++)
        JOIN(A, set)(self, i, self->copy(&value));
    if (self->free)
        self->free(&value);
}

// including to
static inline void JOIN(A, _ranged_sort)(A *self, size_t from, size_t to, int _compare(T *, T *))
{
    if (UNLIKELY(from >= to))
        return;
    // TODO insertion_sort cutoff
    // long mid = (from + to) / 2; // overflow!
    // Dietz formula http://aggregate.org/MAGIC/#Average%20of%20Integers
    size_t mid = ((from ^ to) >> 1) + (from & to);
    SWAP(T, JOIN(A, at)(self, from), JOIN(A, at)(self, mid));
    size_t z = from;
    // check overflow of a + 1
    if (LIKELY(from + 1 > from))
        for (size_t i = from + 1; i <= to; i++)
            if (!_compare(JOIN(A, at)(self, from), JOIN(A, at)(self, i)))
            {
                z++;
                SWAP(T, JOIN(A, at)(self, z), JOIN(A, at)(self, i));
            }
    SWAP(T, JOIN(A, at)(self, from), JOIN(A, at)(self, z));
    if (LIKELY(z))
        JOIN(A, _ranged_sort)(self, from, z - 1, _compare);
    // check overflow of z + 1
    if (LIKELY(z + 1 > z))
        JOIN(A, _ranged_sort)(self, z + 1, to, _compare);
}

static inline void JOIN(A, sort)(A *self)
{
    CTL_ASSERT_COMPARE
    // TODO insertion_sort cutoff
    if (self->size > 1)
        JOIN(A, _ranged_sort)(self, 0, self->size - 1, self->compare);
}

// excluding to
static inline void JOIN(A, sort_range)(A *self, size_t from, size_t to)
{
    CTL_ASSERT_COMPARE
    // TODO insertion_sort cutoff
    if (to > 1) // overflow with 0
        JOIN(A, _ranged_sort)(self, from, to - 1, self->compare);
}

static inline size_t JOIN(A, remove_if)(A *self, int (*_match)(T *))
{
    if (!self->size)
        return 0;
    size_t erases = 0;
    T *ref = JOIN(A, at)(self, 0);
    for (size_t i = 0; i < self->size;)
    {
        ref = JOIN(A, at)(self, i);
        if (_match(ref))
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

static inline I JOIN(A, find)(A *self, T key)
{
    foreach (A, self, i)
        if (JOIN(A, _equal)(self, i.ref, &key))
            return i;
    return JOIN(A, end)(self);
}

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

// move elements from range to the end of out
static inline A *JOIN(A, move_range)(I *range, A *out)
{
    A *self = range->container;
    size_t index = range->index;
    while (index != range->end)
    {
        T *ref = JOIN(A, at)(self, index);
        JOIN(A, push_back)(out, *ref);
        JOIN(A, erase_index)(self, index);
        index++;
    }
    return out;
}

static inline void JOIN(A, insert_generic)(I *pos, GI *range)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;

    while (!done(range))
    {
        JOIN(A, insert)(pos, *ref(range));
        pos->index++;
        //pos->end++;
        next(range);
    }
}

//#include <ctl/algorithm.h>

#undef T
#undef A
#undef B
#undef I
#undef GI
#undef POD
#undef NOT_INTEGRAL
#undef CTL_DEQ

#undef DEQ_BUCKET_SIZE
