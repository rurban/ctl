/* Double-ended queues are sequence containers with dynamic sizes
   that can be expanded or contracted on both ends.
   SPDX-License-Identifier: MIT
*/
/* It should be possible to do it thread-safe. Not yet. */

#ifndef T
# error "Template type T undefined for <ctl/deque.h>"
#endif

#define CTL_DEQ
#define A JOIN(deq, T)
#define B JOIN(A, bucket)
#ifndef C
# define C deq
#endif
#define I JOIN(A, it)
//#undef IT
#define IT T*

#include <ctl/ctl.h>
#include <ctl/bits/iterators.h>

#ifndef DEQ_BUCKET_SIZE
#define DEQ_BUCKET_SIZE (512)
#endif

#ifdef DEBUG
# if defined(_ASSERT_H) && !defined(NDEBUG)
# define CHECK_TAG(it,ret)                      \
    if (it->tag != CTL_DEQ_TAG)                 \
    {                                           \
        assert (it->tag == CTL_DEQ_TAG &&       \
                "invalid deque iterator");      \
        return ret;                             \
    }
# else
# define CHECK_TAG(it,ret)                      \
    if (it->tag != CTL_DEQ_TAG)                 \
        return ret;
# endif
#else
# define CHECK_TAG(it,ret)
#endif


typedef struct B
{
    T value[DEQ_BUCKET_SIZE];
    int16_t a;
    int16_t b;
} B;

typedef struct A
{
    B** pages;
    size_t mark_a;
    size_t mark_b;
    size_t capacity;
    size_t size;
    void (*free)(T*);
    T (*copy)(T*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*);
} A;

typedef struct I
{
    T* ref;
    A* container;
    size_t index;
#ifdef DEBUG
    uint32_t tag;
#endif
} I;

static I _deq_begin_it = {NULL, NULL, 0
#ifdef DEBUG
    , CTL_DEQ_TAG
#endif
};
static I _deq_end_it = {NULL, NULL, 0
#ifdef DEBUG
    , CTL_DEQ_TAG
#endif
};

/* Fast typed iters */
#define deq_foreach(A, T, self, pos)                  \
    if (self->size)                                   \
        for(T* pos = JOIN(A, begin)(self);            \
            pos != JOIN(A, end)(self);                \
            pos = JOIN(I, next)(pos))
#define deq_foreach_ref(A, T, self, i, ref)           \
    T* ref = (self)->size ? JOIN(A, at)(self, 0) : NULL; \
    for(size_t i = 0;                                 \
        i < (self)->size;                             \
        ++i, ref = JOIN(A, at)(self, i))
#define deq_foreach_range(A, T, pos, first, last)     \
    if (self->size)                                   \
        for(T* pos = first;                           \
            pos != last;                              \
            pos = JOIN(I, next)(pos))

static inline B**
JOIN(A, first)(A* self)
{
    return &self->pages[self->mark_a];
}

static inline B**
JOIN(A, last)(A* self)
{
    return &self->pages[self->mark_b - 1];
}

static inline T*
JOIN(A, at)(A* self, size_t index)
{
    // allow accessing end (for iters)
    if (index == self->size)
        return NULL;
    else if(UNLIKELY(self->size == 0 || index > self->size))
    {
#if defined(_ASSERT_H) && !defined(NDEBUG)
        assert (index <= self->size || !"invalid deque index");
#endif
        self->capacity = 1;
        self->pages = (B**) calloc(1, sizeof(B*));
        if (!self->pages)
            return NULL;
        self->pages[0] = (B*) calloc(1, sizeof(B));
        if (!self->pages[0])
            return NULL;
        return &self->pages[0]->value[0];
    }
    else
    {
        const B* first = *JOIN(A, first)(self);
        const size_t actual = index + first->a;
        const size_t q = actual / DEQ_BUCKET_SIZE;
        const size_t r = actual % DEQ_BUCKET_SIZE;
        B* page = self->pages[self->mark_a + q];
        return &page->value[r];
    }
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

// Embed index and container into the iter, returned as T*.
// Note that we can only have one single deq iter per deque.
static inline T*
JOIN(A, begin)(A* self)
{
    I *iter = &_deq_begin_it;
    iter->ref = JOIN(A, at)(self, 0);
    //only valid if not empty
    //iter.value = *JOIN(A, first)(self);
    iter->index = 0;
    iter->container = self;
    return (T*)iter;
}

// We support `it.advance(a.end() - 1)`, so we must create a fresh iter
// and embed the full iter into the T*.
// Note that we can only have one single deq end iter per deque.
static inline T*
JOIN(A, end)(A* self)
{
    I* iter = &_deq_end_it;
    iter->ref = JOIN(A, back)(self);
    iter->container = self;
    iter->index = self->size;
    return (T*)iter;
}

static inline I*
JOIN(I, iter)(T* self)
{
    I* iter = (I*)self;
    CHECK_TAG(iter, 0)
    return iter;
}

static inline size_t
JOIN(I, index)(T* self)
{
    I* iter = (I*)self;
    CHECK_TAG(iter, 0)
    return iter->index;
}

static inline int
JOIN(I, done)(T* self)
{
    return self != JOIN(A, end)(((I*)self)->container);
}

// must be constructed via begin or end, not first, last
static inline T*
JOIN(I, next)(T* self)
{
    I* iter = (I*)self;
    CHECK_TAG(iter, NULL)
    iter->index++;
    if(iter->index == iter->container->size)
        return JOIN(A, end)(iter->container);
    else
    {
        iter->ref = JOIN(A, at)(iter->container, iter->index);
        return (T*)iter;
    }
}

static inline T*
JOIN(I, advance)(T* self, int i)
{
    I* iter = (I*)self;
    CHECK_TAG(iter, NULL)
    // error case: overflow => end or NULL?
    if(iter->index + i >= iter->container->size || (long)iter->index + i < 0)
        return JOIN(A, end)(iter->container);
    else
    {
        iter->index += i;
        iter->ref = JOIN(A, at)(iter->container, iter->index);
        return (T*)iter;
    }
}

static inline long
JOIN(I, distance)(T* self, T* other)
{
    I* iter1 = (I*)self;
    I* iter2 = (I*)other;
    CHECK_TAG(iter1, 0)
    CHECK_TAG(iter2, 0)
    return iter2->index - iter1->index;
}

#include <ctl/bits/container.h>

static inline B*
JOIN(B, init)(size_t cut)
{
    B* self = (B*) malloc(sizeof(B));
    self->a = self->b = cut;
    return self;
}

static inline B*
JOIN(B, next)(B* self)
{
    return self;
}

static inline void
JOIN(A, set)(A* self, size_t index, T value)
{
    T* ref = JOIN(A, at)(self, index);
#ifndef POD
    if(self->free)
        self->free(ref);
#endif
    *ref = value;
}

static inline void
JOIN(A, alloc)(A* self, size_t capacity, size_t shift_from)
{
    self->capacity = capacity;
    self->pages = (B**) realloc(self->pages, capacity * sizeof(B*));
    size_t shift = (self->capacity - shift_from) / 2;
    size_t i = self->mark_b;
    while(i != 0)
    {
        i--;
        self->pages[i + shift] = self->pages[i];
    }
    self->mark_a += shift;
    self->mark_b += shift;
}

static inline A
JOIN(A, init)(void)
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

static inline void
JOIN(A, push_front)(A* self, T value)
{
    if(JOIN(A, empty)(self))
    {
        self->mark_a = 0;
        self->mark_b = 1;
        JOIN(A, alloc)(self, 1, 0);
        *JOIN(A, last)(self) = JOIN(B, init)(DEQ_BUCKET_SIZE);
    }
    else
    {
        B* page = *JOIN(A, first)(self);
        if(page->a == 0)
        {
            if(self->mark_a == 0)
                JOIN(A, alloc)(self, 2 * self->capacity, self->mark_a);
            self->mark_a--;
            *JOIN(A, first)(self) = JOIN(B, init)(DEQ_BUCKET_SIZE);
        }
    }
    B* page = *JOIN(A, first)(self);
    page->a--;
    self->size++;
    page->value[page->a] = value;
}

static inline void
JOIN(A, pop_front)(A* self)
{
    B* page = *JOIN(A, first)(self);
#ifndef POD
    if(self->free)
    {
        T* ref = &page->value[page->a];
        self->free(ref);
    }
#endif
    page->a++;
    self->size--;
    if(page->a == page->b)
    {
        free(page);
        self->mark_a++;
    }
}

static inline void
JOIN(A, push_back)(A* self, T value)
{
    if(JOIN(A, empty)(self))
    {
        self->mark_a = 0;
        self->mark_b = 1;
        JOIN(A, alloc)(self, 1, 0);
        *JOIN(A, last)(self) = JOIN(B, init)(0);
    }
    else
    {
        B* page = *JOIN(A, last)(self);
        if(page->b == DEQ_BUCKET_SIZE)
        {
            if(self->mark_b == self->capacity)
                JOIN(A, alloc)(self, 2 * self->capacity, self->mark_b);
            self->mark_b++;
            *JOIN(A, last)(self) = JOIN(B, init)(0);
        }
    }
    B* page = *JOIN(A, last)(self);
    page->value[page->b] = value;
    page->b++;
    self->size++;
}

static inline void
JOIN(A, pop_back)(A* self)
{
    B* page = *JOIN(A, last)(self);
    page->b--;
    self->size--;
#ifndef POD
    if(self->free)
    {
        T* ref = &page->value[page->b];
        self->free(ref);
    }
#endif
    if(page->b == page->a)
    {
        free(page);
        self->mark_b--;
    }
}

static inline size_t
JOIN(A, erase_index)(A* self, size_t index)
{
    static T zero;
    JOIN(A, set)(self, index, zero);
#ifndef POD
    void (*saved)(T*) = self->free;
    self->free = NULL;
#endif
    if(index < self->size / 2)
    {
        for(size_t i = index; i > 0; i--)
            *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i - 1);
        JOIN(A, pop_front)(self);
    }
    else
    {
        for(size_t i = index; i < self->size - 1; i++)
            *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i + 1);
        JOIN(A, pop_back)(self);
    }
#ifndef POD
    self->free = saved;
#endif
    return index;
}

static inline size_t
JOIN(A, erase)(A* self, T* pos)
{
    return JOIN(A, erase_index)(self, JOIN(I, index)(pos));
}

static inline void
JOIN(A, insert_index)(A* self, size_t index, T value)
{
    if(self->size > 0)
    {
#ifndef POD
        void (*saved)(T*) = self->free;
        self->free = NULL;
#endif
        if(index < self->size / 2)
        {
            JOIN(A, push_front)(self, *JOIN(A, at)(self, 0));
            for(size_t i = 0; i < index; i++)
                *JOIN(A, at)(self, i) = *JOIN(A, at)(self, i + 1);
        }
        else
        {
            JOIN(A, push_back)(self, *JOIN(A, at)(self, self->size - 1));
            for(size_t i = self->size - 1; i > index; i--)
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

static inline void
JOIN(A, insert)(A* self, T* pos, T value)
{
    if(self->size > 0)
    {
        size_t index = JOIN(I, index)(pos);
        JOIN(A, insert_index)(self, index, value);
    }
    else
        JOIN(A, push_back)(self, value);
}

static inline void
JOIN(A, clear)(A* self)
{
    while(!JOIN(A, empty)(self))
        JOIN(A, pop_back)(self);
}

static inline void
JOIN(A, free)(A* self)
{
    JOIN(A, clear)(self);
    free(self->pages);
    *self = JOIN(A, init)();
}

static inline A
JOIN(A, copy)(A* self)
{
    A other = JOIN(A, init)();
    while(other.size < self->size)
    {
        T* value = JOIN(A, at)(self, other.size);
        JOIN(A, push_back)(&other, other.copy(value));
    }
    return other;
}

static inline void
JOIN(A, resize)(A* self, size_t size, T value)
{
    if(size != self->size)
    {
        // TODO optimize POD with realloc and memset
        while(size != self->size)
            if(size < self->size)
                JOIN(A, pop_back)(self);
            else
                JOIN(A, push_back)(self, self->copy(&value));
    }
    FREE_VALUE(self, value);
}

static inline T*
JOIN(A, erase_range)(A* self, T* first, T* last)
{
    deq_foreach_range(A, T, pos, first, last)
        JOIN(A, erase)(self, pos);
    return first;
}

static inline void
JOIN(A, emplace)(A* self, T* pos, T* value)
{
    JOIN(A, insert)(self, pos, *value);
}

static inline void
JOIN(A, emplace_front)(A* self, T* value)
{
    JOIN(A, push_front)(self, *value);
}

static inline void
JOIN(A, emplace_back)(A* self, T* value)
{
    JOIN(A, push_back)(self, *value);
}

static inline T*
JOIN(A, insert_range)(A* self, T* pos, T* first, T* last)
{
    deq_foreach_range(A, T, iter, first, last)
    {
        size_t index = JOIN(I, index)(iter);
        T* ref = JOIN(A, at)(self, index);
        if (ref)
            JOIN(A, insert)(self, pos, self->copy(ref));
    }
    return pos;
}

static inline T*
JOIN(A, insert_count)(A* self, T* pos, size_t count, T value)
{
    // detect overflows, esp. silent signed conversions, like -1
    size_t index = JOIN(I, index)(pos);
    if (self->size + count < self->size ||
        index + count < count ||
        self->size + count > JOIN(A, max_size)())
    {
#if defined(_ASSERT_H) && !defined(NDEBUG)
        assert (self->size + count >= self->size || !"count overflow");
        assert (index + count >= count || !"pos overflow");
        assert (self->size + count < JOIN(A, max_size)() || !"max_size overflow");
#endif
        FREE_VALUE(self, value);
        return NULL;
    }
    for(size_t i = index; i < count + index; i++)
        JOIN(A, insert_index)(self, i, self->copy(&value));
    FREE_VALUE(self, value);
    return pos;
}

static inline void
JOIN(A, assign)(A* self, size_t size, T value)
{
    JOIN(A, resize)(self, size, self->copy(&value));
    for(size_t i = 0; i < size; i++)
        JOIN(A, set)(self, i, self->copy(&value));
    FREE_VALUE(self, value);
}

// including to
static inline void
JOIN(A, _ranged_sort)(A* self, size_t from, size_t to, int _compare(T*, T*))
{
    if(UNLIKELY(from >= to))
        return;
    // TODO insertion_sort cutoff
    //long mid = (from + to) / 2; // overflow!
    // Dietz formula http://aggregate.org/MAGIC/#Average%20of%20Integers
    size_t mid = ((from ^ to) >> 1) + (from & to);
    SWAP(T, JOIN(A, at)(self, from), JOIN(A, at)(self, mid));
    size_t z = from;
    // check overflow of a + 1
    if (LIKELY(from + 1 > from))
        for(size_t i = from + 1; i <= to; i++)
            if(_compare(JOIN(A, at)(self, from), JOIN(A, at)(self, i)))
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

static inline void
JOIN(A, sort)(A* self)
{
    CTL_ASSERT_COMPARE
    // TODO insertion_sort cutoff
    if (self->size > 1)
        JOIN(A, _ranged_sort)(self, 0, self->size - 1, self->compare);
}

// excluding to
static inline void
JOIN(A, sort_range)(A* self, size_t from, size_t to)
{
    CTL_ASSERT_COMPARE
    // TODO insertion_sort cutoff
    if (to > 1) // overflow with 0
        JOIN(A, _ranged_sort)(self, from, to - 1, self->compare);
}

static inline size_t
JOIN(A, remove_if)(A* self, int (*_match)(T*))
{
    size_t erases = 0;
    deq_foreach_ref(A, T, self, i, ref)
        if(_match(ref))
        {
            JOIN(A, erase_index)(self, i);
            erases++;
        }
    return erases;
}

static inline size_t
JOIN(A, erase_if)(A* self, int (*_match)(T*))
{
    return JOIN(A, remove_if)(self, _match);
}

static inline T*
JOIN(A, find)(A* self, T key)
{
    deq_foreach(A, T, self, pos)
        if(JOIN(A, _equal)(self, pos, &key))
            return pos;
    return NULL;
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

//#include <ctl/algorithm.h>

#undef T
#undef A
#undef B
#undef C
#undef I
#undef IT
#undef POD
#undef NOT_INTEGRAL
#undef CTL_DEQ

#undef DEQ_BUCKET_SIZE
