/* Double-ended queues are sequence containers with dynamic sizes
   that can be expanded or contracted on both ends. */
/* It should be possible to do it thread-safe. Not yet. */

#ifndef T
#error "Template type T undefined for <ctl/deque.h>"
#endif

#include <ctl/ctl.h>

#define CTL_DEQ
#define A JOIN(deq, T)
#define B JOIN(A, bucket)
#define I JOIN(A, it)

#define DEQ_BUCKET_SIZE (512)

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
    CTL_COMMONFIELDS_ITER;
    A* container;
    size_t index;
    size_t index_next;
    size_t index_last;
} I;

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
    if(self->size == 0 || index >= self->size)
    {
#if defined(_ASSERT_H) && !defined(NDEBUG)
        assert (index < self->size);
#endif
        return NULL;
    }
    else
    {
        B* first = *JOIN(A, first)(self);
        size_t actual = index + first->a;
        B* page = self->pages[self->mark_a + actual / DEQ_BUCKET_SIZE];
        return &page->value[actual % DEQ_BUCKET_SIZE];
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
    self->index = self->index_next;
    if(self->index == self->index_last)
        self->done = 1;
    else
    {
        self->ref = JOIN(A, at)(self->container, self->index);
        self->index_next++;
    }
}

static inline void
JOIN(I, advance)(I* self, int i)
{
    if(self->index + i >= self->index_last || (long)self->index + i < 0)
        self->done = 1;
    else
    {
        self->index += i;
        self->ref = JOIN(A, at)(self->container, self->index);
        self->index_next += i;
    }
}

static inline I
JOIN(I, range)(A* container, T* begin, T* end)
{
    static I zero;
    I self = zero;
    if(begin && end)
    {
        self.container = container;
        self.step = JOIN(I, step);
        self.index = begin - JOIN(A, begin)(container);
        self.index_next = self.index + 1;
        self.index_last = container->size - (JOIN(A, end)(container) - end);
        self.ref = JOIN(A, at)(container, self.index);
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

static inline B*
JOIN(B, init)(size_t cut)
{
    B* self = (B*) malloc(sizeof(B));
    self->a = self->b = cut;
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
    if(self->free)
    {
        T* ref = &page->value[page->a];
        self->free(ref);
    }
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
    if(self->free)
    {
        T* ref = &page->value[page->b];
        self->free(ref);
    }
    if(page->b == page->a)
    {
        free(page);
        self->mark_b--;
    }
}

static inline void
JOIN(A, erase)(A* self, size_t index)
{
    static T zero;
    JOIN(A, set)(self, index, zero);
    void (*saved)(T*) = self->free;
    self->free = NULL;
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
    self->free = saved;
}

static inline void
JOIN(A, insert)(A* self, size_t index, T value)
{
    if(self->size > 0)
    {
        void (*saved)(T*) = self->free;
        self->free = NULL;
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
        self->free = saved;
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
    if(self->free)
        self->free(&value);

}

static inline I*
JOIN(A, erase_it)(A* self, I* pos)
{
    JOIN(A, erase)(self, pos->index);
    return pos;
}

static inline I*
JOIN(A, erase_range)(A* self, I* first, I* last)
{
    for(size_t i = first->index; i < last->index; i++)
        JOIN(A, erase)(self, first->index);
    return first;
}

static inline void
JOIN(A, emplace)(A* self, I* pos, T* value)
{
    JOIN(A, insert)(self, pos->index, *value);
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

static inline I*
JOIN(A, insert_it)(A* self, I* pos, T value)
{
    JOIN(A, insert)(self, pos->index, value);
    return pos;
}

static inline I*
JOIN(A, insert_range)(A* self, I* pos, I* first, I* last)
{
    if (first->index < last->index)
    {
        size_t index = pos->index;
        if (!last->done)
            first->index_last = last->index;
        // broken if overlapping. STL does mostly fine, but undefined behavior.
        // and sometimes it even fails. so skip or assert.
        if (first->container == pos->container)
        {
#if defined(_ASSERT_H) && !defined(NDEBUG)
            assert (first->container != pos->container || !"container overlap");
#endif
#if 0
            A copy = JOIN(A, copy)(self);
            for(I it = *first; !it.done; it.step(&it))
                JOIN(A, insert)(&copy, index++, self->copy(it.ref));
            for (size_t i = pos->index; i < index; i++)
            {
                T value = *JOIN(A, at)(&copy, i);
                JOIN(A, insert)(self, i, self->copy(&value));
            }
            JOIN(A, free)(&copy);
#endif
        }
        else
            for(I it = *first; !it.done; it.step(&it))
                JOIN(A, insert)(self, index++, self->copy(it.ref));
    }
    return pos;
}

static inline I*
JOIN(A, insert_count)(A* self, I* pos, size_t count, T value)
{
    // detect overflows, esp. silent signed conversions, like -1
    if (self->size + count < self->size ||
        count + pos->index < count ||
        self->size + count > JOIN(A, max_size)())
    {
#if defined(_ASSERT_H) && !defined(NDEBUG)
        assert (self->size + count >= self->size || !"count overflow");
        assert (pos->index + count >= count || !"pos overflow");
        assert (self->size + count < JOIN(A, max_size)() || !"max_size overflow");
#endif
        if(self->free)
            self->free(&value);
        return NULL;
    }
    for(size_t i = pos->index; i < count + pos->index; i++)
        JOIN(A, insert)(self, i, self->copy(&value));
    if(self->free)
        self->free(&value);
    return pos;
}

static inline void
JOIN(A, assign)(A* self, size_t size, T value)
{
    JOIN(A, resize)(self, size, self->copy(&value));
    for(size_t i = 0; i < size; i++)
        JOIN(A, set)(self, i, self->copy(&value));
    if(self->free)
        self->free(&value);
}

// including to
static inline void
JOIN(A, _ranged_sort)(A* self, long from, long to, int _compare(T*, T*))
{
    if(from >= to)
        return;
    long mid = (from + to) / 2;
    SWAP(T, JOIN(A, at)(self, from), JOIN(A, at)(self, mid));
    long z = from;
    for(long i = from + 1; i <= to; i++)
        if(_compare(JOIN(A, at)(self, from), JOIN(A, at)(self, i)))
        {
            z++;
            SWAP(T, JOIN(A, at)(self, z), JOIN(A, at)(self, i));
        }
    SWAP(T, JOIN(A, at)(self, from), JOIN(A, at)(self, z));
    if (z)
        JOIN(A, _ranged_sort)(self, from, z - 1, _compare);
    JOIN(A, _ranged_sort)(self, z + 1, to, _compare);
}

static inline void
JOIN(A, sort)(A* self)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->compare || !"compare undefined");
#endif
    if (self->size)
        JOIN(A, _ranged_sort)(self, 0, self->size - 1, self->compare);
}

// excluding to
static inline void
JOIN(A, sort_range)(A* self, I* from, I* to)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->compare);
#endif
    if (to->index)
        JOIN(A, _ranged_sort)(self, from->index, to->index - 1, self->compare);
}

static inline size_t
JOIN(A, remove_if)(A* self, int (*_match)(T*))
{
    size_t erases = 0;
    foreach(A, self, it)
        if(_match(it.ref))
        {
            JOIN(A, erase)(self, it.index);
            it.index_next = it.index;
            it.index_last--;
            erases++;
        }
    return erases;
}

static inline T*
JOIN(A, find)(A* self, T key)
{
    foreach(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, &key))
            return it.ref;
    return NULL;
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

#ifdef DEBUG

static inline I*
JOIN(A, find_range)(A* self, I* first, I* last, T value)
{
    foreach(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, &value))
            return first;
    return last;
}

#endif


#undef T
#undef A
#undef B
#undef I
#undef POD
#undef NOT_INTEGRAL
#undef CTL_DEQ

#undef DEQ_BUCKET_SIZE
