/* hive (C++26, formerly plf::colony): an unordered collection that gives every
   element a stable address for its whole lifetime and reuses the memory of
   erased elements for later insertions.  Storage is a linked list of
   fixed-capacity blocks with a per-container free-list of erased slots; erased
   slots are skipped during iteration and refilled on the next insert.

   Element addresses never change on insert/erase of *other* elements, so
   pointers and iterators to live elements stay valid.  Iteration order is
   unspecified (roughly insertion order within reused memory).

   Block capacity defaults to CTL_HIVE_BLOCK (32); override before include.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/hive.h>"
#endif

#include <assert.h>
#include <stdbool.h>
#include <ctl/ctl.h>

#ifndef CTL_HIVE_BLOCK
#define CTL_HIVE_BLOCK 32
#endif

#define CTL_HIVE
#define A JOIN(hive, T)
#define B JOIN(A, block)
#define I JOIN(A, it)
#define GI JOIN(A, it)

typedef struct B
{
    struct B *next;
    struct B *prev;
    T *data;
    unsigned char *skip; // 1 = erased/empty slot, 0 = active
    size_t cap;
    size_t used;  // high-water mark: slots [0,used) have been appended
    size_t count; // active (non-erased) elements in this block
} B;

typedef struct
{
    B *block;
    size_t index;
} JOIN(A, slot);

typedef struct A
{
    B *head;
    B *tail;
    size_t size;
    JOIN(A, slot) * freev; // LIFO stack of reusable erased slots
    size_t freen;
    size_t freecap;
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *); // 2-way operator<, optional
    int (*equal)(T *, T *);   // optional
} A;

typedef int (*JOIN(A, compare_fn))(T *, T *);

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    struct JOIN(I, vtable_t) vtable;
    T *ref;
    A *container;
    B *block;
    size_t index;
} I;

#include <ctl/bits/iterators.h>
#include <ctl/bits/integral.h>

// forward declarations
static inline void JOIN(I, next)(I *iter);
static inline T *JOIN(I, ref)(I *iter);
static inline int JOIN(I, done)(I *iter);
static inline I JOIN(A, iter_at)(A *self, B *block, size_t index);

static inline T JOIN(A, implicit_copy)(T *self)
{
    return *self;
}

static inline int JOIN(A, _equal)(A *self, T *a, T *b)
{
    if (self->equal)
        return self->equal(a, b);
    ASSERT(self->compare || !"equal or compare undefined");
    return !self->compare(a, b) && !self->compare(b, a);
}

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
    size_t c = 0;
    for (B *b = self->head; b; b = b->next)
        c += b->cap;
    return c;
}

static inline size_t JOIN(A, max_size)(void)
{
    return 4294967296 / sizeof(T);
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

static inline B *JOIN(B, init)(size_t cap)
{
    B *b = (B *)malloc(sizeof(B));
    b->next = b->prev = NULL;
    b->cap = cap;
    b->used = 0;
    b->count = 0;
    b->data = (T *)malloc(cap * sizeof(T));
    b->skip = (unsigned char *)malloc(cap * sizeof(unsigned char));
    memset(b->skip, 1, cap * sizeof(unsigned char));
    return b;
}

static inline B *JOIN(A, _append_block)(A *self)
{
    B *b = JOIN(B, init)(CTL_HIVE_BLOCK);
    b->prev = self->tail;
    if (self->tail)
        self->tail->next = b;
    else
        self->head = b;
    self->tail = b;
    return b;
}

static inline void JOIN(A, _free_push)(A *self, B *block, size_t index)
{
    if (self->freen == self->freecap)
    {
        self->freecap = self->freecap ? self->freecap * 2 : 8;
        self->freev = (JOIN(A, slot) *)realloc(self->freev, self->freecap * sizeof(JOIN(A, slot)));
    }
    self->freev[self->freen].block = block;
    self->freev[self->freen].index = index;
    self->freen++;
}

static inline void JOIN(A, reserve)(A *self, size_t n)
{
    while (JOIN(A, capacity)(self) < n)
        JOIN(A, _append_block)(self);
}

static inline I JOIN(A, insert)(A *self, T value)
{
    B *block;
    size_t index;
    if (self->freen)
    {
        JOIN(A, slot) s = self->freev[--self->freen];
        block = s.block;
        index = s.index;
    }
    else
    {
        if (!self->tail || self->tail->used == self->tail->cap)
            JOIN(A, _append_block)(self);
        block = self->tail;
        index = block->used++;
    }
    block->data[index] = value;
    block->skip[index] = 0;
    block->count++;
    self->size++;
    return JOIN(A, iter_at)(self, block, index);
}

static inline I JOIN(A, emplace)(A *self, T *value)
{
    return JOIN(A, insert)(self, *value);
}

// advance (block,index) to the first active slot at or after it; end => NULL
static inline void JOIN(A, _seek)(B **pblock, size_t *pindex)
{
    B *b = *pblock;
    size_t i = *pindex;
    while (b)
    {
        for (; i < b->used; i++)
            if (!b->skip[i])
            {
                *pblock = b;
                *pindex = i;
                return;
            }
        b = b->next;
        i = 0;
    }
    *pblock = NULL;
    *pindex = 0;
}

static inline I JOIN(A, iter_at)(A *self, B *block, size_t index)
{
    static I zero;
    I it = zero;
    it.container = self;
    it.block = block;
    it.index = index;
    it.ref = block ? &block->data[index] : NULL;
    it.vtable.next = JOIN(I, next);
    it.vtable.ref = JOIN(I, ref);
    it.vtable.done = JOIN(I, done);
    return it;
}

static inline I JOIN(A, begin)(A *self)
{
    B *b = self->head;
    size_t i = 0;
    JOIN(A, _seek)(&b, &i);
    return JOIN(A, iter_at)(self, b, i);
}

static inline I JOIN(A, end)(A *self)
{
    return JOIN(A, iter_at)(self, NULL, 0);
}

static inline T *JOIN(I, ref)(I *iter)
{
    return iter->ref;
}

static inline int JOIN(I, done)(I *iter)
{
    return iter->block == NULL;
}

static inline void JOIN(I, next)(I *iter)
{
    if (!iter->block)
        return;
    B *b = iter->block;
    size_t i = iter->index + 1;
    JOIN(A, _seek)(&b, &i);
    iter->block = b;
    iter->index = i;
    iter->ref = b ? &b->data[i] : NULL;
}

// erase the element at pos, returning an iterator to the next active element
static inline I JOIN(A, erase_it)(I *pos)
{
    A *self = pos->container;
    B *b = pos->block;
    size_t i = pos->index;
    if (!b)
        return *pos;
    B *nb = b;
    size_t ni = i + 1;
    JOIN(A, _seek)(&nb, &ni);
    if (self->free)
        self->free(&b->data[i]);
    b->skip[i] = 1;
    b->count--;
    self->size--;
    JOIN(A, _free_push)(self, b, i);
    return JOIN(A, iter_at)(self, nb, ni);
}

static inline void JOIN(A, clear)(A *self)
{
    B *b = self->head;
    while (b)
    {
        B *nx = b->next;
        if (self->free)
            for (size_t i = 0; i < b->used; i++)
                if (!b->skip[i])
                    self->free(&b->data[i]);
        free(b->data);
        free(b->skip);
        free(b);
        b = nx;
    }
    self->head = self->tail = NULL;
    self->size = 0;
    self->freen = 0;
}

static inline void JOIN(A, free)(A *self)
{
    JOIN(A, clear)(self);
    free(self->freev);
    JOIN(A, compare_fn) compare = self->compare;
    JOIN(A, compare_fn) equal = self->equal;
    *self = JOIN(A, init)();
    self->compare = compare;
    self->equal = equal;
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init_from)(self);
    for (B *b = self->head; b; b = b->next)
        for (size_t i = 0; i < b->used; i++)
            if (!b->skip[i])
                JOIN(A, insert)(&other, other.copy(&b->data[i]));
    return other;
}

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline I JOIN(A, find)(A *self, T key)
{
    for (B *b = self->head; b; b = b->next)
        for (size_t i = 0; i < b->used; i++)
            if (!b->skip[i] && JOIN(A, _equal)(self, &b->data[i], &key))
                return JOIN(A, iter_at)(self, b, i);
    return JOIN(A, end)(self);
}

static inline int JOIN(A, contains)(A *self, T key)
{
    I it = JOIN(A, find)(self, key);
    return !JOIN(I, done)(&it);
}

static inline size_t JOIN(A, count)(A *self, T key)
{
    size_t n = 0;
    for (B *b = self->head; b; b = b->next)
        for (size_t i = 0; i < b->used; i++)
            if (!b->skip[i] && JOIN(A, _equal)(self, &b->data[i], &key))
                n++;
    return n;
}

static inline size_t JOIN(A, remove_if)(A *self, int (*_match)(T *))
{
    size_t erases = 0;
    for (B *b = self->head; b; b = b->next)
        for (size_t i = 0; i < b->used; i++)
            if (!b->skip[i] && _match(&b->data[i]))
            {
                if (self->free)
                    self->free(&b->data[i]);
                b->skip[i] = 1;
                b->count--;
                self->size--;
                JOIN(A, _free_push)(self, b, i);
                erases++;
            }
    return erases;
}

static inline size_t JOIN(A, erase_if)(A *self, int (*_match)(T *))
{
    return JOIN(A, remove_if)(self, _match);
}

#undef A
#undef B
#undef I
#undef GI
#undef CTL_HIVE
#undef T
#undef POD
#undef NOT_INTEGRAL
