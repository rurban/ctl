/* List containers are implemented as doubly-linked lists
   SPDX-License-Identifier: MIT
 */

#ifndef T
#error "Template type T undefined for <ctl/list.h>"
#endif

#define CTL_LIST
#define A JOIN(list, T)
#define B JOIN(A, node)
#define I JOIN(A, it)
#define GI JOIN(A, it)

#include <ctl/ctl.h>

typedef struct B
{
    struct B *next;
    struct B *prev;
    T value;
} B;

typedef struct A
{
    B *head;
    B *tail;
    size_t size;
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *); // 2-way operator<
    int (*equal)(T *, T *);
} A;

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_B_ITER_FIELDS;
} I;

#include <ctl/bits/iterators.h>

typedef int (*JOIN(A, compare_fn))(T *, T *);

static inline T *JOIN(A, front)(A *self)
{
    return self->head ? &self->head->value : NULL;
}

static inline T *JOIN(A, back)(A *self)
{
    return self->tail ? &self->tail->value : NULL;
}

static inline I JOIN(I, iter)(A *self, B *node);

static inline I JOIN(A, begin)(A *self)
{
    return JOIN(I, iter)(self, self->head);
}

static inline I JOIN(A, end)(A *self)
{
    return JOIN(I, iter)(self, NULL);
}

static inline int JOIN(I, done)(I *iter)
{
    return iter->node == iter->end;
}

static inline B *JOIN(B, next)(B *node)
{
    return node->next;
}

static inline void JOIN(I, next)(I *iter)
{
    if (LIKELY(iter->node))
    {
        iter->node = iter->node->next;
        if (iter->node)
            iter->ref = &iter->node->value;
    }
}

static inline void JOIN(I, prev)(I *iter)
{
    if (LIKELY(iter->node))
    {
        iter->node = iter->node->prev;
        if (iter->node)
            iter->ref = &iter->node->value;
    }
}

static inline void JOIN(I, range)(I *first, I *last)
{
    last->end = first->end = last->node;
}

static inline void JOIN(I, set_done)(I *iter)
{
    iter->node = iter->end;
}

static inline void JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->node;
}

static inline T *JOIN(I, ref)(I *iter)
{
    return &iter->node->value;
}

static inline I *JOIN(I, advance)(I *self, long i);

// the only way to keep the iter struct intact
static inline I *JOIN(I, advance)(I *iter, long i)
{
    A *a = iter->container;
    B *node = iter->node;
    if (UNLIKELY(i < 0))
    {
        if ((size_t)-i > a->size)
            return NULL;
        return JOIN(I, advance)(iter, a->size + i);
    }
    for (long j = 0; node != NULL && j < i; j++)
        node = node->next;
    iter->node = node;
    if (LIKELY(node))
        iter->ref = &node->value;
    return iter;
}

// set end node
static inline void JOIN(I, advance_end)(I *iter, long n)
{
    B *node = iter->node;
    for (long i = 0; i < n && iter->node != iter->end; i++)
        node = node->next;
    iter->end = iter->node;
}

static inline long JOIN(I, distance)(I *iter, I *other)
{
    long d = 0;
    if (UNLIKELY(iter == other || iter->node == other->node))
        return 0;
    B *i = iter->node;
    for (; i != NULL && i != other->node; d++)
        i = i->next;
    if (i == other->node)
        return d;
    // other before self, negative result. in STL undefined
    return -1L;
}

static inline size_t JOIN(I, index)(I *iter)
{
    I begin = JOIN(A, begin)(iter->container);
    return (size_t)JOIN(I, distance)(&begin, iter);
}

static inline size_t JOIN(I, distance_range)(I *range)
{
    size_t d = 0;
    B *n = range->node;
    if (n == range->end)
        return 0;
    for (; n != NULL && n != range->end; d++)
        n = n->next;
    return d;
}

static inline void JOIN(A, disconnect)(A *self, B *node)
{
    ASSERT(self->size);
    if (node == self->tail)
        self->tail = self->tail->prev;
    if (node == self->head)
        self->head = self->head->next;
    if (node->prev)
        node->prev->next = node->next;
    if (node->next)
        node->next->prev = node->prev;
    node->prev = node->next = NULL;
    self->size--;
}

// forwards for algorithm
static inline A JOIN(A, copy)(A *self);
static inline A JOIN(A, init_from)(A *copy);
static inline void JOIN(A, push_back)(A *self, T value);
static inline I JOIN(A, find)(A *self, T key);
static inline A *JOIN(A, move_range)(I *range, A *out);

#include <ctl/bits/container.h>

static inline I JOIN(I, iter)(A *self, B *node)
{
    static I zero;
    I iter = zero;
    iter.node = node;
    if (LIKELY(node))
        iter.ref = &node->value;
    // iter.end = NULL;
    iter.container = self;
    //iter.vtable = { JOIN(I, next), JOIN(I, ref), JOIN(I, done) };
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
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    self.compare = copy->compare;
    self.equal = copy->equal;
    return self;
}

static inline B *JOIN(B, init)(T value)
{
    B *self = (B *)malloc(sizeof(B));
    self->prev = self->next = NULL;
    self->value = value;
    return self;
}

static inline void JOIN(A, connect_before)(A *self, B *position, B *node)
{
    if (JOIN(A, empty)(self))
    {
        self->head = self->tail = node;
        self->size++;
    }
    else if (LIKELY(self->size < JOIN(A, max_size)()))
    {
        node->next = position;
        node->prev = position->prev;
        if (position->prev)
            position->prev->next = node;
        position->prev = node;
        if (position == self->head)
            self->head = node;
        self->size++;
    }
    /* error handling? silent ignore or stderr or assert or customizable. */
    else
    {
        ASSERT(!"list max_size exceeded");
        // fprintf (stderr, "list max_size exceeded");
    }
}

static inline void JOIN(A, push_front)(A *self, T value)
{
    B *node = JOIN(B, init)(value);
    JOIN(A, connect_before)(self, self->head, node);
}

static inline void JOIN(A, transfer_before)(A *self, A *other, B *position, B *node)
{
    if (LIKELY(other->size))
        JOIN(A, disconnect)(other, node);
    JOIN(A, connect_before)(self, position, node);
}

static inline void JOIN(A, erase_node)(A *self, B *node)
{
    if (LIKELY(self->size))
        JOIN(A, disconnect)(self, node);
    if (self->free)
        self->free(&node->value);
    free(node);
}

static inline void JOIN(A, erase)(I *it)
{
    if (LIKELY(it->node))
        JOIN(A, erase_node)(it->container, it->node);
}

static inline void JOIN(A, pop_back)(A *self)
{
    JOIN(A, erase_node)(self, self->tail);
}

static inline void JOIN(A, pop_front)(A *self)
{
    JOIN(A, erase_node)(self, self->head);
}

static inline I *JOIN(A, insert)(I *pos, T value)
{
    B *node = JOIN(B, init)(value);
    JOIN(A, connect_before)(pos->container, pos->node, node);
    pos->node = node;
    pos->ref = &node->value;
    return pos;
}

static inline void JOIN(A, clear)(A *self)
{
    while (!JOIN(A, empty)(self))
        JOIN(A, pop_back)(self);
}

static inline void JOIN(A, free)(A *self)
{
    JOIN(A, compare_fn) *compare = &self->compare;
    JOIN(A, compare_fn) *equal = &self->equal;
    JOIN(A, clear)(self);
    *self = JOIN(A, init)();
    self->compare = *compare;
    self->equal = *equal;
}

static inline void JOIN(A, connect_after)(A *self, B *position, B *node)
{
    if (JOIN(A, empty)(self))
    {
        self->head = self->tail = node;
        self->size += 1;
    }
    else if (LIKELY(self->size < JOIN(A, max_size)()))
    {
        node->prev = position;
        node->next = position->next;
        if (position->next)
            position->next->prev = node;
        position->next = node;
        if (position == self->tail)
            self->tail = node;
        self->size += 1;
    }
    /* error handling? silent ignore or stderr or assert or customizable. */
    else
    {
        ASSERT(!"list max_size exceeded");
        // fprintf (stderr, "list max_size exceeded");
    }
}

static inline void JOIN(A, push_back)(A *self, T value)
{
    B *node = JOIN(B, init)(value);
    JOIN(A, connect_after)(self, self->tail, node);
}

static inline void JOIN(A, resize)(A *self, size_t size, T value)
{
    if (LIKELY(size != self->size && size < JOIN(A, max_size)()))
        for (size_t i = 0; size != self->size; i++)
            (size < self->size) ? JOIN(A, pop_back)(self) : JOIN(A, push_back)(self, self->copy(&value));
    if (self->free)
        self->free(&value);
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init_from)(self);
    for (B *node = self->head; node; node = node->next)
        JOIN(A, push_back)(&other, self->copy(&node->value));
    return other;
}

static inline void JOIN(A, assign)(A *self, size_t size, T value)
{
    JOIN(A, resize)(self, size, self->copy(&value));
    size_t i = 0;
    list_foreach_ref(A, self, it)
    {
#ifndef POD
        if (self->free)
            self->free(it.ref);
#endif
        *it.ref = self->copy(&value);
        i++;
    }
    FREE_VALUE(self, value);
}

static inline void JOIN(A, reverse)(A *self)
{
    if (self->size < 2)
        return;
    B *tail = self->tail;
    B *head = self->head;
    B *node = self->head;
    while (node)
    {
        B *next = node->next;
        B *prev = node->prev;
        node->prev = next;
        node->next = prev;
        node = next;
    }
    self->tail = head;
    self->head = tail;
}

static inline size_t JOIN(A, remove)(A *self, T value)
{
    size_t erased = 0;
    B *node = self->head;
    while (node)
    {
        B *next = node->next;
        if (JOIN(A, _equal)(self, &node->value, &value))
        {
            JOIN(A, erase_node)(self, node);
            erased++;
        }
        node = next;
    }
    FREE_VALUE(self, value);
    return erased;
}

static inline I *JOIN(A, emplace)(I *pos, T *value)
{
    A *self = pos->container;
    B *node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_before)(self, pos->node, node);
    JOIN(I, next)(pos);
    return pos;
}

static inline B *JOIN(A, emplace_front)(A *self, T *value)
{
    B *node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_before)(self, self->head, node);
    // FIXME return iter
    return self->head;
}

static inline B *JOIN(A, emplace_back)(A *self, T *value)
{
    B *node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_after)(self, self->tail, node);
    // FIXME return iter
    return self->tail;
}

static inline I *JOIN(A, insert_count)(I *pos, size_t count, T value)
{
    A *self = pos->container;
    B *node = NULL;
    for (size_t i = 0; i < count; i++)
    {
        node = JOIN(B, init)(self->copy(&value));
        if (pos->node)
            JOIN(A, connect_before)(self, pos->node, node);
        else
            JOIN(A, connect_after)(self, self->tail, node);
    }
    if (self->free)
        self->free(&value);
    if (LIKELY(count && node))
    {
        pos->node = node;
        pos->ref = &node->value;
    }
    return pos;
}

static inline I *JOIN(A, insert_range)(I *pos, I *range)
{
    B *node = range->node;
    A *self = pos->container;
    if (!pos->node)
    {
        while (node != range->end)
        {
            JOIN(A, connect_after)(self, self->tail, JOIN(B, init)(self->copy(&node->value)));
            node = node->next;
        }
    }
    else
        while (node != range->end)
        {
            JOIN(A, connect_before)(self, pos->node, JOIN(B, init)(self->copy(&node->value)));
            node = node->next;
        }
    if (node)
    {
        pos->node = node;
        pos->ref = &node->value;
    }
    return pos;
}

static inline void JOIN(A, insert_generic)(I *pos, GI *range)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;

    A *self = pos->container;
    if (range->container == self)
        return;
    if (!pos->node)
    {
        while (!done(range))
        {
            JOIN(A, connect_after)(self, self->tail, JOIN(B, init)(self->copy(ref(range))));
            next(range);
        }
    }
    else
    {
        while (!done(range))
        {
            JOIN(A, connect_before)(self, pos->node, JOIN(B, init)(self->copy(ref(range))));
            next(range);
        }
    }
}

static inline size_t JOIN(A, remove_if)(A *self, int _match(T *))
{
    if (!self->size)
        return 0;
    size_t erases = 0;
    B *node = self->head;
    while (node)
    {
        B *next = node->next;
        if (_match(&node->value))
        {
            JOIN(A, erase_node)(self, node);
            erases++;
        }
        node = next;
    }
    return erases;
}

static inline size_t JOIN(A, erase_if)(A *self, int _match(T *))
{
    return JOIN(A, remove_if)(self, _match);
}

static inline I *JOIN(A, erase_range)(I *range)
{
    B *node = range->node;
    A *self = range->container;
    while (node != range->end)
    {
        B *next = node->next;
        JOIN(A, erase_node)(self, node);
        node = next;
    }
    return range;
}

static inline void JOIN(A, erase_generic)(A* self, GI *range)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;

    if (range->container == self)
        return;
    while (!done(range))
    {
        JOIN(A, remove)(self, *ref(range));
        next(range);
    }
}

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline void JOIN(A, splice)(I *pos, A *other)
{
    A *self = pos->container;
    if (self->size == 0 && pos->node == NULL)
        JOIN(A, swap)(self, other);
    else if (other->size)
    {
        B *node = other->head;
        B *next;
        while (node)
        {
            next = node->next;
            JOIN(A, transfer_before)(self, other, pos->node, node);
            node = next;
        }
    }
}

static inline void JOIN(A, splice_it)(I *pos, I *first2)
{
    A *self = pos->container;
    A *other = first2->container;
    if (UNLIKELY(self->size == 0 && pos->node == NULL && first2->node == other->head))
        JOIN(A, swap)(self, other);
    else if (LIKELY(first2->node))
        JOIN(A, transfer_before)(self, other, pos->node, first2->node);
}

static inline void JOIN(A, splice_range)(I *pos, I *range2)
{
    A *self = pos->container;
    A *other = range2->container;
    if (UNLIKELY(self->size == 0 && pos->node == NULL && range2->node == other->head && range2->end == NULL))
        JOIN(A, swap)(self, other);
    else if (other->size)
    {
        B *node = range2->node;
        B *next;
        while (node != range2->end)
        {
            next = node->next;
            JOIN(A, transfer_before)(self, other, pos->node, node);
            node = next;
        }
    }
}

// only needed for merge and move
static inline void JOIN(A, transfer_after)(A *self, A *other, B *position, B *node)
{
    ASSERT(other->size);
    JOIN(A, disconnect)(other, node);
    JOIN(A, connect_after)(self, position, node);
}

// move elements from range to the end of out
static inline A *JOIN(A, move_range)(I *range, A *out)
{
    A *self = range->container;
    B *node = range->node;
    while (node != range->end)
    {
        B *next = node->next;
        JOIN(A, transfer_after)(out, self, out->tail, node);
        node = next;
    }
    return out;
}

static inline void JOIN(A, merge)(A *self, A *other)
{
    ASSERT(self->compare || !"compare undefined");
    if (JOIN(A, empty)(self))
        JOIN(A, swap)(self, other);
    else
    {
        for (B *node = self->head; node; node = node->next)
            while (!JOIN(A, empty)(other) && !self->compare(&node->value, &other->head->value))
                JOIN(A, transfer_before)(self, other, node, other->head);
        // Remainder.
        while (!JOIN(A, empty)(other))
            JOIN(A, transfer_after)(self, other, self->tail, other->head);
    }
}

static inline void JOIN(A, sort)(A *self)
{
    if (LIKELY(self->size > 1))
    {
        A carry = JOIN(A, init_from)(self);
        A temp[64];
        for (size_t i = 0; i < len(temp); i++)
            temp[i] = JOIN(A, init_from)(self);
        A *fill = temp;
        A *counter = NULL;
        do
        {
            JOIN(A, transfer_before)(&carry, self, carry.head, self->head);
            for (counter = temp; counter != fill && !JOIN(A, empty)(counter); counter++)
            {
                JOIN(A, merge)(counter, &carry);
                JOIN(A, swap)(&carry, counter);
            }
            JOIN(A, swap)(&carry, counter);
            if (counter == fill)
                fill++;
        } while (!JOIN(A, empty)(self));
        for (counter = temp + 1; counter != fill; counter++)
            JOIN(A, merge)(counter, counter - 1);
        JOIN(A, swap)(self, fill - 1);
    }
}

static inline I JOIN(A, unique_range)(I *range)
{
    JOIN(A, it) prev = *range;
    if (JOIN(I, done)(range))
        return prev;
    JOIN(I, next)(range);
    A *self = range->container;
    while (range->node != range->end)
    {
        B *next = range->node->next;
        range->ref = &range->node->value;
        if (JOIN(A, _equal)(self, prev.ref, range->ref))
            JOIN(A, erase)(range);
        prev.node = prev.node->next;
        prev.ref = &prev.node->value;
        range->node = next;
    }
    JOIN(I, next)(&prev);
    return prev;
}

static inline void /* I, B* ?? */
    JOIN(A, unique)(A *self)
{
    list_foreach_ref(A, self, it)
    {
        B *next = JOIN(B, next)(it.node);
        if (next != NULL && JOIN(A, _equal)(self, it.ref, &next->value))
        {
            B *n = it.node->next;
            JOIN(A, erase_node)(self, it.node);
            it.node = n;
        }
    }
}

static inline I JOIN(A, find)(A *self, T key)
{
    list_foreach_ref(A, self, it) if (JOIN(A, _equal)(self, it.ref, &key)) return it;
    return JOIN(A, end)(self);
}

#undef POD
#undef NOT_INTEGRAL
#undef T
#undef A
#undef B
#undef I
#undef GI
#undef CTL_LIST
