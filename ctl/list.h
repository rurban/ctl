/* List containers are implemented as doubly-linked lists
   SPDX-License-Identifier: MIT
 */

#ifndef T
#error "Template type T undefined for <ctl/list.h>"
#endif

#define CTL_LIST
#define A JOIN(list, T)
#define B JOIN(A, node)
#ifndef C
# define C list
#endif
#define I JOIN(A, it)
#undef IT
#define IT B*

#include <ctl/ctl.h>

typedef struct B
{
    struct B* next;
    struct B* prev;
    T value;
} B;

typedef struct A
{
    B* head;
    B* tail;
    size_t size;
    void (*free)(T*);
    T (*copy)(T*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*);
} A;

typedef struct I
{
    B node;
    A* container;
    uint32_t tag;
} I;

typedef int (*JOIN(A, compare_fn))(T*, T*);

#include <ctl/bits/iterators.h>

static inline T*
JOIN(A, front)(A* self)
{
    return self->head ? &self->head->value : NULL;
}

static inline T*
JOIN(A, back)(A* self)
{
    return self->tail ? &self->tail->value : NULL;
}

#undef _list_begin_it
#define _list_begin_it JOIN(JOIN(_list, T), begin_it)
#undef _list_end_it
#define _list_end_it JOIN(JOIN(_list, T), end_it)

#ifdef __cplusplus
static I _list_begin_it = {};
static I _list_end_it = {};
#else
static I _list_begin_it = {0};
static I _list_end_it = {0};
#endif

static inline B*
JOIN(A, begin)(A* self)
{
    I *iter = &_list_begin_it;
    if (self->head)
        iter->node = *self->head;
    iter->container = self;
#ifdef DEBUG
    iter->tag = CTL_LIST_TAG;
#endif
    return (B*)iter;
}

static inline B*
JOIN(A, end)(A* self)
{
    I *iter = &_list_end_it;
    iter->container = self;
#ifdef DEBUG
    iter->tag = CTL_LIST_TAG;
#endif
    return (B*)iter;
}

// expand the iter to a node. only valid for begin/end, before a foreach loop.
static inline I*
JOIN(I, iter)(B* self)
{
    I* iter = (I*)self;
    CHECK_TAG(iter, 0)
    return iter;
}

static inline int
JOIN(I, done)(I* iter)
{
    return iter != NULL || iter->node.next == NULL;
}

static inline B*
JOIN(B, next)(B* node)
{
    return node->next;
}

static inline B*
JOIN(I, next)(B* node)
{
    return node->next;
}

static inline T*
JOIN(I, ref)(B* node)
{
    return &node->value;
}

static inline I* JOIN(I, advance)(I* self, long i);

// the only way to keep the iter struct intact
static inline I*
JOIN(I, advance)(I* iter, long i)
{
    A* a = iter->container;
    B* node = &iter->node;
    if (i < 0)
    {
        CHECK_TAG(iter, NULL);
        if ((size_t)-i > a->size)
            return NULL;
        return JOIN(I, advance)(iter, a->size + i);
    }
    for(long j = 0; node != NULL && j < i; j++)
        node = node->next;
    iter->node = *node;
    return iter;
}

static inline long
JOIN(I, distance)(B* self, B* other)
{
    long d = 0;
    if (self == other)
        return 0;
    B* i = self;
    for(; i != NULL && i != other; d++)
        i = i->next;
    if (i == other)
        return d;
    // other before self, negative result
    I* iter2 = (I*)other;
    CHECK_TAG(iter2, 0)
    d = (long)iter2->container->size;
    for(; other != NULL && other != self; d--)
        other = other->next;
    return other ? -d : LONG_MAX;
}

static inline void
JOIN(A, disconnect)(A* self, B* node)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (self->size);
#endif
    if(node == self->tail) self->tail = self->tail->prev;
    if(node == self->head) self->head = self->head->next;
    if(node->prev) node->prev->next = node->next;
    if(node->next) node->next->prev = node->prev;
    node->prev = node->next = NULL;
    self->size--;
}

#include <ctl/bits/container.h>

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

static inline A
JOIN(A, init_from)(A* copy)
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

static inline B*
JOIN(B, init)(T value)
{
    B* self = (B*) malloc(sizeof(B));
    self->prev = self->next = NULL;
    self->value = value;
    return self;
}

static inline void
JOIN(A, connect_before)(A* self, B* position, B* node)
{
    if(JOIN(A, empty)(self))
    {
        self->head = self->tail = node;
        self->size++;
    }
    else
    if (self->size < JOIN(A, max_size)())
    {
        node->next = position;
        node->prev = position->prev;
        if(position->prev)
            position->prev->next = node;
        position->prev = node;
        if(position == self->head)
            self->head = node;
        self->size++;
    }
    /* error handling? silent ignore or stderr or assert or customizable.
    else
        assert (0 || "list size exceeded");
        fprintf (stderr, "list size exceeded");
    */
}

static inline void
JOIN(A, push_front)(A* self, T value)
{
    B* node = JOIN(B, init)(value);
    JOIN(A, connect_before)(self, self->head, node);
}

static inline void
JOIN(A, transfer_before)(A* self, A* other, B* position, B* node)
{
    JOIN(A, disconnect)(other, node);
    JOIN(A, connect_before)(self, position, node);
}

static inline void
JOIN(A, erase)(A* self, B* node)
{
    JOIN(A, disconnect)(self, node);
    FREE_VALUE(self, node->value);
    free(node);
}

static inline void
JOIN(A, pop_back)(A* self)
{
    JOIN(A, erase)(self, self->tail);
}

static inline void
JOIN(A, pop_front)(A* self)
{
    JOIN(A, erase)(self, self->head);
}

static inline B*
JOIN(A, insert)(A* self, B* pos, T value)
{
    B* node = JOIN(B, init)(value);
    JOIN(A, connect_before)(self, pos, node);
    return node;
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
    JOIN(A, compare_fn) *compare = &self->compare;
    JOIN(A, compare_fn) *equal = &self->equal;
    JOIN(A, clear)(self);
    *self = JOIN(A, init)();
    self->compare = *compare;
    self->equal = *equal;
}

static inline void
JOIN(A, connect_after)(A* self, B* position, B* node)
{
    if(JOIN(A, empty)(self))
    {
        self->head = self->tail = node;
        self->size += 1;
    }
    else
    if (self->size < JOIN(A, max_size)())
    {
        node->prev = position;
        node->next = position->next;
        if(position->next)
            position->next->prev = node;
        position->next = node;
        if(position == self->tail)
            self->tail = node;
        self->size += 1;
    }
    /* error handling? silent ignore or stderr or assert or customizable.
    else
        assert (0 || "list size exceeded");
        fprintf (stderr, "list size exceeded");
    */
}

static inline void
JOIN(A, push_back)(A* self, T value)
{
    B* node = JOIN(B, init)(value);
    JOIN(A, connect_after)(self, self->tail, node);
}

static inline void
JOIN(A, resize)(A* self, size_t size, T value)
{
    if(size != self->size && size < JOIN(A, max_size)())
        for(size_t i = 0; size != self->size; i++)
            (size < self->size)
                ? JOIN(A, pop_back)(self)
                : JOIN(A, push_back)(self, self->copy(&value));
    FREE_VALUE(self, value);
}

static inline A
JOIN(A, copy)(A* self)
{
    A other = JOIN(A, init_from)(self);
    for(B* node = self->head; node; node = node->next)
        JOIN(A, push_back)(&other, self->copy(&node->value));
    return other;
}

static inline void
JOIN(A, assign)(A* self, size_t size, T value)
{
    JOIN(A, resize)(self, size, self->copy(&value));
    size_t i = 0;
    list_foreach_ref(A, T, self, it, ref)
    {
#ifndef POD
        if(self->free)
            self->free(ref);
#endif
        *ref = self->copy(&value);
        i++;
    }
    FREE_VALUE(self, value);
}

static inline void
JOIN(A, reverse)(A* self)
{
    list_foreach(A, self, it)
    {
        B* next = it->next;
        B* prev = it->prev;
        it->prev = next;
        it->next = prev;
    }
    B* tail = self->tail;
    B* head = self->head;
    self->tail = head;
    self->head = tail;
}

static inline size_t
JOIN(A, remove)(A* self, T* value)
{
    size_t erased = 0;
    list_foreach_ref(A, T, self, it, ref)
        if(JOIN(A, _equal)(self, ref, value))
        {
            JOIN(A, erase)(self, it);
            erased += 1;
        }
    return erased;
}

static inline B*
JOIN(A, emplace)(A* self, B* pos, T* value) {
    B* node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_before)(self, pos, node);
    return pos->next;
}

static inline B*
JOIN(A, emplace_front)(A* self, T* value) {
    B* node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_before)(self, self->head, node);
    return self->head;
}

static inline B*
JOIN(A, emplace_back)(A* self, T* value) {
    B* node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_after)(self, self->tail, node);
    return self->tail;
}

static inline B*
JOIN(A, insert_count)(A* self, B* pos, size_t count, T value)
{
    B* node = JOIN(B, init)(value);
    for (size_t i=0; i < count; i++)
        JOIN(A, connect_before)(self, pos, node);
    return node;
}

#ifdef DEBUG

static inline B*
JOIN(A, insert_range)(A* self, B* pos, B* first, B* last)
{
    B* node = NULL;
    for(B* it = first; it < last; it++)
    {
        node = JOIN(B, init)(it->value);
        JOIN(A, connect_before)(self, pos, node);
    }
    return node;
}

#endif

static inline size_t
JOIN(A, remove_if)(A* self, int _match(T*))
{
    size_t erases = 0;
    list_foreach_ref(A, T, self, it, ref)
        if(_match(ref))
        {
            JOIN(A, erase)(self, it);
            erases++;
        }
    return erases;
}

static inline size_t
JOIN(A, erase_if)(A* self, int _match(T*))
{
    return JOIN(A, remove_if)(self, _match);
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline void
JOIN(A, splice)(A* self, B* pos, A* other)
{
    if(self->size == 0 && pos == NULL)
        JOIN(A, swap)(self, other);
    else
    {
        list_foreach(A, other, it)
            JOIN(A, transfer_before)(self, other, pos, it);
    }
}

// only needed for merge
static inline void
JOIN(A, transfer_after)(A* self, A* other, B* position, B* node)
{
    JOIN(A, disconnect)(other, node);
    JOIN(A, connect_after)(self, position, node);
}

#ifdef DEBUG
static inline void
JOIN(A, splice_it)(A* self, B* pos, A* other, B* other_pos)
{
    if(self->size == 0 && pos == NULL)
        JOIN(A, swap)(self, other);
    else
    {
        //??
        JOIN(A, transfer_before)(self, other, pos, other_pos);
    }
}

static inline void
JOIN(A, splice_range)(A* self, B* pos, A* other, B* other_first, B* other_last)
{
    if(self->size == 0 && pos == NULL)
        JOIN(A, swap)(self, other);
    else
    {
        // FIXME util other_last
        (void) other_last;
        JOIN(A, transfer_before)(self, other, pos, other_first);
    }
}

#endif

static inline void
JOIN(A, merge)(A* self, A* other)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->compare || !"compare undefined");
#endif
    if(JOIN(A, empty)(self))
        JOIN(A, swap)(self, other);
    else
    {
        for(B* node = self->head; node; node = node->next)
            while(!JOIN(A, empty)(other) && self->compare(&node->value, &other->head->value))
                JOIN(A, transfer_before)(self, other, node, other->head);
        // Remainder.
        while(!JOIN(A, empty)(other))
            JOIN(A, transfer_after)(self, other, self->tail, other->head);
    }
}

static inline void
JOIN(A, sort)(A* self)
{
    if(LIKELY(self->size > 1))
    {
        A carry = JOIN(A, init_from)(self);
        A temp[64];
        for(size_t i = 0; i < len(temp); i++)
            temp[i] = JOIN(A, init_from)(self);
        A* fill = temp;
        A* counter = NULL;
        do
        {
            JOIN(A, transfer_before)(&carry, self, carry.head, self->head);
            for(counter = temp; counter != fill && !JOIN(A, empty)(counter); counter++)
            {
                JOIN(A, merge)(counter, &carry);
                JOIN(A, swap)(&carry, counter);
            }
            JOIN(A, swap)(&carry, counter);
            if(counter == fill)
                fill++;
        }
        while(!JOIN(A, empty)(self));
        for(counter = temp + 1; counter != fill; counter++)
            JOIN(A, merge)(counter, counter - 1);
        JOIN(A, swap)(self, fill - 1);
    }
}

static inline void /* B* ?? */
JOIN(A, unique)(A* self)
{
    list_foreach_ref(A, T, self, it, ref)
    {
        B* node = (B*)it;
        if(node->next && JOIN(A, _equal)(self, ref, &node->next->value))
            JOIN(A, erase)(self, it);
    }
}

static inline B*
JOIN(A, find)(A* self, T key)
{
    list_foreach_ref(A, T, self, it, ref)
        if(JOIN(A, _equal)(self, ref, &key))
            return it;
    return NULL;
}

#undef POD
#undef NOT_INTEGRAL
#undef T
#undef A
#undef B
#undef C
#undef I
#undef CTL_LIST
