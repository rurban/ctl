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
//#ifndef C
//# define C list
//#endif
//#undef IT
//#define IT B*

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
    B *node;
    T* ref;
    B* end;
    A* container;
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

static inline I
JOIN(A, begin)(A* self)
{
    I iter = _list_begin_it;
    iter.node = self->head;
    iter.end = NULL;
    iter.ref = JOIN(A, front)(self);
    iter.container = self;
    return iter;
}

static inline I
JOIN(A, end)(A* self)
{
    I iter = _list_end_it;
    iter.node = NULL;
    iter.ref = NULL;
    iter.end = NULL;
    iter.container = self;
    return iter;
}

static inline int
JOIN(I, done)(I* iter)
{
    return iter->node == iter->end;
}

static inline int
JOIN(I, isend)(I* iter, I* last)
{
    return iter->end == last->node;
}

static inline B*
JOIN(B, next)(B* node)
{
    return node->next;
}

static inline void
JOIN(I, next)(I* iter)
{
    iter->node = iter->node->next;
    if (iter->node)
        iter->ref = &iter->node->value;
}

static inline void
JOIN(I, range)(I* begin, I* end)
{
    begin->end = end->node;
}

static inline T*
JOIN(I, ref)(I* iter)
{
    return &iter->node->value;
}

static inline I* JOIN(I, advance)(I* self, long i);

// the only way to keep the iter struct intact
static inline I*
JOIN(I, advance)(I* iter, long i)
{
    A* a = iter->container;
    B* node = iter->node;
    if (i < 0)
    {
        if ((size_t)-i > a->size)
            return NULL;
        return JOIN(I, advance)(iter, a->size + i);
    }
    for(long j = 0; node != NULL && j < i; j++)
        node = node->next;
    iter->node = node;
    return iter;
}

static inline long
JOIN(I, distance)(I* iter, I* other)
{
    long d = 0;
    if (iter == other || iter->node == other->node)
        return 0;
    B* i = iter->node;
    for(; i != NULL && i != other->node; d++)
        i = i->next;
    if (i == other->node)
        return d;
    // other before self, negative result
    d = other->container->size;
    for(; other->node != NULL && other->node != iter->node; d--)
        other->node = other->node->next;
    return other->node ? -d : LONG_MAX;
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
JOIN(A, erase_node)(A* self, B* node)
{
    JOIN(A, disconnect)(self, node);
    FREE_VALUE(self, node->value);
    free(node);
}

static inline void
JOIN(A, erase)(A* self, I* it)
{
    JOIN(A, erase_node)(self, it->node);
}

static inline void
JOIN(A, pop_back)(A* self)
{
    JOIN(A, erase_node)(self, self->tail);
}

static inline void
JOIN(A, pop_front)(A* self)
{
    JOIN(A, erase_node)(self, self->head);
}

static inline I*
JOIN(A, insert)(A* self, I* pos, T value)
{
    B* node = JOIN(B, init)(value);
    JOIN(A, connect_before)(self, pos->node, node);
    return pos;
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
    list_foreach_ref(A, self, it)
    {
#ifndef POD
        if(self->free)
            self->free(it.ref);
#endif
        *it.ref = self->copy(&value);
        i++;
    }
    FREE_VALUE(self, value);
}

static inline void
JOIN(A, reverse)(A* self)
{
    list_foreach(A, self, it)
    {
        B* next = it.node->next;
        B* prev = it.node->prev;
        it.node->prev = next;
        it.node->next = prev;
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
    list_foreach_ref(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, value))
        {
            B* next = it.node->next;
            JOIN(A, erase_node)(self, it.node);
            it.node = next;
            erased += 1;
        }
    return erased;
}

static inline I*
JOIN(A, emplace)(A* self, I* pos, T* value) {
    B* node = JOIN(B, init)(self->copy(value));
    JOIN(A, connect_before)(self, pos->node, node);
    JOIN(I, next)(pos);
    return pos;
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

static inline I*
JOIN(A, insert_count)(A* self, I* pos, size_t count, T value)
{
    B* node = JOIN(B, init)(value);
    for (size_t i=0; i < count; i++)
        JOIN(A, connect_before)(self, pos->node, node);
    return pos;
}

#ifdef DEBUG

static inline I*
JOIN(A, insert_range)(A* self, I* pos, I* first, I* last)
{
    B* node = NULL;
    for(JOIN(A, it) it = *first; it.node != last->node; JOIN(I, next)(&it))
    {
        node = JOIN(B, init)(*it.ref);
        JOIN(A, connect_before)(self, pos->node, node);
    }
    return pos;
}

#endif

static inline size_t
JOIN(A, remove_if)(A* self, int _match(T*))
{
    size_t erases = 0;
    list_foreach_ref(A, self, it)
        if(_match(it.ref))
        {
            B* next = it.node->next;
            JOIN(A, erase_node)(self, it.node);
            it.node = next;
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
JOIN(A, splice)(A* self, I* pos, A* other)
{
    if(self->size == 0 && pos->node == NULL)
        JOIN(A, swap)(self, other);
    else
    {
        list_foreach(A, other, it)
            JOIN(A, transfer_before)(self, other, pos->node, it.node);
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
JOIN(A, splice_it)(A* self, I* pos, A* other, I* other_pos)
{
    if(self->size == 0 && pos == NULL)
        JOIN(A, swap)(self, other);
    else
    {
        //??
        JOIN(A, transfer_before)(self, other, pos->node, other_pos->node);
    }
}

static inline void
JOIN(A, splice_range)(A* self, I* pos, I* other_first, I* other_last)
{
    if(self->size == 0 && pos == NULL)
        JOIN(A, swap)(self, other_first->container);
    else
    {
        // FIXME util other_last
        (void) other_last;
        JOIN(A, transfer_before)(self, other_first->container, pos->node, other_first->node);
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

static inline void /* I, B* ?? */
JOIN(A, unique)(A* self)
{
    list_foreach_ref(A, self, it)
        if(it.node->next != NULL && JOIN(A, _equal)(self, it.ref, &it.node->next->value))
        {
            B* next = it.node->next;
            JOIN(A, erase_node)(self, it.node);
            it.node = next;
        }
}

static inline I
JOIN(A, find)(A* self, T key)
{
    list_foreach_ref(A, self, it)
        if(JOIN(A, _equal)(self, it.ref, &key))
            return it;
    return JOIN(A, end)(self);
}

#undef POD
#undef NOT_INTEGRAL
#undef T
#undef A
#undef B
#undef C
#undef I
#undef CTL_LIST
