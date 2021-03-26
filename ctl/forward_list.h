/* Forward lists are implemented as singly-linked lists.
   All but length and has_cycle are not cycle-safe. */

#ifndef T
#error "Template type T undefined for <ctl/forward_list.h>"
#endif

#define CTL_SLIST
#define A JOIN(slist, T)
#define B JOIN(A, node)
#define I JOIN(A, it)
#define GI JOIN(A, it)

#include <assert.h>
#include <ctl/ctl.h>

typedef struct B
{
    struct B *next;
    T value;
} B;

typedef struct A
{
    B *head;
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *);
    int (*equal)(T *, T *);
} A;

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_B_ITER_FIELDS;
} I;

#include <ctl/bits/iterators.h>

typedef int (*JOIN(A, compare_fn))(T *, T *);
static inline T JOIN(A, implicit_copy)(T *self);

static inline B *JOIN(B, init)(T value)
{
    B *self = (B *)malloc(sizeof(B));
    self->next = NULL;
    self->value = value;
    return self;
}

static inline B* JOIN(A, tail)(A *self)
{
    B *node = self->head;
    if (UNLIKELY(!node))
        return NULL;
    while (node->next)
        node = node->next;
    return node;
}

static inline int JOIN(A, empty)(A *self)
{
    return self->head == NULL;
}

static inline T *JOIN(A, front)(A *self)
{
    return &self->head->value;
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

static inline void JOIN(I, range)(I *first, I *last)
{
    last->end = first->end = last->node;
}

static inline void JOIN(I, set_done)(I *iter)
{
    iter->node = iter->end;
}

static inline void JOIN(I, set_pos)(I *iter, I *other)
{
    iter->node = other->node;
}

static inline void JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->node;
}

static inline T *JOIN(I, ref)(I *iter)
{
    return &iter->node->value;
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
        if (LIKELY(iter->node))
            iter->ref = &iter->node->value;
    }
}

static inline I *JOIN(I, advance)(I *iter, long i)
{
    //A *a = iter->container;
    B *node = iter->node;
    if (UNLIKELY(i < 0))
        return NULL;
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
    if (node)
        for (long i = 0; i < n && node != iter->end; i++)
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

// not cycle-safe! would need two fingers
static inline size_t JOIN(A, size)(A *self)
{
    size_t size = 0;
    for (B *n = self->head; n; size++)
        n = n->next;
    return size;
}

// forwards for algorithm
static inline A JOIN(A, copy)(A *self);
static inline A JOIN(A, init_from)(A *copy);
static inline void JOIN(A, push_front)(A *self, T value);
static inline I JOIN(A, find)(A *self, T key);
static inline void JOIN(A, merge)(A *self, A* other);
static inline A *JOIN(A, move_range)(I *range, A *out);
static inline A* JOIN(A, copy_range)(GI *range, A *out);

#include <ctl/bits/container.h>

static inline I JOIN(I, iter)(A *self, B *begin)
{
    static I zero;
    I iter = zero;
    iter.node = begin;
    if (LIKELY(begin))
        iter.ref = &begin->value;
    iter.container = self;
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
    A self = JOIN(A, init)();
    self.compare = copy->compare;
    self.equal = copy->equal;
    return self;
}

static inline void JOIN(A, disconnect)(A *self, B *node)
{
    if (node == self->head)
        self->head = self->head->next;
    else
    {
        B *prev;
        for (B *tail = self->head; tail != node; prev = tail, tail = tail->next)
            ;
        if (prev->next) // == node
            prev->next = prev->next->next;
    }
}

static inline void JOIN(A, connect_before)(A *self, B *position, B *node)
{
    if (JOIN(A, empty)(self))
        self->head = node;
    else
    {
        node->next = position;
        if (position == self->head)
            self->head = node;
    }
}

static inline void JOIN(A, transfer_before)(A *self, A *other, B *position, B *node)
{
    JOIN(A, disconnect)(other, node);
    JOIN(A, connect_before)(self, position, node);
}

static inline void JOIN(A, push_front)(A *self, T value)
{
    B *node = JOIN(B, init)(value);
    JOIN(A, connect_before)(self, self->head, node);
}

static inline B* JOIN(B, erase_node)(A *self, B *node)
{
    assert(node);
    B *next = node->next;
    if (self->free)
        self->free(&node->value);
    free(node);
    return next;
}

// on node == NULL erase the head
static inline B* JOIN(A, erase_after)(A *self, B *node)
{
    if (!node)
    {
        if (!self->head)
            return NULL;
        self->head = JOIN(B, erase_node)(self, self->head);
        return self->head;
    }
    if (node->next)
        node->next = JOIN(B, erase_node)(self, node->next);
    return node;
}

// erase after, i.e. range->node stays
static inline void JOIN(A, erase_range)(I* range)
{
    A* self = range->container;
    B* node = range->node;
    while (node != NULL && node->next != range->end) // ensure not to erase_before
        node = JOIN(A, erase_after)(self, node);
}

static inline void JOIN(A, pop_front)(A *self)
{
    self->head = JOIN(B, erase_node)(self, self->head);
}

static inline void JOIN(B, insert_after)(B *position, T value)
{
    B* next = position->next;
    position->next = JOIN(B, init)(value);
    if (next)
        position->next->next = next;
}

static inline void JOIN(A, insert_after)(I *iter, T value)
{
    B* node = iter->node;
    if (!node)
        return;
    B* next = node->next;
    node->next = JOIN(B, init)(value);
    if (next)
        node->next->next = next;
}

// On !iter->node (aka before_begin()) and empty slist insert before. all other insert_after.
static inline void JOIN(A, insert_range)(I *iter, GI* range)
{
    A *self = iter->container;
    //A *other = range->container;
    void (*next2)(struct I*) = range->vtable.next;
    T* (*ref2)(struct I*) = range->vtable.ref;
    int (*done2)(struct I*) = range->vtable.done;
    B* node = iter->node;
    B* next;
    if (done2(range))
        return;
    next = node ? iter->node->next : self->head;
    if (!node) // before_begin() => push_front
    {
        self->head = node = JOIN(B, init)(self->copy(ref2(range)));
        next2(range);
    }
    while (!done2(range))
    {
        node->next = JOIN(B, init)(self->copy(ref2(range)));
        node = node->next;
        next2(range);
    }
    if (next)
        node->next = next;
}

static inline void JOIN(A, insert_generic)(I *iter, GI* range)
{
    JOIN(A, insert_range)(iter, range);
}

static inline void JOIN(A, clear)(A *self)
{
    while (!JOIN(A, empty)(self))
        JOIN(A, pop_front)(self);
}

static inline void JOIN(A, free)(A *self)
{
    JOIN(A, clear)(self);
    *self = JOIN(A, init_from)(self);
}

static inline bool JOIN(A, has_cycle)(A *self)
{
    B *slow, *fast;
    slow = fast = self->head;
    while (slow && fast && fast->next) {
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast) {
            return true;
        }
    }
    return false;
}

// cycle-safe. returns 0 if cycling.
static inline size_t JOIN(A, length)(A *self)
{
    size_t size = 0;
    B *slow, *fast;
    slow = fast = self->head;
    while (slow && fast && fast->next) {
        size++;
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast) {
            return 0;
        }
    }
    return size;
}

/* NOOP?
static inline void
JOIN(A, resize)(A* self, size_t size, T value)
{
    if (size < JOIN(A, max_size)())
    {
        size_t sz = 0;
        B *prev = NULL;
        for (B *node = self->head; node && sz < size; prev = node, node = node->next, sz++)
            ;
        if (size == sz || !prev)
            ;
        else if (size < sz)
            for (B *node = prev; node;)
            {
                B *next = node->next;
                if (self->free)
                    self->free(&node->value);
                free(node);
                node = next->next;
            }
        else
            for (size_t i = 0; size != i; i++)
                JOIN(A, insert_after)(self, prev, self->copy(&value));
    }
    if (self->free)
        self->free(&value);
}
*/

static inline void JOIN(A, swap)(A *self, A *other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline void JOIN(A, reverse_range)(I *range)
{
    if (range->node)
    {
        A* self = range->container;
        B *prev = NULL;
        B *cur = range->node;
        B *next = range->node;
        if (range->node != self->head)
            for (prev = self->head; prev->next != range->node; prev = prev->next)
                ;
        while (cur)
        {
            next = next->next;
            cur->next = prev;
            prev = cur;
            cur = next;
        }
        range->node = prev;
    }
}

static inline void JOIN(A, reverse)(A *self)
{
    B *cur = self->head;
    if (cur && cur->next)
    {
        B *prev = NULL;
        B *next = self->head;
        while (cur)
        {
            next = next->next;
            cur->next = prev;
            prev = cur;
            cur = next;
        }
        self->head = prev;
    }
}

static inline A JOIN(A, copy)(A *self)
{
    A other = JOIN(A, init)();
#if 0
    B *node = self->head;
    B* last;
    if (node)
        other.head = JOIN(B, init)(self->copy(&node->value));
    last = other.head;
    while (node)
    {
        last->next = JOIN(B, init)(self->copy(&node->value));
        node = node->next;
        last = last->next;
    }
#else    
    for (B *node = self->head; node; node = node->next)
        JOIN(A, push_front)(&other, self->copy(&node->value));
    JOIN(A, reverse)(&other);
#endif
    return other;
}

static inline void JOIN(A, assign)(A *self, size_t size, T value)
{
    B *node = self->head;
    size_t i = 0;
    for (; i < size; i++)
    {
        if (!node->next) // too short
            node->next = JOIN(B, init)(value);
        node = node->next;
    }
    // too large: shrink
    while (node)
        node = JOIN(A, erase_after)(self, node);
    if (self->free)
        self->free(&value);
}

static inline void JOIN(A, assign_generic)(A *self, GI *range)
{
    void (*next2)(struct I*) = range->vtable.next;
    T* (*ref2)(struct I*) = range->vtable.ref;
    int (*done2)(struct I*) = range->vtable.done;

    JOIN(A, clear)(self);
    if (!done2(range))
    {
        self->head = JOIN(B, init)(self->copy(ref2(range)));
        next2(range);
    }
    for (B* prev = self->head; !done2(range); next2(range))
    {
        // TODO: maybe skip clear and reuse most nodes, just change values
        prev->next = JOIN(B, init)(self->copy(ref2(range)));
        prev = prev->next;
    }
}

static inline size_t JOIN(A, remove)(A *self, T value)
{
    size_t erases = 0;
    B* prev = NULL;
    B* node = self->head;
    while (node)
    {
        if (self->equal(&node->value, &value))
        {
            node = JOIN(A, erase_after)(self, prev);
            erases += 1;
        }
        else
        {
            prev = node;
            node = node->next;
        }
    }
    if (self->free)
        self->free (&value);
    return erases;
}

static inline size_t JOIN(A, erase)(A *self, void *vvalue)
{
    T *value = (T *)vvalue;
    return JOIN(A, remove)(self, *value);
}

static inline size_t JOIN(A, remove_if)(A *self, int _match(T *))
{
    size_t erases = 0;
    B* node = self->head;
    B* prev = NULL;
    if (!node)
        return erases;
    while (node)
    {
        if (_match(&node->value))
        {
            node = JOIN(A, erase_after)(self, prev);
            erases++;
        }
        else
        {
            prev = node;
            node = node->next;
        }
    }
    return erases;
}

static inline size_t JOIN(A, erase_if)(A *self, int _match(T *))
{
    size_t erases = 0;
    foreach (A, self, it)
        if (_match(it.ref))
        {
            JOIN(A, erase_after)(self, it.node);
            erases += 1;
        }
    return erases;
}

static inline void JOIN(A, splice_after)(A *self, B *position, A *other)
{
    if (JOIN(A, empty)(self) && position == NULL)
        JOIN(A, swap)(self, other);
    else
        foreach (A, other, it)
            JOIN(A, transfer_before)(self, other, position, it.node);
}

static inline void JOIN(A, connect_after)(A *self, B *position, B *node)
{
    if (JOIN(A, empty)(self))
        self->head = node;
    else
    {
        node->next = position->next;
        position->next = node;
    }
}
static inline void JOIN(A, transfer_after)(A *self, A *other, B *position, B *node)
{
    JOIN(A, disconnect)(other, node);
    JOIN(A, connect_after)(self, position, node);
}

static inline void JOIN(A, broken_merge)(A *self, A *other)
{
    CTL_ASSERT_COMPARE;
    if (JOIN(A, empty)(self))
        JOIN(A, swap)(self, other);
    else
    {
        B *node = self->head;
        for (; node; node = node->next)
            while (!JOIN(A, empty)(other) && self->compare(&node->value, &other->head->value))
                JOIN(A, transfer_before)(self, other, node, other->head);
        // Remainder
        B *tail = node; // XXX
        while (!JOIN(A, empty)(other))
            JOIN(A, transfer_after)(self, other, tail, other->head);
    }
}

// FIXME
static inline int JOIN(A, equal)(A *self, A *other)
{
    if (JOIN(A, empty)(self))
        return JOIN(A, empty)(other);
    I a = JOIN(A, begin)(self);
    I b = JOIN(A, begin)(other);
    while (!JOIN(I, done)(&a) && !b.vtable.done(&b))
    {
        if (!self->equal(a.ref, b.vtable.ref(&b)))
            return 0;
        JOIN(I, next)(&a);
        b.vtable.next(&b);
    }
    return 1;
}

// FIXME
static inline void JOIN(A, fast_sort)(A *self)
{
    CTL_ASSERT_COMPARE;
    if (self->head && self->head->next) // more than 1 element
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
        } while (self->head);

        for (counter = temp + 1; counter != fill; counter++)
            JOIN(A, merge)(counter, counter - 1);
        JOIN(A, swap)(self, fill - 1);
    }
}

// split list into two halfs
static inline void JOIN(B, split_front_back)(B* head, B** a, B** b)
{
    B *slow = head;
    B *fast = head->next;
    while (fast)
    {
        fast = fast->next;
        if (fast)
        {
            slow = slow->next;
            fast = fast->next;
        }
    }
    *a = head;
    *b = slow->next;
    slow->next = NULL;
}

static inline B* JOIN(B, merge)(A* self, B* a, B* b)
{
    B* result = NULL;
    if (!a)
        return b;
    else if (!b)
        return a;
    if (self->compare(&a->value, &b->value) || self->equal(&a->value, &b->value))
    {
        result = a;
        result->next = JOIN(B, merge)(self, a->next, b);
    }
    else
    {
        result = b;
        result->next = JOIN(B, merge)(self, a, b->next);
    }
    return result;
}

// not the fast inplace_merge as above
static inline A JOIN(A, merge_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;
    /*
    if (next2 == JOIN(I, next))
    {
        // do the native destructive merge?
        self.head = JOIN(B, merge)(&self, r1->node, r2->node);
        return self;
    }
    */
    B* node = self.head;
    while (!JOIN(I, done)(r1))
    {
        B* next;
        if (done2(r2))
            return *JOIN(A, copy_range)(r1, &self);
        if (self.compare(ref2(r2), r1->ref))
        {
            next = JOIN(B, init)(self.copy(ref2(r2)));
            next2(r2);
        }
        else
        {
            next = JOIN(B, init)(self.copy(r1->ref));
            JOIN(I, next)(r1);
        }

        if (UNLIKELY(!node)) // empty head
        {
            node = next;
            if (!self.head)
                self.head = node;
        }
        else
        {
            node->next = next;
            node = next;
        }
    }
    JOIN(A, copy_range)(r2, &self);
    return self;
}

static inline void JOIN(A, merge)(A *self, A *other)
{
    CTL_ASSERT_COMPARE;
    if (JOIN(A, empty)(self))
        JOIN(A, swap)(self, other);
    else
        self->head = JOIN(B, merge)(self, self->head, other->head);
}

static inline void JOIN(B, _merge_sort)(A* self, B** headref)
{
    B* head = *headref;
    B *a, *b;
    if (!head || !head->next) // less than 2 elements
        return;
    JOIN(B, split_front_back)(head, &a, &b);
    JOIN(B, _merge_sort)(self, &a);
    JOIN(B, _merge_sort)(self, &b);
    *headref = JOIN(B, merge)(self, a, b);
}

static inline void JOIN(A, sort)(A *self)
{
    CTL_ASSERT_COMPARE;
    JOIN(B, _merge_sort)(self, &self->head);
}

static inline void JOIN(A, stable_sort)(A *self)
{
    CTL_ASSERT_COMPARE;
    JOIN(B, _merge_sort)(self, &self->head);
}

// not implemented in the STL
static inline void JOIN(A, sort_range)(I *range)
{
    A* self = range->container;
    CTL_ASSERT_COMPARE;
    if (range->end != NULL && range->node != range->end) // have tail behind range->end
    {
        B* last = range->node;
        B* tail = range->end;
        while (last->next != range->end)
            last = last->next;
        last->next = NULL;
        JOIN(B, _merge_sort)(self, &range->node);
        // find new end
        last = range->node;
        while (last->next)
            last = last->next;
        last->next = tail;
    }
    else
    {
        JOIN(B, _merge_sort)(self, &range->node);
    }
}

static inline void JOIN(A, unique)(A *self)
{
    CTL_ASSERT_EQUAL
    foreach (A, self, it)
        if (it.node->next && JOIN(A, _equal)(self, it.ref, &it.node->next->value))
            JOIN(A, erase_after)(self, it.node);
}

static inline I JOIN(A, find)(A *self, T key)
{
    CTL_ASSERT_EQUAL
    foreach (A, self, it)
        if (JOIN(A, _equal)(self, it.ref, &key))
            return it;
    return JOIN(A, end)(self);
}

static inline A* JOIN(A, copy_range)(GI *range, A *out)
{
    void (*next1)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;
    B* tail = JOIN(A, tail)(out);
    while (!done(range))
    {
        B* next = JOIN(B, init)(out->copy(ref(range)));
        if (!tail)
        {
            tail = next;
            if (!out->head)
                out->head = tail;
        }
        else
        {
            tail->next = next;
            tail = next;
        }
        next1(range);
    }
    return out;
}

static inline A* JOIN(A, copy_front_range)(GI *range, A *out)
{
    void (*next)(struct I*) = range->vtable.next;
    T* (*ref)(struct I*) = range->vtable.ref;
    int (*done)(struct I*) = range->vtable.done;
    while (!done(range))
    {
        JOIN(A, push_front)(out, out->copy(ref(range)));
        next(range);
    }
    return out;
}

// move elements from range to the end of out
static inline A *JOIN(A, move_range)(I *range, A *out)
{
    A *self = range->container;
    B *node = range->node;
    B* tail = JOIN(A, tail)(self);
    while (node != range->end)
    {
        JOIN(A, connect_after)(self, tail, node);
        tail = tail->next;
        node = node->next;
    }
    /*
    I outrange = JOIN(A, begin)(out);
    while (node != range->end)
    {
        B *next = node->next;
        JOIN(A, transfer_before)(out, self, node, out->head);
        node = next;
    }
    outrange.node = out->head;
    JOIN(A, reverse_range)(&outrange);
    */
    return out;
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
            JOIN(A, erase_after)(range->container, range->node);
        prev.node = prev.node->next;
        prev.ref = &prev.node->value;
        range->node = next;
    }
    JOIN(I, next)(&prev);
    return prev;
}

static inline A JOIN(A, union_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;
 
    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
        {
            JOIN(A, copy_front_range)(r1, &self);
            JOIN(A, reverse)(&self);
            return self;
        }
        if (self.compare(ref2(r2), r1->ref))
        {
            JOIN(A, push_front)(&self, self.copy(ref2(r2)));
            next2(r2);
        }
        else
        {
            JOIN(A, push_front)(&self, self.copy(r1->ref));
            if (!self.compare(r1->ref, ref2(r2)))
                next2(r2);
            JOIN(I, next)(r1);
        }
    }
    JOIN(A, copy_front_range)(r2, &self);
    JOIN(A, reverse)(&self);
    return self;
}

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
                JOIN(A, push_front)(&self, self.copy(r1->ref));
                JOIN(I, next)(r1);
            }
            next2(r2);
        }
    }
    JOIN(A, reverse)(&self);
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
        {
            JOIN(A, copy_front_range)(r1, &self);
            JOIN(A, reverse)(&self);
            return self;
        }
        if (self.compare(r1->ref, ref2(r2)))
        {
            JOIN(A, push_front)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (self.compare(ref2(r2), r1->ref))
                JOIN(A, push_front)(&self, self.copy(ref2(r2)));
            else
                JOIN(I, next)(r1);
            next2(r2);
        }
    }
    JOIN(A, copy_front_range)(r2, &self);
    JOIN(A, reverse)(&self);
    return self;
}

static inline A JOIN(A, difference_range)(I *r1, GI *r2)
{
    A self = JOIN(A, init_from)(r1->container);
    void (*next2)(struct I*) = r2->vtable.next;
    T* (*ref2)(struct I*) = r2->vtable.ref;
    int (*done2)(struct I*) = r2->vtable.done;

    while (!JOIN(I, done)(r1))
    {
        if (done2(r2))
        {
            JOIN(A, copy_front_range)(r1, &self);
            JOIN(A, reverse)(&self);
            return self;
        }
        // r1 < r2 (fails with 3-way compare)
        if (self.compare(r1->ref, ref2(r2)))
        {
            JOIN(A, push_front)(&self, self.copy(r1->ref));
            JOIN(I, next)(r1);
        }
        else
        {
            if (!self.compare(ref2(r2), r1->ref))
                JOIN(I, next)(r1);
            next2(r2);
        }
    }
    JOIN(A, reverse)(&self);
    return self;
}

static inline A JOIN(A, difference)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, difference_range)(&r1, &r2);
}
static inline A JOIN(A, union)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, union_range)(&r1, &r2);
}
static inline A JOIN(A, intersection)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, intersection_range)(&r1, &r2);
}
static inline A JOIN(A, symmetric_difference)(A *a, A *b)
{
    JOIN(A, it) r1 = JOIN(A, begin)(a);
    JOIN(A, it) r2 = JOIN(A, begin)(b);
    return JOIN(A, symmetric_difference_range)(&r1, &r2);
}

// untested
static inline void JOIN(A, iter_swap)(I *iter1, I *iter2)
{
    ASSERT(iter1->node);
    ASSERT(iter2->node);
    JOIN(A, transfer_before)(iter1->container, iter2->container, iter1->node, iter2->node);
}

// O(2n) without i. with i: O(n+(n*n/2))
static inline void JOIN(A, shuffle)(A *self)
{
    size_t n = JOIN(A, length)(self);
    size_t i = 0;
    I iter = JOIN(A, begin)(self);
    while (!JOIN(I, done)(&iter) && n > 1)
    {
        size_t pick = rand() % (n - 1);
        B *next = iter.node->next;
        if (pick)
        {
            I iter2 = JOIN(A, begin)(self); // need a copy
            JOIN(I, advance)(&iter2, i + pick);
            JOIN(A, iter_swap)(&iter, &iter2);
        }
        i++;
        n--;
        iter.node = next;
    }
}

#undef POD
#undef NOT_INTEGRAL
#undef T
#undef A
#undef B
#undef I
#undef CTL_SLIST
