/* Red-black tree.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/set.h>"
#endif

// TODO emplace, lower_bound, upper_bound, equal_range

#define CTL_SET
#define A JOIN(set, T)
#define B JOIN(A, node)
#ifndef C
# define C set
#endif
#define I JOIN(A, it)
#undef IT
#define IT B*

#include <ctl/ctl.h>
#include <ctl/bits/iterators.h>

typedef struct B
{
    struct B* l;
    struct B* r;
    struct B* p;
    T value;
    int color; // Red = 0, Black = 1
} B;

typedef struct A
{
    B* root;
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

#undef _set_begin_it
#define _set_begin_it JOIN(JOIN(_set, T), begin_it)
#undef _set_end_it
#define _set_end_it JOIN(JOIN(_set, T), end_it)

static I _set_begin_it = {{NULL,NULL,NULL}, NULL
#ifdef DEBUG
    , CTL_LIST_TAG
#endif
};

static I _set_end_it = {{NULL,NULL,NULL}, NULL
#ifdef DEBUG
    , CTL_LIST_TAG
#endif
};

static inline B*
JOIN(A, begin)(A* self)
{
    I *iter = &_set_begin_it;
    if (self->root)
        iter->node = *self->root;
    iter->container = self;
    return (B*)iter;
}

static inline B*
JOIN(A, end)(A* self)
{
    I *iter = &_set_end_it;
    iter->container = self;
    return (B*)iter;
}

static inline B*
JOIN(B, min)(B* self)
{
    while(self->l)
        self = self->l;
    return self;
}

static inline B*
JOIN(B, max)(B* self)
{
    while(self->r)
        self = self->r;
    return self;
}

static inline B*
JOIN(B, next)(B* self)
{
    if(self->r)
    {
        self = self->r;
        while(self->l)
            self = self->l;
    }
    else
    {
        B* parent = self->p;
        while(parent && self == parent->r)
        {
            self = parent;
            parent = parent->p;
        }
        self = parent;
    }
    return self;
}

static inline T*
JOIN(I, ref)(B* node)
{
    return &node->value;
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
    return iter->node.r == NULL && iter->node.l == NULL;
}

static inline B*
JOIN(I, next)(B* node)
{
    return JOIN(B, next)(node);
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
        node = JOIN(B, next)(node);
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
        i = JOIN(B, next)(i);
    if (i == other)
        return d;
    // other before self, negative result
    I* iter2 = (I*)other;
    CHECK_TAG(iter2, 0)
    d = (long)iter2->container->size;
    for(; other != NULL && other != self; d--)
        other = JOIN(B, next)(other);
    return other ? -d : LONG_MAX;
}

/*
static inline void
JOIN(I, step)(I* self)
{
    if(self->next == self->end)
        self->done = 1;
    else
    {
        self->node = self->next;
        if (self->node)
        {
            self->ref = &self->node->key;
            self->next = JOIN(B, next)(self->node);
        }
        else
        {
            self->done = 1;
            self->ref = NULL;
            self->next = NULL;
        }
    }
}

static inline I
JOIN(I, range)(A* container, B* begin, B* end)
{
    static I zero;
    I self = zero;
    self.container = container;
    if(begin)
    {
        self.step = JOIN(I, step);
        self.node = JOIN(B, min)(begin);
        self.ref = &self.node->value;
        self.next = JOIN(B, next)(self.node);
        self.end = end;
    }
    else
        self.done = 1;
    return self;
}
*/

#include <ctl/bits/container.h>

static inline A
JOIN(A, init)(int _compare(T*, T*))
{
    static A zero;
    A self = zero;
    self.compare = _compare;
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
JOIN(A, free_node)(A* self, B* node)
{
#ifndef POD
    if(self->free)
        self->free(&node->value);
#else
    (void) self;
#endif
    free(node);
}

static inline int
JOIN(B, color)(B* self)
{
    return self ? self->color : 1;
}

static inline int
JOIN(B, is_black)(B* self)
{
    return JOIN(B, color)(self) == 1;
}

static inline int
JOIN(B, is_red)(B* self)
{
    return JOIN(B, color)(self) == 0;
}

static inline B*
JOIN(B, grandfather)(B* self)
{
    return self->p->p;
}

static inline B*
JOIN(B, sibling)(B* self)
{
    if(self == self->p->l)
        return self->p->r;
    else
        return self->p->l;
}

static inline B*
JOIN(B, uncle)(B* self)
{
    return JOIN(B, sibling)(self->p);
}

static inline B*
JOIN(B, init)(T key, int color)
{
    B* self = (B*) malloc(sizeof(B));
    self->value = key;
    self->color = color;
    self->l = self->r = self->p = NULL;
    return self;
}

static inline B*
JOIN(A, find)(A* self, T key)
{
    B* node = self->root;
    while(node)
    {
        int diff = self->compare(&key, &node->value);
        // Don't rely on a valid 3-way compare. can be just a simple >
        if(diff == 0)
        {
            if (self->equal)
            {
                if (self->equal(&key, &node->value))
                    return node;
                else
                    node = node->r;
            }
            else
                return node;
        }
        else if(diff < 0)
            node = node->l;
        else
            node = node->r;
    }
    return NULL;
}

static inline int
JOIN(A, count)(A* self, T key)
{
    int result = JOIN(A, find)(self, key) ? 1 : 0;
#ifndef POD
    if(self->free)
        self->free(&key);
#endif
    return result;
}

static inline int
JOIN(A, contains)(A* self, T key)
{
    return JOIN(A, count)(self, key) == 1;
}

static inline void
JOIN(B, replace)(A* self, B* a, B* b)
{
    if(a->p)
    {
        if(a == a->p->l)
            a->p->l = b;
        else
            a->p->r = b;
    }
    else
        self->root = b;
    if(b)
        b->p = a->p;
}

#ifdef USE_INTERNAL_VERIFY

#include <assert.h>

static inline void
JOIN(B, verify_property_1)(B* self)
{
    assert(JOIN(B, is_red)(self) || JOIN(B, is_black)(self));
    if(self)
    {
        JOIN(B, verify_property_1)(self->l);
        JOIN(B, verify_property_1)(self->r);
    }
}

static inline void
JOIN(B, verify_property_2)(B* self)
{
    assert(JOIN(B, is_black)(self));
}

static inline void
JOIN(B, verify_property_4)(B* self)
{
    if(JOIN(B, is_red)(self))
    {
        assert(JOIN(B, is_black)(self->l));
        assert(JOIN(B, is_black)(self->r));
        assert(JOIN(B, is_black)(self->p));
    }
    if(self)
    {
        JOIN(B, verify_property_4)(self->l);
        JOIN(B, verify_property_4)(self->r);
    }
}

static inline void
JOIN(B, count_black)(B* self, int nodes, int* in_path)
{
    if(JOIN(B, is_black)(self))
        nodes++;
    if(self)
    {
        JOIN(B, count_black)(self->l, nodes, in_path);
        JOIN(B, count_black)(self->r, nodes, in_path);
    }
    else
    {
        if(*in_path == -1)
            *in_path = nodes;
        else
            assert(nodes == *in_path);
    }
}

static inline void
JOIN(B, verify_property_5)(B* self)
{
    int in_path = -1;
    JOIN(B, count_black)(self, 0, &in_path);
}

static inline void
JOIN(A, verify)(A* self)
{
    JOIN(B, verify_property_1)(self->root); // Property 1: Each node is either red or black.
    JOIN(B, verify_property_2)(self->root); // Property 2: The root node is black.
    /* Implicit */                          // Property 3: Leaves are colored black
    JOIN(B, verify_property_4)(self->root); // Property 4: Every red node has two black nodes.
    JOIN(B, verify_property_5)(self->root); // Property 5: All paths from a node have the same number of black nodes.
}

#endif

static inline void
JOIN(A, rotate_l)(A* self, B* node)
{
    B* r = node->r;
    JOIN(B, replace)(self, node, r);
    node->r = r->l;
    if(r->l)
        r->l->p = node;
    r->l = node;
    node->p = r;
}

static inline void
JOIN(A, rotate_r)(A* self, B* node)
{
    B* l = node->l;
    JOIN(B, replace)(self, node, l);
    node->l = l->r;
    if(l->r)
        l->r->p = node;
    l->r = node;
    node->p = l;
}

static inline void
JOIN(A, insert_1)(A*, B*),
JOIN(A, insert_2)(A*, B*),
JOIN(A, insert_3)(A*, B*),
JOIN(A, insert_4)(A*, B*),
JOIN(A, insert_5)(A*, B*);

static inline B*
JOIN(A, insert)(A* self, T key)
{
    B* insert = JOIN(B, init)(key, 0);
    if(self->root)
    {
        B* node = self->root;
        while(1)
        {
            int diff = self->compare(&key, &node->value);
            if(diff == 0)
            {
                JOIN(A, free_node)(self, insert);
                return node;
            }
            else
            if(diff < 0)
            {
                if(node->l)
                    node = node->l;
                else
                {
                    node->l = insert;
                    break;
                }
            }
            else
            {
                if(node->r)
                    node = node->r;
                else
                {
                    node->r = insert;
                    break;
                }
            }
        }
        insert->p = node;
    }
    else
        self->root = insert;
    JOIN(A, insert_1)(self, insert);
    self->size++;
#ifdef USE_INTERNAL_VERIFY
    JOIN(A, verify)(self);
#endif
    return insert;
}

static inline void
JOIN(A, insert_1)(A* self, B* node)
{
    if(node->p)
        JOIN(A, insert_2)(self, node);
    else
        node->color = 1;
}

static inline void
JOIN(A, insert_2)(A* self, B* node)
{
    if(JOIN(B, is_black)(node->p))
        return;
    else
       JOIN(A, insert_3)(self, node);
}

static inline void
JOIN(A, insert_3)(A* self, B* node)
{
    if(JOIN(B, is_red)(JOIN(B, uncle)(node)))
    {
        node->p->color = 1;
        JOIN(B, uncle)(node)->color = 1;
        JOIN(B, grandfather)(node)->color = 0;
        JOIN(A, insert_1)(self, JOIN(B, grandfather)(node));
    }
    else
        JOIN(A, insert_4)(self, node);
}

static inline void
JOIN(A, insert_4)(A* self, B* node)
{
    if(node == node->p->r && node->p == JOIN(B, grandfather)(node)->l)
    {
        JOIN(A, rotate_l)(self, node->p);
        node = node->l;
    }
    else
    if(node == node->p->l && node->p == JOIN(B, grandfather)(node)->r)
    {
        JOIN(A, rotate_r)(self, node->p);
        node = node->r;
    }
    JOIN(A, insert_5)(self, node);
}

static inline void
JOIN(A, insert_5)(A* self, B* node)
{
    node->p->color = 1;
    JOIN(B, grandfather)(node)->color = 0;
    if(node == node->p->l && node->p == JOIN(B, grandfather)(node)->l)
        JOIN(A, rotate_r)(self, JOIN(B, grandfather)(node));
    else
        JOIN(A, rotate_l)(self, JOIN(B, grandfather)(node));
}

static inline void
JOIN(A, erase_1)(A*, B*),
JOIN(A, erase_2)(A*, B*),
JOIN(A, erase_3)(A*, B*),
JOIN(A, erase_4)(A*, B*),
JOIN(A, erase_5)(A*, B*),
JOIN(A, erase_6)(A*, B*);

static inline void
JOIN(A, erase_node)(A* self, B* node)
{
    if(node->l && node->r)
    {
        B* pred = JOIN(B, max)(node->l);
        SWAP(T, &node->value, &pred->value);
        node = pred;
    }
    B* child = node->r ? node->r : node->l;
    if(JOIN(B, is_black)(node))
    {
        node->color = JOIN(B, color)(child);
        JOIN(A, erase_1)(self, node);
    }
    JOIN(B, replace)(self, node, child);
    if(node->p == NULL && child)
        child->color = 1;
    JOIN(A, free_node)(self, node);
    self->size--;
#ifdef USE_INTERNAL_VERIFY
    JOIN(A, verify)(self);
#endif
}

/*
static inline I
JOIN(I, iter)(A* self, B *node)
{
    I iter = _set_begin_it;
    if (self->root)
        iter.node = *self->root;
    iter->container = self;
    return iter;
}
*/

static inline void
JOIN(A, erase_it)(A* self, I* it)
{
    B* node = &it->node;
    if(node)
        JOIN(A, erase_node)(self, node);
}

#ifdef DEBUG
static inline void
JOIN(A, erase_range)(A* self, B* from, B* to)
{
    // TODO: check if clear would be faster (from==begin && to==end)
    for(B* it = from; it; it = JOIN(B, next)(it))
        JOIN(A, erase_node)(self, it);
}
#endif

static inline void
JOIN(A, erase)(A* self, T key)
{
    B* node = JOIN(A, find)(self, key);
    if(node)
        JOIN(A, erase_node)(self, node);
}

static inline void
JOIN(A, erase_1)(A* self, B* node)
{
    if(node->p)
        JOIN(A, erase_2)(self, node);
}

static inline void
JOIN(A, erase_2)(A* self, B* node)
{
    if(JOIN(B, is_red)(JOIN(B, sibling)(node)))
    {
        node->p->color = 0;
        JOIN(B, sibling)(node)->color = 1;
        if(node == node->p->l)
            JOIN(A, rotate_l)(self, node->p);
        else
            JOIN(A, rotate_r)(self, node->p);
    }
    JOIN(A, erase_3)(self, node);
}

static inline void
JOIN(A, erase_3)(A* self, B* node)
{
    if(JOIN(B, is_black)(node->p)
    && JOIN(B, is_black)(JOIN(B, sibling)(node))
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->l)
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->r))
    {
        JOIN(B, sibling)(node)->color = 0;
        JOIN(A, erase_1)(self, node->p);
    }
    else
        JOIN(A, erase_4)(self, node);
}

static inline void
JOIN(A, erase_4)(A* self, B* node)
{
    if(JOIN(B, is_red)(node->p)
    && JOIN(B, is_black)(JOIN(B, sibling)(node))
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->l)
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->r))
    {
        JOIN(B, sibling)(node)->color = 0;
        node->p->color = 1;
    }
    else
        JOIN(A, erase_5)(self, node);
}

static inline void
JOIN(A, erase_5)(A* self, B* node)
{
    if(node == node->p->l
    && JOIN(B, is_black)(JOIN(B, sibling)(node))
    && JOIN(B, is_red)(JOIN(B, sibling)(node)->l)
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->r))
    {
        JOIN(B, sibling)(node)->color = 0;
        JOIN(B, sibling)(node)->l->color = 1;
        JOIN(A, rotate_r)(self, JOIN(B, sibling)(node));
    }
    else
    if(node == node->p->r
    && JOIN(B, is_black)(JOIN(B, sibling)(node))
    && JOIN(B, is_red)(JOIN(B, sibling)(node)->r)
    && JOIN(B, is_black)(JOIN(B, sibling)(node)->l))
    {
        JOIN(B, sibling)(node)->color = 0;
        JOIN(B, sibling)(node)->r->color = 1;
        JOIN(A, rotate_l)(self, JOIN(B, sibling)(node));
    }
    JOIN(A, erase_6)(self, node);
}

static inline void
JOIN(A, erase_6)(A* self, B* node)
{
    JOIN(B, sibling)(node)->color = JOIN(B, color)(node->p);
    node->p->color = 1;
    if(node == node->p->l)
    {
        JOIN(B, sibling)(node)->r->color = 1;
        JOIN(A, rotate_l)(self, node->p);
    }
    else
    {
        JOIN(B, sibling)(node)->l->color = 1;
        JOIN(A, rotate_r)(self, node->p);
    }
}

// erase without rebalancing. e.g. for clear
static inline void
JOIN(B, erase_fast)(A* self, B* node)
{
    while(node)
    {
        JOIN(B, erase_fast)(self, node->r);
        B* left = node->l;
        JOIN(A, free_node)(self, node);
        node = left;
        self->size--;
    }
}

static inline void
JOIN(A, clear)(A* self)
{
    while(!JOIN(A, empty)(self))
        JOIN(B, erase_fast)(self, self->root);
}

static inline void
JOIN(A, free)(A* self)
{
    JOIN(A, clear)(self);
    *self = JOIN(A, init)(self->compare);
}

static inline A
JOIN(A, copy)(A* self)
{
    A copy =  JOIN(A, init)(self->compare);
    foreach_ref(A, T, IT, self, it, ref)
        JOIN(A, insert)(&copy, self->copy(ref));
    return copy;
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline size_t
JOIN(A, remove_if)(A* self, int (*_match)(T*))
{
    size_t erases = 0;
    foreach_ref(A, T, IT, self, it, ref)
        if(_match(ref))
        {
            JOIN(A, erase_node)(self, it);
            erases++;
        }
    return erases;
}

static inline size_t
JOIN(A, erase_if)(A* self, int (*_match)(T*))
{
    return JOIN(A, remove_if)(self, _match);
}

static inline A
JOIN(A, intersection)(A* a, A* b)
{
    A self = JOIN(A, init)(a->compare);
    foreach_ref(A, T, IT, a, it, ref)
        if(JOIN(A, find)(b, *ref))
            JOIN(A, insert)(&self, self.copy(ref));
    return self;
}

static inline A
JOIN(A, union)(A* a, A* b)
{
    A self = JOIN(A, init)(a->compare);
    foreach_ref(A, T, IT, a, it, ref)
        JOIN(A, insert)(&self, self.copy(ref));
    foreach_ref(A, T, IT, b, it2, ref2)
        JOIN(A, insert)(&self, self.copy(ref2));
    return self;
}

static inline A
JOIN(A, difference)(A* a, A* b)
{
    A self = JOIN(A, copy)(a);
    foreach_ref(A, T, IT, b, it, ref)
        JOIN(A, erase)(&self, *ref);
    return self;
}

static inline A
JOIN(A, symmetric_difference)(A* a, A* b)
{
    A self = JOIN(A, union)(a, b);
    A intersection = JOIN(A, intersection)(a, b);
    foreach_ref(A, T, IT, &intersection, it, ref)
        JOIN(A, erase)(&self, *ref);
    JOIN(A, free)(&intersection);
    return self;
}

#if defined(CTL_MAP)
# include <ctl/algorithm.h>
#endif

#ifndef HOLD
#undef POD
#undef NOT_INTEGRAL
#undef T
#undef A
#undef B
#undef C
#undef I
#else
#undef HOLD
#endif
#undef CTL_SET

#ifdef USE_INTERNAL_VERIFY
#undef USE_INTERNAL_VERIFY
#endif
