/* B-Tree with node size 256.
   SPDX-License-Identifier: MIT */

#ifndef T
# error "Template type T undefined for <ctl/btree_set.h>"
#endif

#include <ctl/ctl.h>

// TODO emplace, lower_bound, upper_bound, equal_range

#define CTL_BTSET
#define A JOIN(set, T)
#define B JOIN(A, node)
#define I JOIN(A, it)
// usually called M. max 31 (i.e. 4 bits)
#define NS ((256 / MAX(sizeof(T),sizeof(void*))) - 1)

//struct B {};
typedef struct B
{
#if 1
    struct B* l;
    struct B* r;
    struct B* p;
    T key;
    int color; // Red = 0, Black = 1
#endif
    struct B* parent;
    unsigned position:4;
    //unsigned start:4;   // always 0 for now
    unsigned finish:4;
    unsigned maxcount:4; // => is_leaf
    // either internal or leaves, no mix.
    union {
        T values[NS - 1];
        struct B* children[NS];
        // all keys in children[i] are less than key[i],
        // all keys in children[i+1] are greater than key[i],
        // 0 keys for leaf nodes, 7 for internal nodes.
    } u;
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
    CTL_B_ITER_FIELDS;
} I;

static inline B*
JOIN(A, begin)(A* self)
{
    return self->root;
}

static inline B*
JOIN(A, end)(A* self)
{
    (void) self;
    return NULL;
}

static inline B*
JOIN(B, next)(B* node)
{
    for (int i = 0; i < node->maxcount; i++)
        JOIN(B, next)(node->u.children[i]);
    return node;
}

static inline void
JOIN(I, step)(I* iter)
{
    if(iter->next == iter->end)
        iter->done = 1;
    else
    {
        iter->node = iter->next;
        if (iter->node)
        {
            iter->ref = &iter->node->key;
            iter->next = JOIN(B, next)(iter->node);
        }
        else
        {
            iter->done = 1;
            iter->ref = NULL;
            iter->next = NULL;
        }
    }
}

static inline I
JOIN(I, range)(A* container, B* begin, B* end)
{
    static I zero;
    I iter = zero;
    iter.container = container;
    if(begin)
    {
        iter.step = JOIN(I, step);
        iter.node = begin;
        iter.ref = JOIN(B, ref)(iter.node);
        iter.next = JOIN(B, next)(iter.node);
        iter.end = end;
    }
    else
        iter.done = 1;
    return iter;
}

// FIXME: disable algos until we have iters
#define __CTL_ALGORITHM_H__
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

static inline A
JOIN(A, init_from)(A* from)
{
    static A zero;
    A self = zero;
    self.equal = from->equal;
    self.compare = from->compare;
    self.copy = from->copy;
    self.free = from->free;
    return self;
}

static inline void
JOIN(A, free_node)(A* self, B* node)
{
#ifndef POD
    if(self->free)
        self->free(&node->key);
#else
    (void) self;
#endif
    free(node);
}

static inline B*
JOIN(B, init)()
{
    B* node = (B*) calloc(1, sizeof(B));
    return node;
}

static inline B*
JOIN(A, find)(A* self, T key)
{
    B* node = self->root;
    while(node)
    {
        int diff = self->compare(&key, &node->key);
        if(diff == 0)
            return node;
        else
        if(diff < 0)
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
JOIN(B, verify_property_1)(B* node)
{
    assert(JOIN(B, is_red)(node) || JOIN(B, is_black)(node));
    if(node)
    {
        JOIN(B, verify_property_1)(node->l);
        JOIN(B, verify_property_1)(node->r);
    }
}

static inline void
JOIN(B, verify_property_2)(B* node)
{
    assert(JOIN(B, is_black)(node));
}

static inline void
JOIN(B, verify_property_4)(B* node)
{
    if(JOIN(B, is_red)(node))
    {
        assert(JOIN(B, is_black)(node->l));
        assert(JOIN(B, is_black)(node->r));
        assert(JOIN(B, is_black)(node->p));
    }
    if(node)
    {
        JOIN(B, verify_property_4)(node->l);
        JOIN(B, verify_property_4)(node->r);
    }
}

static inline void
JOIN(B, count_black)(B* node, int nodes, int* in_path)
{
    if(JOIN(B, is_black)(node))
        nodes++;
    if(node)
    {
        JOIN(B, count_black)(node->l, nodes, in_path);
        JOIN(B, count_black)(node->r, nodes, in_path);
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
JOIN(B, verify_property_5)(B* node)
{
    int in_path = -1;
    JOIN(B, count_black)(node, 0, &in_path);
}

static inline void
JOIN(A, verify)(A* node)
{
    JOIN(B, verify_property_1)(node->root); // Property 1: Each node is either red or black.
    JOIN(B, verify_property_2)(node->root); // Property 2: The root node is black.
    /* Implicit */                          // Property 3: Leaves are colored black
    JOIN(B, verify_property_4)(node->root); // Property 4: Every red node has two black nodes.
    JOIN(B, verify_property_5)(node->root); // Property 5: All paths from a node have the same number of black nodes.
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

static inline B*
JOIN(A, insert)(A* self, T key)
{
    B* insert = JOIN(B, init)(key, 0);
    if(self->root)
    {
        B* node = self->root;
        while(1)
        {
            int diff = self->compare(&key, &node->key);
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
        SWAP(T, &node->key, &pred->key);
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

static inline I
JOIN(I, iter)(A* self, B *node)
{
    I it = JOIN(I, each)(self);
    it.node = node;
    it.ref = &node->key;
    it.next = JOIN(B, next)(it.node);
    return it;
}

static inline void
JOIN(A, erase_it)(A* self, I* pos)
{
    B* node = pos->node;
    if(node)
        JOIN(A, erase_node)(self, node);
}

#ifdef DEBUG
static inline void
JOIN(A, erase_range)(A* self, I* from, I* to)
{
    B* node = from->node;
    if(node)
    {
        // TODO: check if clear would be faster (from==begin && to==end)
        JOIN(A, it) it = JOIN(I, range)(self, from->node, to->node);
        for(; !it.done; it.step(&it))
            JOIN(A, erase_node)(self, it.node);
    }
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
    I it = JOIN(I, each)(self);
    A copy =  JOIN(A, init)(self->compare);
    while(!it.done)
    {
        JOIN(A, insert)(&copy, self->copy(&it.node->key));
        it.step(&it);
    }
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
    foreach(A, self, it)
        if(_match(&it.node->key))
        {
            JOIN(A, erase_node)(self, it.node);
            erases++;
        }
    return erases;
}

static inline size_t
JOIN(A, erase_if)(A* self, int (*_match)(T*))
{
    return JOIN(A, remove_if)(self, _match);
}

// join and split for fast bulk insert, bulk erase and the algos below.
// also needed for pctl.
static inline size_t
JOIN(B, rank)(B* node)
{
    size_t count = 0;
    while (node) {
        if (!node->r) {
            count++;
        }
        node = node->l;
    }
    return count;
}

/*
static inline A*
JOIN(A, join_right)(A* left, T key, B* right)
{
    // same black height
    if(JOIN(B, rank)(left->root) == (JOIN(B, rank)(right->root)/2) * 2)
    {
        B* old = left->root;
        int color = JOIN(B, is_black)(left->root) & JOIN(B, is_black)(right->root) ? 0 : 1;
        left->root = JOIN(B, init)(key, color);
        left->root->l = old;
        left->root->r = right->root;
        left->size += right->size + 1;
        return left;
    }
    else
    {
        B* l1 = left->root->l;
        B* r1 = left->root->r;
        T k1 = left->root->key;
        int c1 = left->root->color;
        A new_t = JOIN(A, init_from)(left);
        new_t->root = r1;
        new_t->root->r = join_right(&new_r, key, right);
        new_t->root->l = l1;
        new_t->key = k1;
        new_t->color = c1;
        if(c == black) and (c(R(T′)) == c(R(R(T′))) == red)
        {
            c(R(R(T′))) = black;
            JOIN(A, rotate_l)(new_t);
        }
        return new_t;
    }
}

static inline A*
JOIN(A, join_left)(A* left, T key, B* right)
{
    if r(TL)/2 > r(TR)/2
        T′ = join_right(TL, k, TR);
    if(c(T′) == red) and (c(R(T′))=red) then
        Node(L(T′),〈k(T′),black〉, R(T′))
        else T′
    else if r(TR)/2c>br(TL)/2 then
        T′ = join_eft(TL, k, TR);
        if (c(T′)==red) and (c(L(T′)) == red)
            Node(L(T′),〈k(T′),black〉, R(T′));
        else
            T′
    else if (c(TL) == black and c(TR) == black)
        Node(TL,〈k,red〉, TR)
    else
        Node(TL,〈k,black〉, TR)
}
*/

static inline A
JOIN(A, intersection)(A* a, A* b)
{
    A self = JOIN(A, init)(a->compare);
    foreach(A, a, i)
        if(JOIN(A, find)(b, *i.ref))
            JOIN(A, insert)(&self, self.copy(i.ref));
    return self;
}

static inline A
JOIN(A, union)(A* a, A* b)
{
    A self = JOIN(A, init)(a->compare);
    foreach(A, a, i) JOIN(A, insert)(&self, self.copy(i.ref));
    foreach(A, b, i) JOIN(A, insert)(&self, self.copy(i.ref));
    return self;
}

static inline A
JOIN(A, difference)(A* a, A* b)
{
    A self = JOIN(A, copy)(a);
    foreach(A, b, i) JOIN(A, erase)(&self, *i.ref);
    return self;
}

static inline A
JOIN(A, symmetric_difference)(A* a, A* b)
{
    A self = JOIN(A, union)(a, b);
    A intersection = JOIN(A, intersection)(a, b);
    foreach(A, &intersection, i) JOIN(A, erase)(&self, *i.ref);
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
#undef I
#else
#undef HOLD
#endif
#undef CTL_SET

#ifdef USE_INTERNAL_VERIFY
#undef USE_INTERNAL_VERIFY
#endif
