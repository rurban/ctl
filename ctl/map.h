/* WIP Unordered, in opposition to C++ STL. Implemented as open-addressing hash table. */

#ifndef T
#error "Template type T undefined for <ctl/map.h>"
#endif

/* TODO khash or such */

#include <ctl/ctl.h>

#define A JOIN(map, T)
#define B JOIN(A, node)
#define I JOIN(A, it)

typedef struct B
{
    struct C* buckets;
    T key;
    int size;
} B;

typedef struct A
{
    B* root;
    int (*compare)(T*, T*);
    void (*free)(T*);
    T (*copy)(T*);
    size_t size;
} A;

typedef struct I
{
    void (*step)(struct I*);
    B* end;
    B* node;
    T* ref;
    B* next;
    int done;
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

static inline int
JOIN(A, empty)(A* self)
{
    return self->size == 0;
}

static inline size_t
JOIN(A, size)(A* self)
{
    return self->size;
}

static inline size_t
JOIN(A, max_size)()
{
    return 4294967296 / sizeof(T); // 32bit at most
}

static inline T
JOIN(A, implicit_copy)(T* self)
{
    return *self;
}

static inline A
JOIN(A, init)(int _compare(T*, T*))
{
    static A zero;
    A self = zero;
    self.compare = _compare;
#ifdef POD
#undef P
    self.copy = JOIN(A, implicit_copy);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    return self;
}

static inline void
JOIN(A, free_node)(A* self, B* node)
{
    if(self->free)
        self->free(&node->key);
    free(node);
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
JOIN(B, init)(T key, int color)
{
    B* self = (B*) malloc(sizeof(B));
    self->key = key;
    self->color = color;
    self->l = self->r = self->p = NULL;
    return self;
}

static inline B*
JOIN(A, at)(A* self, T key)
{
    return JOIN(A, find)(self, key);
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
    return JOIN(A, find)(self, key) ? 1 : 0;
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
    assert(JOIN(B, is_red)(self) || JOIN(B, is_blk)(self));
    if(self)
    {
        JOIN(B, verify_property_1)(self->l);
        JOIN(B, verify_property_1)(self->r);
    }
}

static inline void
JOIN(B, verify_property_2)(B* self)
{
    assert(JOIN(B, is_blk)(self));
}

static inline void
JOIN(B, verify_property_4)(B* self)
{
    if(JOIN(B, is_red)(self))
    {
        assert(JOIN(B, is_blk)(self->l));
        assert(JOIN(B, is_blk)(self->r));
        assert(JOIN(B, is_blk)(self->p));
    }
    if(self)
    {
        JOIN(B, verify_property_4)(self->l);
        JOIN(B, verify_property_4)(self->r);
    }
}

static inline void
JOIN(B, count_blk)(B* self, int nodes, int* in_path)
{
    if(JOIN(B, is_blk)(self))
        nodes += 1;
    if(self)
    {
        JOIN(B, count_blk)(self->l, nodes, in_path);
        JOIN(B, count_blk)(self->r, nodes, in_path);
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
    JOIN(B, count_blk)(self, 0, &in_path);
}

static inline void
JOIN(A, verify)(A* self)
{
    JOIN(B, verify_property_1)(self->root); // Property 1: Each node is either red or black.
    JOIN(B, verify_property_2)(self->root); // Property 2: The root node is black.
    /* Implicit */                          // Property 3: Leaves are colored black
    JOIN(B, verify_property_4)(self->root); // Property 4: Every red node has two black ndoes.
    JOIN(B, verify_property_5)(self->root); // Property 5: All paths from a node have the same number of black nodes.
}

#endif

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
    self->size += 1;
#ifdef USE_INTERNAL_VERIFY
    JOIN(A, verify)(self);
#endif
    return insert;
}

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
    if(JOIN(B, is_blk)(node))
    {
        node->color = JOIN(B, color)(child);
        JOIN(A, erase_1)(self, node);
    }
    JOIN(B, replace)(self, node, child);
    if(node->p == NULL && child)
        child->color = 1;
    JOIN(A, free_node)(self, node);
    self->size -= 1;
#ifdef USE_INTERNAL_VERIFY
    JOIN(A, verify)(self);
#endif
}

static inline void
JOIN(A, erase)(A* self, T key)
{
    B* node = JOIN(A, find)(self, key);
    if(node)
        JOIN(A, erase_node)(self, node);
}

static inline void
JOIN(A, clear)(A* self)
{
    while(!JOIN(A, empty)(self))
        JOIN(A, erase)(self, self->root->key);
}

static inline void
JOIN(A, free)(A* self)
{
    JOIN(A, clear)(self);
    *self = JOIN(A, init)(self->compare);
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
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

static inline void
JOIN(I, step)(I* self)
{
    if(self->next == self->end)
        self->done = 1;
    else
    {
        self->node = self->next;
        self->ref = &self->node->key;
        self->next = JOIN(B, next)(self->node);
    }
}

static inline I
JOIN(I, range)(B* begin, B* end)
{
    static I zero;
    I self = zero;
    if(begin)
    {
        self.step = JOIN(I, step);
        self.node = JOIN(B, min)(begin);
        self.ref = &self.node->key;
        self.next = JOIN(B, next)(self.node);
        self.end = end;
    }
    else
        self.done = 1;
    return self;
}

static inline I
JOIN(I, each)(A* a)
{
    return JOIN(I, range)(JOIN(A, begin)(a), JOIN(A, end)(a));
}

static inline int
JOIN(A, equal)(A* self, A* other, int _equal(T*, T*))
{
    if(self->size != other->size)
        return 0;
    I a = JOIN(I, each)(self);
    I b = JOIN(I, each)(other);
    while(!a.done && !b.done)
    {
        if(!_equal(&a.node->key, &b.node->key))
            return 0;
        a.step(&a);
        b.step(&b);
    }
    return 1;
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

#undef T
#undef A
#undef B
#undef I

#ifdef USE_INTERNAL_VERIFY
#undef USE_INTERNAL_VERIFY
#endif
