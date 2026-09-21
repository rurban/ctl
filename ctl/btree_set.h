/* B-tree set.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/btree_set.h>"
#endif

#ifndef BTSET_MAX_KEYS
#define BTSET_MAX_KEYS 7
#endif

#if BTSET_MAX_KEYS < 3 || !(BTSET_MAX_KEYS & 1)
#error "BTSET_MAX_KEYS must be an odd integer of at least 3"
#endif

#define CTL_BTSET
#define A JOIN(btset, T)
#define B JOIN(A, node)
#define I JOIN(A, it)
#define GI JOIN(A, it)
#define BTSET_MIN_KEYS (BTSET_MAX_KEYS / 2)

#include <ctl/ctl.h>
#include <stdbool.h>

typedef struct B
{
    size_t count;
    bool leaf;
    T keys[BTSET_MAX_KEYS];
    struct B *children[BTSET_MAX_KEYS + 1];
} B;

typedef struct A
{
    B *root;
    size_t size;
    void (*free)(T *);
    T (*copy)(T *);
    int (*compare)(T *, T *);
    int (*equal)(T *, T *);
} A;

#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_DEQ_ITER_FIELDS;
} I;

static inline T *JOIN(A, at)(A *self, size_t index);

static inline T *JOIN(I, ref)(I *iter)
{
    return iter->ref;
}

static inline int JOIN(I, done)(I *iter)
{
    return iter->index >= iter->end;
}

static inline void JOIN(I, next)(I *iter)
{
    if (iter->index < iter->end)
        iter->index++;
    iter->ref = iter->index < iter->end ? JOIN(A, at)(iter->container, iter->index) : NULL;
}

static inline I JOIN(I, iter)(A *self, size_t index)
{
    static I zero;
    I iter = zero;
    iter.container = self;
    iter.index = index;
    iter.end = self->size;
    iter.ref = index < self->size ? JOIN(A, at)(self, index) : NULL;
    iter.vtable.next = JOIN(I, next);
    iter.vtable.ref = JOIN(I, ref);
    iter.vtable.done = JOIN(I, done);
    return iter;
}

static inline I JOIN(A, begin)(A *self)
{
    return JOIN(I, iter)(self, 0);
}

static inline I JOIN(A, end)(A *self)
{
    return JOIN(I, iter)(self, self->size);
}

static inline bool JOIN(A, less)(A *self, T *left, T *right)
{
    const int forward = self->compare(left, right);
    const int reverse = self->compare(right, left);
    return forward < 0 || (forward > 0 && reverse == 0);
}

static inline bool JOIN(A, equivalent)(A *self, T *left, T *right)
{
    return self->equal ? self->equal(left, right) : !JOIN(A, less)(self, left, right) && !JOIN(A, less)(self, right, left);
}

static inline B *JOIN(B, init)(bool leaf)
{
    B *node = (B *)calloc(1, sizeof(B));
    if (node)
        node->leaf = leaf;
    return node;
}

static inline T *JOIN(B, find)(A *self, B *node, T *key)
{
    while (node)
    {
        size_t index = 0;
        while (index < node->count && JOIN(A, less)(self, &node->keys[index], key))
            index++;
        if (index < node->count && JOIN(A, equivalent)(self, &node->keys[index], key))
            return &node->keys[index];
        if (node->leaf)
            return NULL;
        node = node->children[index];
    }
    return NULL;
}

static inline T *JOIN(A, find_value)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    return JOIN(B, find)(self, self->root, &key);
}

static inline int JOIN(A, contains)(A *self, T key)
{
    return JOIN(A, find_value)(self, key) != NULL;
}

static inline size_t JOIN(A, count)(A *self, T key)
{
    return JOIN(A, contains)(self, key) ? 1 : 0;
}

static inline T *JOIN(B, nth)(B *node, size_t *index)
{
    if (!node)
        return NULL;
    for (size_t i = 0; i < node->count; i++)
    {
        if (!node->leaf)
        {
            T *value = JOIN(B, nth)(node->children[i], index);
            if (value)
                return value;
        }
        if (*index == 0)
            return &node->keys[i];
        (*index)--;
    }
    return node->leaf ? NULL : JOIN(B, nth)(node->children[node->count], index);
}

static inline T *JOIN(A, at)(A *self, size_t index)
{
    if (index >= self->size)
        return NULL;
    return JOIN(B, nth)(self->root, &index);
}

static inline T *JOIN(A, front)(A *self)
{
    return JOIN(A, at)(self, 0);
}

static inline T *JOIN(A, back)(A *self)
{
    return self->size ? JOIN(A, at)(self, self->size - 1) : NULL;
}

static inline A JOIN(A, init_from)(A *source);
static inline void JOIN(A, clear)(A *self);

#include <ctl/bits/container.h>

static inline A JOIN(A, init)(int _compare(T *, T *))
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

static inline A JOIN(A, init_from)(A *source)
{
    static A zero;
    A self = zero;
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    self.compare = source->compare;
    self.equal = source->equal;
    return self;
}

static inline void JOIN(B, free)(A *self, B *node)
{
    if (!node)
        return;
    for (size_t i = 0; i <= node->count && !node->leaf; i++)
        JOIN(B, free)(self, node->children[i]);
#ifndef POD
    if (self->free)
        for (size_t i = 0; i < node->count; i++)
            self->free(&node->keys[i]);
#endif
    free(node);
}

static inline void JOIN(A, clear)(A *self)
{
    JOIN(B, free)(self, self->root);
    self->root = NULL;
    self->size = 0;
}

static inline void JOIN(A, free)(A *self)
{
    int (*compare)(T *, T *) = self->compare;
    JOIN(A, clear)(self);
    *self = JOIN(A, init)(compare);
}

static inline void JOIN(B, split_child)(B *parent, size_t index)
{
    B *left = parent->children[index];
    B *right = JOIN(B, init)(left->leaf);
    right->count = BTSET_MIN_KEYS;
    for (size_t i = 0; i < BTSET_MIN_KEYS; i++)
        right->keys[i] = left->keys[i + BTSET_MIN_KEYS + 1];
    if (!left->leaf)
        for (size_t i = 0; i <= BTSET_MIN_KEYS; i++)
            right->children[i] = left->children[i + BTSET_MIN_KEYS + 1];

    left->count = BTSET_MIN_KEYS;
    for (size_t i = parent->count + 1; i > index + 1; i--)
        parent->children[i] = parent->children[i - 1];
    parent->children[index + 1] = right;
    for (size_t i = parent->count; i > index; i--)
        parent->keys[i] = parent->keys[i - 1];
    parent->keys[index] = left->keys[BTSET_MIN_KEYS];
    parent->count++;
}

static inline T *JOIN(B, insert_nonfull)(A *self, B *node, T key)
{
    size_t index = node->count;
    if (node->leaf)
    {
        while (index > 0 && JOIN(A, less)(self, &key, &node->keys[index - 1]))
        {
            node->keys[index] = node->keys[index - 1];
            index--;
        }
        node->keys[index] = key;
        node->count++;
        return &node->keys[index];
    }

    while (index > 0 && JOIN(A, less)(self, &key, &node->keys[index - 1]))
        index--;
    if (node->children[index]->count == BTSET_MAX_KEYS)
    {
        JOIN(B, split_child)(node, index);
        if (JOIN(A, less)(self, &node->keys[index], &key))
            index++;
    }
    return JOIN(B, insert_nonfull)(self, node->children[index], key);
}

static inline T *JOIN(A, insert)(A *self, T key)
{
    CTL_ASSERT_COMPARE
    T *existing = JOIN(A, find_value)(self, key);
    if (existing)
    {
#ifndef POD
        if (self->free)
            self->free(&key);
#endif
        return existing;
    }

    if (!self->root)
    {
        self->root = JOIN(B, init)(true);
        if (!self->root)
            return NULL;
        self->root->keys[0] = key;
        self->root->count = 1;
        self->size = 1;
        return &self->root->keys[0];
    }

    if (self->root->count == BTSET_MAX_KEYS)
    {
        B *root = JOIN(B, init)(false);
        if (!root)
            return NULL;
        root->children[0] = self->root;
        JOIN(B, split_child)(root, 0);
        self->root = root;
    }
    T *inserted = JOIN(B, insert_nonfull)(self, self->root, key);
    if (inserted)
        self->size++;
    return inserted;
}

static inline void JOIN(B, copy_except)(A *source, B *node, T *key, A *destination)
{
    if (!node)
        return;
    for (size_t i = 0; i < node->count; i++)
    {
        if (!node->leaf)
            JOIN(B, copy_except)(source, node->children[i], key, destination);
        if (!JOIN(A, equivalent)(source, &node->keys[i], key))
            JOIN(A, insert)(destination, source->copy(&node->keys[i]));
    }
    if (!node->leaf)
        JOIN(B, copy_except)(source, node->children[node->count], key, destination);
}

// Removes key by rebuilding the tree. Key is borrowed and not freed.
static inline bool JOIN(A, erase)(A *self, T key)
{
    if (!JOIN(A, find_value)(self, key))
        return false;
    A replacement = JOIN(A, init_from)(self);
    JOIN(B, copy_except)(self, self->root, &key, &replacement);
    JOIN(A, clear)(self);
    *self = replacement;
    return true;
}

static inline A JOIN(A, copy)(A *self)
{
    A result = JOIN(A, init_from)(self);
    for (size_t i = 0; i < self->size; i++)
        JOIN(A, insert)(&result, self->copy(JOIN(A, at)(self, i)));
    return result;
}

static inline void JOIN(A, swap)(A *left, A *right)
{
    A temporary = *left;
    *left = *right;
    *right = temporary;
}

#undef BTSET_MIN_KEYS
#undef BTSET_MAX_KEYS
#undef T
#undef A
#undef B
#undef I
#undef GI
#undef POD
#undef NOT_INTEGRAL
#undef CTL_BTSET
