/* red-black tree from set.h with a key-value struct as T
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template struct type T undefined for <ctl/map.h>"
#endif

#include <ctl/ctl.h>

// TODO C++17: emplace, try_emplace, extract, merge

#define CTL_MAP
#define HOLD
#define C map
#define set map
#define _set _map
#include <ctl/set.h>

static inline I JOIN(A, insert_or_assign)(A *self, T key)
{
    B *insert = JOIN(B, init)(key, 0);
    if (self->root)
    {
        B *node = self->root;
        while (1)
        {
            int diff = self->compare(&key, &node->value);
            if (diff == 0)
            {
                JOIN(A, free_node)(self, node);
                *node = *insert;
                return JOIN(I, iter)(self, node);
            }
            else if (diff < 0)
            {
                if (node->l)
                    node = node->l;
                else
                {
                    node->l = insert;
                    break;
                }
            }
            else
            {
                if (node->r)
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
    return JOIN(I, iter)(self, insert);
}

static inline I JOIN(A, insert_or_assign_found)(A *self, T key, int *foundp)
{
    B *insert = JOIN(B, init)(key, 0);
    if (self->root)
    {
        B *node = self->root;
        while (1)
        {
            int diff = self->compare(&key, &node->value);
            if (diff == 0)
            {
                JOIN(A, free_node)(self, node);
                *node = *insert;
                *foundp = 1;
                return JOIN(I, iter)(self, node);
            }
            else if (diff < 0)
            {
                if (node->l)
                    node = node->l;
                else
                {
                    node->l = insert;
                    break;
                }
            }
            else
            {
                if (node->r)
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
    *foundp = 0;
    return JOIN(I, iter)(self, insert);
}

#undef _set
#undef set
#undef T
#undef A
#undef B
#undef I
#undef GI
#undef CTL_MAP
