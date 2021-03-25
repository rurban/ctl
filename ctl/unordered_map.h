/* Same hash table as unordered_set
   SPDX-License-Identifier: MIT

  But with pairs, to handle the extra free/copy for key and value pairs.

  Search only the key. For most ops, just not insert/emplace.
 */

#ifndef T
#error "Template struct type T undefined for <ctl/unordered_map.h>"
#endif

#include <ctl/ctl.h>

#define CTL_UMAP
#define HOLD
#define uset umap
#define A JOIN(umap, JOIN(T, T_VALUE))

#include <ctl/unordered_set.h>

static inline I JOIN(A, insert_or_assign)(A *self, T key, T_VALUE value)
{
    B *node;
    if ((node = JOIN(A, find_node)(self, key)))
    {
        if (self->free)
            self->free(&key);
        return JOIN(I, iter)(self, node);
    }
    else
    {
        PAIR pair = JOIN(PAIR, make_pair)(key, value);
        JOIN(A, _pre_insert_grow)(self);
        return JOIN(I, iter)(self, *JOIN(A, push_cached)(self, &pair));
    }
}

static inline I JOIN(A, insert_or_assign_found)(A *self, T key, T_VALUE value, int *foundp)
{
    B *node;
    if ((node = JOIN(A, find_node)(self, key)))
    {
        if (self->free)
            self->free(&key);
        *foundp = 1;
        return JOIN(I, iter)(self, node);
    }
    else
    {
        PAIR pair = JOIN(PAIR, make_pair)(key, value);
        JOIN(A, _pre_insert_grow)(self);
        *foundp = 0;
        return JOIN(I, iter)(self, *JOIN(A, push_cached)(self, &pair));
    }
}

#undef CTL_UMAP
#undef uset
#undef T
#undef T_VALUE
#undef A
#undef B
#undef I
#undef GI
