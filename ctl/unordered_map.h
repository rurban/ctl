/* Same hash table as unordered_set
   SPDX-License-Identifier: MIT

  TODO: add pairs, to handle the extra free for key and value pairs.

  search only the key. for most ops, just not insert/emplace.
 */

#ifndef T
#error "Template value type T undefined for <ctl/unordered_map.h>"
#endif
#ifndef TK
#error "Template key type TK undefined for <ctl/unordered_map.h>"
#endif

#include <ctl/ctl.h>

#define CTL_UMAP
#define HOLD
#define uset umap

static inline TK JOIN(A, implicit_copy_key)(TK *key)
{
    return *key;
}

#include <ctl/unordered_set.h>

static inline I JOIN(A, insert_or_assign)(A *self, T value)
{
    B *node;
    if ((node = JOIN(A, find_node)(self, value)))
    {
        FREE_VALUE(self, value);
        return JOIN(I, iter)(self, node);
    }
    else
    {
        JOIN(A, _pre_insert_grow)(self);
        return JOIN(I, iter)(self, *JOIN(A, push_cached)(self, &value));
    }
}

static inline I JOIN(A, insert_or_assign_found)(A *self, T value, int *foundp)
{
    B *node;
    if ((node = JOIN(A, find_node)(self, value)))
    {
        FREE_VALUE(self, value);
        *foundp = 1;
        return JOIN(I, iter)(self, node);
    }
    else
    {
        JOIN(A, _pre_insert_grow)(self);
        *foundp = 0;
        return JOIN(I, iter)(self, *JOIN(A, push_cached)(self, &value));
    }
}

#undef CTL_UMAP
#undef uset
#undef T
#undef TK
#undef A
#undef B
#undef I
#undef GI
#undef POD
#undef PODK
