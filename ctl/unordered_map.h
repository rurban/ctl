/* same hash table as unordered_set */

#ifndef T
#error "Template struct type T undefined for <ctl/unordered_map.h>"
#endif

#include <ctl/ctl.h>

// TODO emplace

#define HOLD
#define uset umap
#include <ctl/unordered_set.h>

static inline void
JOIN(A, insert_or_assign)(A* self, T value)
{
    B** buckets = JOIN(A, bucket)(self, value);
    for(B* n = *buckets; n; n = n->next)
        if(self->equal(&value, &n->value))
        {
            if(self->free)
                self->free(&n->value);
            n->value = value;
            return;
        }
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(value));
    self->size++;
}

#undef uset
#undef T
#undef A
#undef B
#undef I
