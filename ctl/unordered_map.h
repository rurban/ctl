/* Same hash table as unordered_set
   SPDX-License-Identifier: MIT

  TODO: add pairs, to handle the extra free for key and value pairs.

  search only the key. for most ops, just not insert/emplace.
 */

#ifndef T
#error "Template struct type T undefined for <ctl/unordered_map.h>"
#endif

#include <ctl/ctl.h>

#define CTL_UMAP
#define HOLD
#define uset umap
#include <ctl/unordered_set.h>

static inline I
JOIN(A, insert_or_assign)(A* self, T value)
{
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 8);
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&value);
    B** buckets = JOIN(A, _bucket_hash)(self, hash);
#else
    B** buckets = JOIN(A, _bucket)(self, value);
#endif
    for(B* n = *buckets; n; n = n->next)
    {
#ifdef CTL_USET_CACHED_HASH
        if(n->cached_hash != hash)
            break;
#endif
        if(self->equal(&value, &n->value))
        {
            if(self->free)
                self->free(&n->value);
#ifdef CTL_USET_CACHED_HASH
            n->cached_hash = self->hash(&value);
            n->value = value;
#endif
            return JOIN(I, iter)(self, n);
        }
    }

#ifdef CTL_USET_CACHED_HASH
    JOIN(B, push)(buckets, JOIN(B, init_cached)(value, hash));
#else
    JOIN(B, push)(buckets, JOIN(B, init)(value));
#endif
    self->size++;

    if (self->size > self->max_bucket_count)
#ifdef CTL_USET_GROWTH_POWER2
        JOIN(A, _rehash)(self, 2 * self->bucket_count);
#else
        JOIN(A, rehash)(self, 2 * self->bucket_count);
#endif

    return JOIN(I, iter)(self, *buckets);
}

static inline I
JOIN(A, insert_or_assign_found)(A* self, T value, int *foundp)
{
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 8);
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&value);
    B** buckets = JOIN(A, _bucket_hash)(self, hash);
#else
    B** buckets = JOIN(A, _bucket)(self, value);
#endif
    for(B* n = *buckets; n; n = n->next)
    {
#ifdef CTL_USET_CACHED_HASH
        if(n->cached_hash != hash)
            break;
#endif
        if(self->equal(&value, &n->value))
        {
            if(self->free)
                self->free(&n->value);
#ifdef CTL_USET_CACHED_HASH
            n->cached_hash = self->hash(&value);
            n->value = value;
#endif
            *foundp = 1;
            return JOIN(I, iter)(self, n);
        }
    }

#ifdef CTL_USET_CACHED_HASH
    JOIN(B, push)(buckets, JOIN(B, init_cached)(value, hash));
#else
    JOIN(B, push)(buckets, JOIN(B, init)(value));
#endif
    self->size++;

    if (self->size > self->max_bucket_count)
#ifdef CTL_USET_GROWTH_POWER2
        JOIN(A, _rehash)(self, 2 * self->bucket_count);
#else
        JOIN(A, rehash)(self, 2 * self->bucket_count);
#endif

    *foundp = 0;
    return JOIN(I, iter)(self, *buckets);
}

#undef CTL_UMAP
#undef uset
#undef T
#undef A
#undef B
#undef I
