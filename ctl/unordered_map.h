/* same hash table as unordered_set

  TODO: extra free for key and value pairs.
  on str or char* key use defaults. on integral types also.
  so only free on the pair value part is needed.

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
    B* node;
    if((node = JOIN(A, find)(self, value)))
    {
        if(self->free)
            self->free(&value);
        node->value = value;
        return JOIN(I, iter)(self, node);
    }
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 12);
    B** buckets = JOIN(A, _bucket)(self, value);
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(value));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
        JOIN(A, rehash)(self, 2 * self->bucket_count);
    return JOIN(I, iter)(self, *buckets);
}

static inline I
JOIN(A, insert_or_assign_found)(A* self, T value, int *foundp)
{
    B* node;
    if((node = JOIN(A, find)(self, value)))
    {
        if(self->free)
            self->free(&value);
        *foundp = 1;
        node->value = value;
        return JOIN(I, iter)(self, node);
    }
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 12);
    B** buckets = JOIN(A, _bucket)(self, value);
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(value));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
        JOIN(A, rehash)(self, 2 * self->bucket_count);
    *foundp = 0;
    return JOIN(I, iter)(self, *buckets);
}

#undef CTL_UMAP
#undef uset
#undef T
#undef A
#undef B
#undef I
