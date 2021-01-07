/* Unordered set as hashtable.
   This closed, linked list hashing has the advantage of keeping pointers
   into the set valid.
   The faster open addressing moves pointers. Maybe add another class for open
   hashes (hmap, hashtable).
 */
#ifndef T
#error "Template type T undefined for <unordered_set.h>"
#endif

// TODO emplace, extract, merge, contains, erase_if, equal_range

#include <ctl/ctl.h>

#define A JOIN(uset, T)
#define B JOIN(A, node)
#define I JOIN(A, it)
#define PAIR JOIN(A, pair)

typedef struct B
{
    struct B* next;
    T value;
} B;

typedef struct A
{
    B** buckets;
    size_t size;
    size_t bucket_count;
    float max_load_factor;
    void (*free)(T*);
    T (*copy)(T*);
    size_t (*hash)(T*);
    int (*equal)(T*, T*);
} A;

typedef struct I
{
    CTL_COMMONFIELDS_ITER;
    A* container;
    size_t bucket_index;
} I;

static inline B*
JOIN(A, begin)(A* self)
{
    for(size_t i = 0; i < self->bucket_count; i++)
    {
        B* node = self->buckets[i];
        if(node) {
            LOG ("begin %lu %p\n", i, (void*)node);
            return node;
        }
    }
    return NULL;
}

static inline B*
JOIN(A, end)(A* self)
{
    (void) self;
    return NULL;
}

static inline void
JOIN(I, update)(I* self, size_t bucket_index)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (self->node != self->next);
#endif
    self->node = self->next;
    self->ref = &self->node->value;
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (self->next != self->node->next);
#endif
    self->next = self->node->next;
    LOG ("update: bucket_index %lu -> %lu of %lu\n", self->bucket_index,
         bucket_index, self->container->bucket_count);
    self->bucket_index = bucket_index;
}

/*
  need two states: if next is not empty, we are still in the bucket chain.
  if empty, we need to advance to the next bucket.
*/
static inline void
JOIN(I, step)(I* self)
{
    // or just !self->next
    if(self->next == JOIN(A, end)(self->container))
    {
        for(size_t i = self->bucket_index + 1; i < self->container->bucket_count; i++)
        {
            LOG("step buckets[%lu] of %lu\n", i, self->container->bucket_count);
            B* next = self->container->buckets[i];
            if(next != NULL) // && self->next != next) DEBUG only
            {
                self->next = next;
                LOG ("step found in buckets[%lu]\n", i);
                JOIN(I, update)(self, i);
                return;
            }
        }
        LOG ("step done\n");
        self->bucket_index = 0;
        self->done = 1;
    }
    else
    {   // still in chain. advance to next in chain
        LOG ("step next\n");
        JOIN(I, update)(self, self->bucket_index);
    }
}

static inline I
JOIN(I, range)(A* container, B* begin, B* end)
{
    static I zero;
    I self = zero;
    if(begin)
    {
        self.step = JOIN(I, step);
        self.node = begin;
        self.ref = &self.node->value;
        self.next = self.node->next;
        self.end = end;
        self.container = container;
        //self.hash = self.container->hash(self.ref);
    }
    else
    {
        LOG ("range done\n");
        //self.bucket_index = 0;
        self.done = 1;
    }
    return self;
}

#include <ctl/_share.h>

// TODO:
// primes[] obtained experimentally - is there a quicker way to get more primes
// other than checking bucket_count() on std::unorderd_set::insert()?
static inline int
JOIN(A, __next_prime)(size_t n)
{
    const size_t primes[] = {
        13, 29, 59, 127, 257, 541, 1109, 2357, 5087, 10273, 20753,
        42043, 85229, 172933, 351061, 712697, 1447153, 2938679,
        5967347, 12117689, 24607243, 49969847, 101473717
    };
    for(size_t i = 0; i < len(primes); i++)
    {
        size_t p = primes[i];
        if(n < p)
            return p;
    }
    return primes[n - 1];
}

static inline B*
JOIN(B, init)(T value)
{
    B* n = (B*) malloc(sizeof(B));
    n->value = value;
    n->next = NULL;
    return n;
}

static inline B*
JOIN(B, push)(B* bucket, B* n)
{
    n->next = bucket;
    return n;
}

static inline size_t
JOIN(B, bucket_size)(B* self)
{
    size_t size = 0;
    for(B* n = self; n; n = n->next)
        size += 1;
    return size;
}

static inline B**
JOIN(A, bucket)(A* self, T value)
{
    size_t hash = self->hash(&value) % self->bucket_count;
    LOG ("hash -> buckets[%lu]\n", hash);
    return &self->buckets[hash];
}

static inline size_t
JOIN(A, bucket_size)(A* self, size_t index)
{
    size_t size = 0;
    for(B* n = self->buckets[index]; n; n = n->next)
        size += 1;
    return size;
}

static inline void
JOIN(A, free_node)(A* self, B* n)
{
    if(self->free)
        self->free(&n->value);
    free(n);
}

static inline void
JOIN(A, max_load_factor)(A* self, float f)
{
    self->max_load_factor = f;
}

static inline float
JOIN(A, max_bucket_count)(A* self)
{
    return (float) (self->size / self->max_load_factor);
}

static inline float
JOIN(A, load_factor)(A* self)
{
    return (float) self->size / (float) self->bucket_count;
}

static inline void
JOIN(A, reserve)(A* self, size_t desired_count)
{
    size_t new_size = JOIN(A, __next_prime)(desired_count);
    if (self->bucket_count == new_size)
        return;
    if (self->buckets)
    {
        LOG("reserve %zu realloc => %zu\n", self->bucket_count, new_size);
        self->buckets = (B**) realloc(self->buckets, new_size * sizeof(B*));
    }
    else
        self->buckets = (B**) calloc(new_size, sizeof(B*));
    self->bucket_count = new_size;
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (self->buckets || !"out of memory");
#endif
}

static inline A
JOIN(A, init)(size_t (*_hash)(T*), int (*_equal)(T*, T*))
{
    static A zero;
    A self = zero;
    self.hash = _hash;
    self.equal = _equal;
#ifdef POD
#undef POD
    self.copy = JOIN(A, implicit_copy);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    JOIN(A, max_load_factor)(&self, 0.95f);
    JOIN(A, reserve)(&self, 12);
    return self;
}

static inline void
JOIN(A, rehash)(A* self, size_t desired_count)
{
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, reserve)(&rehashed, desired_count);
    foreach(A, self, it)
    {
        B** buckets = JOIN(A, bucket)(&rehashed, it.node->value);
        *buckets = JOIN(B, push)(*buckets, it.node);
    }
    rehashed.size = self->size;
    free(self->buckets);
    *self = rehashed;
}

static inline B*
JOIN(A, find)(A* self, T value)
{
    if(!JOIN(A, empty)(self))
    {
        B** buckets = JOIN(A, bucket)(self, value);
        for(B* n = *buckets; n; n = n->next)
            if(self->equal(&value, &n->value))
                return n;
    }
    return NULL;
}

static inline void
JOIN(A, insert)(A* self, T value)
{
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 12);
    if(JOIN(A, find)(self, value))
    {
        if(self->free)
            self->free(&value);
    }
    else
    {
        B** bucket = JOIN(A, bucket)(self, value);
        *bucket = JOIN(B, push)(*bucket, JOIN(B, init)(value));
        LOG ("insert: add bucket[%zu]\n", JOIN(B, bucket_size)(*bucket));
        self->size++;
        if (JOIN(A, load_factor)(self) > self->max_load_factor)
        {
            size_t bucket_count = 2 * self->bucket_count;
            LOG ("resize from %lu to %lu, load %f\n", self->size, bucket_count,
                 JOIN(A, load_factor)(self));
            JOIN(A, rehash)(self, bucket_count);
        }
    }
}

#if 0
static inline I*
JOIN(A, emplace)(A* self, ...)
{
    B** buckets = JOIN(A, bucket)(self, value);
    for(B* n = *buckets; n; n = n->next)
        if(self->equal(&value, &n->value))
        {
            if(self->free)
                self->free(&value);
            return (PAIR){JOIN(JOIN(A, it), each)(self), false};
        }
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(value));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
    {
        size_t max_bucket_count = JOIN(A, max_bucket_count)(self);
        size_t new_size = JOIN(A, __next_prime)(max_bucket_count);
        JOIN(A, rehash)(self, new_size);
    }
    return JOIN(JOIN(A, it), each)(*buckets);
}
#endif

static inline void
JOIN(A, free)(A* self)
{
    foreach(A, self, it)
        JOIN(A, free_node)(self, it.node);
    free(self->buckets);
}

static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, it)
        if(self->equal(it.ref , &value))
            count++;
    return count;
}

static inline void
JOIN(A, erase)(A* self, T value)
{
    B** buckets = JOIN(A, bucket)(self, value);
    B* prev = NULL;
    for(B* n = *buckets; n; n = n->next)
    {
        if(self->equal(&value, &n->value))
        {
            B* next = n->next;
            JOIN(A, free_node)(self, n);
            if(prev)
                prev->next = next;
            self->size--;
            break;
        }
        prev = n;
    }
}

static inline void
JOIN(A, clear)(A* self)
{
    foreach(A, self, i) JOIN(A, erase)(self, *i.ref);
    JOIN(A, free)(self);
}

static inline A
JOIN(A, copy)(A* self)
{
    LOG ("copy\norig size: %lu\n", self->size);
    A other = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, reserve)(&other, self->bucket_count);
    foreach(A, self, it) {
        LOG ("size: %lu\n", other.size);
        JOIN(A, insert)(&other, self->copy(it.ref));
    }
    LOG ("final size: %lu\n", other.size);
    return other;
}

static inline void
JOIN(A, remove_if)(A* self, int (*_match)(T*))
{
    for(size_t i = 0; i < self->bucket_count; i++)
    {
        B** bucket = &self->buckets[i];
        B* prev = NULL;
        for(B* n = *bucket; n; n = n->next)
        {
            if(_match(&n->value))
            {
                B* next = n->next;
                JOIN(A, free_node)(self, n);
                if(prev)
                    prev->next = next;
            }
            prev = n;
        }
    }
}

static inline A
JOIN(A, intersection)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    foreach(A, a, i)
        if(JOIN(A, find)(b, *i.ref))
            JOIN(A, insert)(&self, self.copy(i.ref));
    return self;
}

static inline A
JOIN(A, union)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    foreach(A, a, i) JOIN(A, insert)(&self, self.copy(i.ref));
    foreach(A, b, i) JOIN(A, insert)(&self, self.copy(i.ref));
    return self;
}

static inline A
JOIN(A, difference)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
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

#ifndef HOLD
#undef A
#undef B
#undef I
#undef T
#else
#undef HOLD
#endif
