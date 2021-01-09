/* Unordered set as hashtable.
   This closed, linked list hashing has the advantage of keeping pointers
   into the set valid.
   The faster open addressing moves pointers. Maybe add another class for open
   hashes (hmap, hashtable).

   See MIT LICENSE.
 */
#ifndef T
#error "Template type T undefined for <unordered_set.h>"
#endif

/* Growth policies
 * CTL_USET_GROWTH_PRIMED:  slower but more secure. uses all hash
 *                          bits. (default)
 * CTL_USET_GROWTH_POWER2:  faster, but less secure. uses only some lower
 *                          bits. not recommended with public inet access (json, ...)
 */

#ifdef CTL_USET_GROWTH_PRIMED // the default
# undef CTL_USET_GROWTH_POWER2
#endif
#ifdef CTL_USET_GROWTH_POWER2
# undef CTL_USET_GROWTH_PRIMED
#endif

// TODO emplace, extract, merge, equal_range

#include <ctl/ctl.h>
#include <stdbool.h>
#if !defined(__GNUC__) && defined(CTL_USET_GROWTH_POWER2)
#include <math.h>
#endif

#define CTL_USET
#define A JOIN(uset, T)
#define B JOIN(A, node)
#define I JOIN(A, it)

typedef struct B
{
    struct B* next;
    T value;
#ifdef CTL_USET_CACHED_HASH
    size_t cached_hash;
#endif
} B;

typedef struct A
{
    B** buckets;
    size_t size;
    size_t bucket_count;
    size_t max_bucket_count;
    float max_load_factor;
    void (*free)(T*);
    T (*copy)(T*);
    size_t (*hash)(T*);
    int (*equal)(T*, T*);
    int (*compare)(T*, T*);
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
            //LOG ("begin %lu %p\n", i, (void*)node);
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

static inline size_t
JOIN(I, index)(A* self, T value)
{
    return self->hash(&value) % self->bucket_count;
}

static inline void
JOIN(I, update)(I* self)
{
    self->node = self->next;
    self->ref = &self->node->value;
    self->next = self->node->next;
    self->bucket_index = JOIN(I, index)(self->container, *self->ref);
}

/*
  need two states: if next is not empty, we are still in the bucket chain, keep bucket_index.
  if empty, we need to advance to the next bucket. bucket_index++
*/
static inline void
JOIN(I, step)(I* self)
{
    // or just !self->next: advance to next bucket
    if(self->next == JOIN(A, end)(self->container))
    {
        for(size_t i = self->bucket_index + 1; i < self->container->bucket_count; i++)
            if((self->next = self->container->buckets[i]))
            {
                JOIN(I, update)(self);
                return;
            }
        self->done = 1;
    }
    else
        JOIN(I, update)(self);
}

static inline I
JOIN(I, range)(A* container, B* begin, B* end)
{
    static I zero;
    I self = zero;
    if(begin)
    {
        //LOG ("range init\n");
        self.step = JOIN(I, step);
        self.node = begin;
        self.ref = &self.node->value;
        self.next = self.node->next;
        self.end = end;
        self.container = container;
        self.bucket_index = JOIN(I, index)(container, *self.ref);
    }
    else
    {
        //LOG ("range done\n");
        self.done = 1;
    }
    return self;
}

#include <ctl/bits/container.h>

static inline I
JOIN(I, iter)(A* self, B *node)
{
    I it = JOIN(I, each)(self);
    it.node = node;
    it.ref = &it.node->value;
    it.next = it.node->next;
    return it;
}

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

// Support huge hash tables with wordsize 64? currently we have a 32bit max_size
static inline uint32_t
JOIN(A, __next_power2)(uint32_t n)
{
#ifdef __GNUC__
    return 1 << (32 - __builtin_clz(n-1));
#else
    return 1 << ceil(log2((double)n));
#endif
}

static inline B*
JOIN(B, init)(T value)
{
    B* n = (B*) malloc(sizeof(B));
    n->value = value;
    n->next = NULL;
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

static inline B*
JOIN(B, push)(B* bucket, B* n)
{
#ifdef DEBUG
    if (n->next)
        LOG ("push collision %zu\n", JOIN(B, bucket_size)(n));
#endif
    n->next = bucket;
    return n;
}

static inline B**
JOIN(A, _bucket)(A* self, T value)
{
    size_t hash = self->hash(&value) % self->bucket_count;
    //LOG ("hash -> buckets[%lu]\n", hash);
    return &self->buckets[hash];
}

static inline size_t
JOIN(A, bucket)(A* self, T value)
{
    return self->hash(&value) % self->bucket_count;
}

static inline size_t
JOIN(A, bucket_size)(A* self, size_t index)
{
    size_t size = 0;
    for(B* n = self->buckets[index]; n; n = n->next)
        size++;
    return size;
}

static inline void
JOIN(A, _free_node)(A* self, B* n)
{
    if(self->free)
        self->free(&n->value);
    free(n);
    self->size--;
}

static inline void
JOIN(A, max_load_factor)(A* self, float f)
{
    self->max_load_factor = f;
}

static inline size_t
JOIN(A, max_bucket_count)(A* self)
{
    return (size_t) (self->size / self->max_load_factor);
}

static inline float
JOIN(A, load_factor)(A* self)
{
    return (float) self->size / (float) self->bucket_count;
}

// new_size must fit the growth policy: power2 or prime
static inline void
JOIN(A, _reserve)(A* self, const size_t new_size)
{
    if (self->bucket_count == new_size)
        return;
    if (self->buckets)
    {
        LOG("_reserve %zu realloc => %zu\n", self->bucket_count, new_size);
        self->buckets = (B**) realloc(self->buckets, new_size * sizeof(B*));
        memset(&self->buckets[self->bucket_count], 0, (new_size - self->bucket_count) * sizeof(B*));
    }
    else
    {
        LOG("_reserve %zu calloc => %zu\n", self->bucket_count, new_size);
        self->buckets = (B**) calloc(new_size, sizeof(B*));
    }
    self->bucket_count = new_size;
    if (self->size > 127)
        self->max_bucket_count = JOIN(A, max_bucket_count(self));
    else
        self->max_bucket_count = new_size; // ignore custom load factors here
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert (self->buckets && "out of memory");
#endif
}

static inline void
JOIN(A, reserve)(A* self, size_t desired_count)
{
#ifdef CTL_USET_GROWTH_POWER2
    const size_t new_size = JOIN(A, __next_power2)(desired_count);
#else
    const size_t new_size = JOIN(A, __next_prime)(desired_count);
#endif
    //LOG("growth policy %zu => %zu ", desired_count, new_size);
    JOIN(A, _reserve)(self, new_size);
}

static inline A
JOIN(A, init)(size_t (*_hash)(T*), int (*_equal)(T*, T*))
{
    static A zero;
    A self = zero;
    self.hash = _hash;
    self.equal = _equal;
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
    _JOIN(A, _set_default_methods)(&self);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
    JOIN(A, max_load_factor)(&self, 1.0f); // better would be 0.95
    JOIN(A, _reserve)(&self, 8);
    return self;
}

static inline void
JOIN(A, rehash)(A* self, size_t desired_count)
{
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    size_t bucket_count = self->bucket_count;
    JOIN(A, reserve)(&rehashed, desired_count);
    if (bucket_count == rehashed.bucket_count)
        return;
    foreach(A, self, it)
    {
        B** buckets = JOIN(A, _bucket)(&rehashed, it.node->value);
        if (it.node != *buckets)
            *buckets = JOIN(B, push)(*buckets, it.node);
    }
    rehashed.size = self->size;
    LOG ("rehash from %lu to %lu, load %f\n", rehashed.size, rehashed.bucket_count,
         JOIN(A, load_factor)(self));
    free(self->buckets);
    *self = rehashed;
}

// count: guaranteed growth policy (power2 or prime)
static inline void
JOIN(A, _rehash)(A* self, size_t count)
{
    if (count == self->bucket_count)
        return;
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    LOG("_rehash %zu => %zu\n", self->size, count);
    JOIN(A, _reserve)(&rehashed, count);
    foreach(A, self, it)
    {
        B** buckets = JOIN(A, _bucket)(&rehashed, it.node->value);
        if (it.node != *buckets)
            *buckets = JOIN(B, push)(*buckets, it.node);
    }
    rehashed.size = self->size;
    LOG ("_rehash from %lu to %lu, load %f\n", rehashed.size, count,
         JOIN(A, load_factor)(self));
    free(self->buckets);
    *self = rehashed;
}

static inline B*
JOIN(A, find)(A* self, T value)
{
    if(self->size)
    {
        B** buckets = JOIN(A, _bucket)(self, value);
        for(B* n = *buckets; n; n = n->next)
            if(self->equal(&value, &n->value))
                return n;
    }
    return NULL;
}

static inline void
JOIN(A, insert)(A* self, T value)
{
    if(JOIN(A, find)(self, value))
    {
        if(self->free)
            self->free(&value);
    }
    else
    {
        if(!self->bucket_count)
            JOIN(A, rehash)(self, 8);
        else if (self->size >= self->max_bucket_count)
        {
#ifdef CTL_USET_GROWTH_POWER2
            const size_t bucket_count = 2 * self->bucket_count;
            LOG ("rehash from %lu to %lu, load %f\n", self->size, self->bucket_count,
                 JOIN(A, load_factor)(self));
            JOIN(A, _rehash)(self, bucket_count);
#else
            // The natural growth factor is the golden ratio.
            //size_t const bucket_count = (size_t)((double)self->bucket_count * 1.618033);
            size_t const bucket_count = 1.618 * (double)self->bucket_count;
            JOIN(A, rehash)(self, bucket_count);
#endif
        }
        B** bucket = JOIN(A, _bucket)(self, value);
        *bucket = JOIN(B, push)(*bucket, JOIN(B, init)(value));
        //LOG ("insert: add bucket, collisions: %zu\n", JOIN(B, bucket_size)(*bucket));
        self->size++;
    }
}

#ifdef DEBUG

static inline void
JOIN(A, insert_found)(A* self, T value, int* foundp)
{
    if(JOIN(A, find)(self, value))
    {
        *foundp = 1;
        if(self->free)
            self->free(&value);
        return;
    }
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 12);
    B** bucket = JOIN(A, _bucket)(self, value);
    *bucket = JOIN(B, push)(*bucket, JOIN(B, init)(value));
    LOG ("insert_found: add bucket[%zu]\n", JOIN(B, bucket_size)(*bucket));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
        JOIN(A, rehash)(self, 2 * self->bucket_count);
    *foundp = 0;
}

static inline I
JOIN(A, emplace)(A* self, T* value)
{
    B* node;
    if ((node = JOIN(A, find)(self, *value)))
        return JOIN(I, iter)(self, node);

    B** buckets = JOIN(A, _bucket)(self, *value);
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(*value));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
        JOIN(A, rehash)(self, 2 * self->bucket_count);
    return JOIN(I, iter)(self, *buckets);
}

static inline I
JOIN(A, emplace_found)(A* self, T* value, int* foundp)
{
    B* node;
    if ((node = JOIN(A, find)(self, *value)))
    {
        if(!self->bucket_count)
            JOIN(A, rehash)(self, 12);
        B** bucket = JOIN(A, _bucket)(self, *value);
        *bucket = JOIN(B, push)(*bucket, JOIN(B, init)(*value));
        self->size++;
        if (self->size > self->max_bucket_count)
        {
            size_t max_bucket_count = JOIN(A, max_bucket_count)(self);
            size_t new_size = JOIN(A, __next_prime)(max_bucket_count);
            JOIN(A, rehash)(self, new_size);
        }
        *foundp = 1;
        return JOIN(I, iter)(self, node);
    }

    B** buckets = JOIN(A, _bucket)(self, *value);
    *buckets = JOIN(B, push)(*buckets, JOIN(B, init)(*value));
    self->size++;
    if (JOIN(A, load_factor)(self) > self->max_load_factor)
        JOIN(A, rehash)(self, 2 * self->bucket_count);
    *foundp = 0;
    return JOIN(I, iter)(self, *buckets);
}
#endif

static inline void
JOIN(A, clear)(A* self)
{
    foreach(A, self, it)
        JOIN(A, _free_node)(self, it.node);
    memset(self->buckets, 0, self->bucket_count * sizeof(B*));
    /* for(size_t i = 0; i < self->bucket_count; i++)
        self->buckets[i] = NULL; */
    self->size = 0;
    self->max_bucket_count = 0;
}

static inline void
JOIN(A, free)(A* self)
{
    LOG("free calloc %zu, %zu\n", self->bucket_count, self->size);
    JOIN(A, clear)(self);
    free(self->buckets);
    self->buckets = NULL;
    self->bucket_count = 0;
}

static inline size_t
JOIN(A, count)(A* self, T value)
{
    size_t count = 0;
    foreach(A, self, it)
        if(self->equal(it.ref, &value))
            count++;
    return count;
}

// C++20
static inline bool
JOIN(A, contains)(A* self, T value)
{
    foreach(A, self, it)
        if(self->equal(it.ref, &value))
            return true;
    return false;
}

static inline void
JOIN(A, _linked_erase)(A* self, B** bucket, B* n, B* prev, B* next)
{
    JOIN(A, _free_node)(self, n);
    if(prev)
        prev->next = next;
    else
        *bucket = next;
}

static inline void
JOIN(A, erase)(A* self, T value)
{
    B** buckets = JOIN(A, _bucket)(self, value);
    B* prev = NULL;
    B* n = *buckets;
    while (n)
    {
        B* next = n->next;
        if(self->equal(&value, &n->value))
        {
            JOIN(A, _linked_erase)(self, buckets, n, prev, next);
            break;
        }
        prev = n;
        n = next;
    }
}

static inline size_t
JOIN(A, erase_if)(A* self, int (*_match)(T*))
{
    size_t erases = 0;
    for(size_t i = 0; i < self->bucket_count; i++)
    {
        B** buckets = &self->buckets[i];
        B* prev = NULL;
        B* n = *buckets;
        while(n)
        {
            B* next = n->next;
            if(_match(&n->value))
            {
                JOIN(A, _linked_erase)(self, buckets, n, prev, next);
                erases += 1;
            }
            else
                prev = n;
            n = next;
        }
    }
    return erases;
}

static inline A
JOIN(A, copy)(A* self)
{
    LOG ("copy\norig size: %lu\n", self->size);
    A other = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, _reserve)(&other, self->bucket_count);
    foreach(A, self, it) {
        LOG ("size: %lu\n", other.size);
        JOIN(A, insert)(&other, self->copy(it.ref));
    }
    LOG ("final size: %lu\n", other.size);
    return other;
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

// different to the shared equal
static inline int
JOIN(A, equal)(A* self, A* other)
{
    if(self->size != other->size)
        return 0;
    A diff = JOIN(A, difference)(self, other);
    int result = JOIN(A, empty)(&diff);
    JOIN(A, free)(&diff);
    return result;
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

#undef POD
#ifndef HOLD
#undef A
#undef B
#undef I
#undef T
#else
#undef HOLD
#endif
#undef CTL_USET

#ifdef USE_INTERNAL_VERIFY
#undef USE_INTERNAL_VERIFY
#endif
