/* Unordered set as hashtable.
   This closed, linked list hashing has the advantage of keeping pointers
   into the set valid.
   The faster open addressing moves pointers. Maybe add another class for open
   hashes (hmap, hashtable).

   SPDX-License-Identifier: MIT

   Tunable policies:

Growth policies:
  - CTL_USET_GROWTH_PRIMED:  slower but more secure. uses all hash
                             bits. (default)
  - CTL_USET_GROWTH_POWER2:  faster, but less secure. uses only some left-most
                             bits. not recommended with inet access.

- CTL_USET_CACHED_HASH:      store the hash in the bucket. faster find when
                             unsuccesful (eg on high load factor), but needs a bit more space.

Planned:

- CTL_USET_MOVE_TO_FRONT moves a bucket in a chain not at the top
position to the top in each access, such as find and contains, not only insert.

- CTL_USET_GROWTH_FACTOR defaults to 2.0 for CTL_USET_GROWTH_POWER2 and
`1.618` for CTL_USET_GROWTH_PRIMED.

*/
#ifndef T
#error "Template type T undefined for <unordered_set.h>"
#endif

#ifdef CTL_USET_GROWTH_PRIMED // the default
# undef CTL_USET_GROWTH_POWER2
#endif
#ifdef CTL_USET_GROWTH_POWER2
# undef CTL_USET_GROWTH_PRIMED
#endif

// TODO emplace, extract, merge, equal_range

#include <stdbool.h>
#if !defined(__GNUC__) && defined(CTL_USET_GROWTH_POWER2)
#include <math.h>
#endif

#define CTL_USET
#define A JOIN(uset, T)
#define B JOIN(A, node)
#define I JOIN(A, it)

#include <ctl/ctl.h>

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
    // in STL as rehash_policy: growth_factor, max_load_factor, next_resize
    size_t bucket_count;
    size_t max_bucket_count;
    float max_load_factor;
    void (*free)(T*);
    T (*copy)(T*);
    size_t (*hash)(T*);
    int (*equal)(T*, T*);
} A;

typedef struct I
{
    CTL_B_ITER_FIELDS;
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

#ifdef CTL_USET_CACHED_HASH
static inline size_t
JOIN(I, cached_index)(A* self, B* node)
{
    return node->cached_hash % self->bucket_count;
}
#define BUCKET_INDEX(self) \
    JOIN(I, cached_index)(self->container, self->node);
#else
# define BUCKET_INDEX(self) \
    JOIN(I, index)(self->container, *self->ref);
#endif

static inline void
JOIN(I, update)(I* self)
{
    self->node = self->next;
    self->ref = &self->node->value;
    self->next = self->node->next;
    self->bucket_index = BUCKET_INDEX(self);
}

static inline int
JOIN(I, scan)(I* self)
{
    for(size_t i = self->bucket_index + 1; i < self->container->bucket_count; i++)
    {
        self->next = self->container->buckets[i];
        if(self->next)
        {
            self->bucket_index = i;
            JOIN(I, update)(self);
            return 1;
        }
    }
    return 0;
}

// for later, with redesigned iters
static inline B*
JOIN(B, next)(A* container, B* node)
{
    if (node->next)
        return node->next;
    else
    {
        size_t i = JOIN(I, index)(container, node->value) + 1;
        for(; i < container->bucket_count; i++)
        {
            B* n = container->buckets[i];
            if(n)
                return n;
        }
        return NULL;
    }
}

/*
  need two states: if next is not empty, we are still in the bucket chain, keep bucket_index.
  if empty, we need to advance to the next bucket. bucket_index++
*/
static inline void
JOIN(I, step)(I* self)
{
    if(self->next == NULL)
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

static inline int
JOIN(A, _equal)(A* self, T* a, T* b)
{
#if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->equal || !"equal undefined");
#endif
    return self->equal(a, b);
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

static inline size_t
JOIN(A, __next_prime)(size_t number)
{
    static const uint32_t primes[] = {
        2, 3, 5, 7, 11,
        13, 17, 19, 23, 29, 31,
        37, 41, 43, 47, 53, 59,
        61, 67, 71, 73, 79, 83,
        89, 97, 103, 109, 113, 127,
        137, 139, 149, 157, 167, 179,
        193, 199, 211, 227, 241, 257,
        277, 293, 313, 337, 359, 383,
        409, 439, 467, 503, 541, 577,
        619, 661, 709, 761, 823, 887,
        953, 1031, 1109, 1193, 1289, 1381,
        1493, 1613, 1741, 1879, 2029, 2179,
        2357, 2549, 2753, 2971, 3209, 3469,
        3739, 4027, 4349, 4703, 5087, 5503,
        5953, 6427, 6949, 7517, 8123, 8783,
        9497, 10273, 11113, 12011, 12983, 14033,
        15173, 16411, 17749, 19183, 20753, 22447,
        24281, 26267, 28411, 30727, 33223, 35933,
        38873, 42043, 45481, 49201, 53201, 57557,
        62233, 67307, 72817, 78779, 85229, 92203,
        99733, 107897, 116731, 126271, 136607, 147793,
        159871, 172933, 187091, 202409, 218971, 236897,
        256279, 277261, 299951, 324503, 351061, 379787,
        410857, 444487, 480881, 520241, 562841, 608903,
        658753, 712697, 771049, 834181, 902483, 976369,
        1056323, 1142821, 1236397, 1337629, 1447153, 1565659,
        1693859, 1832561, 1982627, 2144977, 2320627, 2510653,
        2716249, 2938679, 3179303, 3439651, 3721303, 4026031,
        4355707, 4712381, 5098259, 5515729, 5967347, 6456007,
        6984629, 7556579, 8175383, 8844859, 9569143, 10352717,
        11200489, 12117689, 13109983, 14183539, 15345007, 16601593,
        17961079, 19431899, 21023161, 22744717, 24607243, 26622317,
        28802401, 31160981, 33712729, 36473443, 39460231, 42691603,
        46187573, 49969847, 54061849, 58488943, 63278561, 68460391,
        74066549, 80131819, 86693767, 93793069, 101473717, 109783337,
        118773397, 128499677, 139022417, 150406843, 162723577, 176048909,
        190465427, 206062531, 222936881, 241193053, 260944219, 282312799,
        305431229, 330442829, 357502601, 386778277, 418451333, 452718089,
        489790921, 529899637, 573292817, 620239453, 671030513, 725980837,
        785430967, 849749479, 919334987, 994618837, 1076067617, 1164186217,
        1259520799, 1362662261, 1474249943, 1594975441, 1725587117
    };
    size_t min = primes[0];
    if(number < min)
        return min;
    size_t size = len(primes);
    for(size_t i = 0; i < size - 1; i++)
    {
        size_t a = primes[i + 0];
        size_t b = primes[i + 1];
        if(number >= a && number <= b)
            return number == a ? a : b;
    }
    return primes[size - 1];
}

#ifdef CTL_USET_GROWTH_POWER2
// Support huge hash tables with wordsize 64? currently we have a 32bit max_size
static inline uint32_t
JOIN(A, __next_power2)(uint32_t n)
{
#ifdef __GNUC__
    return n >= 8 ? 1 << (32 - __builtin_clz(n-1)) : 8;
#else
    return 1 << (uint32_t)ceil(log2((double)n));
#endif
}
#endif

static inline B*
JOIN(B, init)(T value)
{
    B* n = (B*) malloc(sizeof(B));
    n->value = value;
    n->next = NULL;
    return n;
}

#ifdef CTL_USET_CACHED_HASH
static inline B*
JOIN(B, init_cached)(T value, size_t hash)
{
    B* n = (B*) malloc(sizeof(B));
    n->value = value;
    n->cached_hash = hash;
    n->next = NULL;
    return n;
}
#endif

static inline size_t
JOIN(B, bucket_size)(B* self)
{
    size_t size = 0;
    for(B* n = self; n; n = n->next)
        size += 1;
    return size;
}

static inline void
JOIN(B, push)(B** bucketp, B* n)
{
#ifdef DEBUG_COLL
    if (n->next)
        LOG ("push collision %zu\n", JOIN(B, bucket_size)(n));
#endif
    n->next = *bucketp;
    *bucketp = n;
}

static inline B**
JOIN(A, _cached_bucket)(A* self, B* node)
{
#ifdef CTL_USET_CACHED_HASH
    size_t hash = node->cached_hash % self->bucket_count;
#else
    size_t hash = self->hash(&node->value) % self->bucket_count;
#endif
    //LOG ("hash -> buckets[%lu]\n", hash);
    return &self->buckets[hash];
}

static inline B**
JOIN(A, _bucket_hash)(A* self, size_t hash)
{
    return &self->buckets[ hash % self->bucket_count ];
}

static inline B**
JOIN(A, _bucket)(A* self, T value)
{
    const size_t hash = self->hash(&value) % self->bucket_count;
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
#ifndef POD
# if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(self->free || !"no uset free without POD");
# endif
    if(self->free)
        self->free(&n->value);
#else
# if defined(_ASSERT_H) && !defined(NDEBUG)
    assert(!self->free || !"uset free with POD");
# endif
#endif
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

static inline void JOIN(A, _rehash)(A* self, size_t count);

static inline void
JOIN(A, reserve)(A* self, size_t desired_count)
{
    if ((int32_t)desired_count <= 0)
        return;
#ifdef CTL_USET_GROWTH_POWER2
    const size_t new_size = JOIN(A, __next_power2)(desired_count);
    LOG("power2 growth policy %zu => %zu ", desired_count, new_size);
#else
    const size_t new_size = JOIN(A, __next_prime)(desired_count);
    LOG("primed growth policy %zu => %zu ", desired_count, new_size);
#endif
    if (new_size <= self->bucket_count)
        return;
    JOIN(A, _rehash)(self, new_size);
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
    if (desired_count == self->bucket_count)
        return;
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, reserve)(&rehashed, desired_count);
    foreach(A, self, it)
    {
        B** buckets = JOIN(A, _cached_bucket)(&rehashed, it.node);
        if (it.node != *buckets)
            JOIN(B, push)(buckets, it.node);
    }
    rehashed.size = self->size;
    LOG ("rehash temp. from %lu to %lu, load %f\n", rehashed.size, rehashed.bucket_count,
         JOIN(A, load_factor)(self));
    free(self->buckets);
    LOG ("free old\n");
    *self = rehashed;
}

// count: guaranteed growth policy (power2 or prime)
static inline void
JOIN(A, _rehash)(A* self, size_t count)
{
    // we do allow shrink here
    if (count == self->bucket_count)
        return;
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    LOG("_rehash %zu => %zu\n", self->size, count);
    JOIN(A, _reserve)(&rehashed, count);
    foreach(A, self, it)
    {
        B** buckets = JOIN(A, _cached_bucket)(&rehashed, it.node);
        if (it.node != *buckets)
            JOIN(B, push)(buckets, it.node);
    }
    rehashed.size = self->size;
    LOG ("_rehash from %lu to %lu, load %f\n", rehashed.size, count,
         JOIN(A, load_factor)(self));
    free(self->buckets);
    *self = rehashed;
    return;
}

// Note: As this is used internally a lot, don't consume (free) the key.
// The user must free it by himself.
static inline B*
JOIN(A, find)(A* self, T value)
{
    if(self->size)
    {
#ifdef CTL_USET_CACHED_HASH
        size_t hash = self->hash(&value);
        B** buckets = JOIN(A, _bucket_hash)(self, hash);
#else
        B** buckets = JOIN(A, _bucket)(self, value);
#endif
        for(B* n = *buckets; n; n = n->next)
        {
#ifdef CTL_USET_CACHED_HASH
            // faster unsucessful searches
            if(n->cached_hash != hash)
                continue;
#endif
            if(self->equal(&value, &n->value))
                // TODO move-to-front
                return n;
        }
    }
    return NULL;
}

static inline B**
JOIN(A, push_cached)(A* self, T* value)
{
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(value);
    B** buckets = JOIN(A, _bucket_hash)(self, hash);
    JOIN(B, push)(buckets, JOIN(B, init_cached)(*value, hash));
#else
    B** buckets = JOIN(A, _bucket)(self, *value);
    JOIN(B, push)(buckets, JOIN(B, init)(*value));
#endif
    //LOG ("push_bucket[%zu]\n", JOIN(B, bucket_size)(*buckets));
    self->size++;
    return buckets;
}

static inline void
JOIN(A, insert)(A* self, T value)
{
    if(JOIN(A, find)(self, value))
    {
        FREE_VALUE(self, value);
    }
    else
    {
        if(!self->bucket_count)
            JOIN(A, rehash)(self, 8);
        if (self->size + 1 > self->max_bucket_count)
        {
#ifdef CTL_USET_GROWTH_POWER2
            const size_t bucket_count = 2 * self->bucket_count;
            LOG ("rehash from %lu to %lu, load %f\n", self->size, self->bucket_count,
                 JOIN(A, load_factor)(self));
            JOIN(A, _rehash)(self, bucket_count);
#else
            // The natural growth factor is the golden ratio. libstc++ v3 and
            // libc++ use 2.0 here.
            //size_t const bucket_count = (size_t)((double)self->bucket_count * 1.618033);
            size_t const bucket_count = 1.618 * (double)self->bucket_count;
            JOIN(A, rehash)(self, bucket_count);
#endif
        }
        JOIN(A, push_cached)(self, &value);
    }
}

#ifdef DEBUG

static inline void
JOIN(A, insert_found)(A* self, T value, int* foundp)
{
    if(JOIN(A, find)(self, value))
    {
        *foundp = 1;
        FREE_VALUE(self, value);
        return;
    }
    if(JOIN(A, empty)(self))
        JOIN(A, rehash)(self, 12);
#ifdef DEBUG
    B** bucket =
#endif
    JOIN(A, push_cached)(self, &value);
    LOG ("insert_found: add bucket[%zu]\n", JOIN(B, bucket_size)(*bucket));
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

    B** buckets = JOIN(A, push_cached)(self, value);
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
        // new value, need to recalc hash
        JOIN(A, push_cached)(self, value);
        if (self->size > self->max_bucket_count)
        {
            size_t max_bucket_count = JOIN(A, max_bucket_count)(self);
            size_t new_size = JOIN(A, __next_prime)(max_bucket_count);
            JOIN(A, rehash)(self, new_size);
        }
        *foundp = 1;
        return JOIN(I, iter)(self, node);
    }

    B** buckets = JOIN(A, push_cached)(self, value);
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
    //self->max_bucket_count = 0;
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
    if (JOIN(A, find)(self, value))
    {
        FREE_VALUE(self, value);
        // TODO: the popular move-to-front strategy
        return 1UL;
    }
    else
    {
        FREE_VALUE(self, value);
        return 0UL;
    }
}

// C++20
static inline bool
JOIN(A, contains)(A* self, T value)
{
    if (JOIN(A, find)(self, value))
    {
        FREE_VALUE(self, value);
        // TODO: the popular move-to-front strategy
        return true;
    }
    else
    {
        FREE_VALUE(self, value);
        return false;
    }
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
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&value);
    B** buckets = JOIN(A, _bucket_hash)(self, hash);
#else
    B** buckets = JOIN(A, _bucket)(self, value);
#endif
    B* prev = NULL;
    B* n = *buckets;
    while (n)
    {
        B* next = n->next;
#ifdef CTL_USET_CACHED_HASH
        if(n->cached_hash != hash)
        {
            prev = n;
            n = next;
            continue;
        }
#endif
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
        //LOG ("size: %lu\n", other.size);
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

#ifdef DEBUG
// FIXME
static inline A
JOIN(A, difference)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    foreach(A, b, i) JOIN(A, erase)(&self, *i.ref);
    return self;
}
#endif

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
    size_t count_a = 0;
    size_t count_b = 0;
    foreach(A, self, it)
        if(JOIN(A, find)(self, *it.ref))
            count_a += 1;
    foreach(A, other, it)
        if(JOIN(A, find)(other, *it.ref))
            count_b += 1;
    return count_a == count_b;
}

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

#if defined(CTL_UMAP)
# include <ctl/algorithm.h>
#endif

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
