/* flat_hash_map, with unordered map API.
   Translated from Google's C++ Abseil swisstable.
   No pointer and no iterator stability.

   WIP This is the TK variant, in contrast to the pair/map variants with
   T_VALUE. See also stanford hash in hashmap.h for integer keys, as cuckoo
   table, or github.com/greg7mdp/parallel-hashmap for pctl (multithreaded).

   SPDX-License-Identifier: MIT

   Default max_load_factor = 0.75
   See also github.com/LIMachi/swiss-table
*/
#ifndef T
# error "Template valuetype T undefined for <ctl/swisstable.h>"
#endif
#ifndef TK
# error "Template keytype TK undefined for <ctl/swisstable.h>"
#endif

#include <stdlib.h>
#include <stdbool.h>
#if !defined(__GNUC__) // no __builtin_clz
#include <math.h>
#endif
#include <immintrin.h>

#define CTL_HMAP
#define CTL_UMAP
#define CTL_USET
#define A JOIN(hmap, TK)
#define B JOIN(A, node)
#define I JOIN(A, it)
#define GI JOIN(A, it)

#include <ctl/ctl.h>

#define HMAP_CONTROL_SIZE (16)
#define HMAP_GROUP_SIZE (16)
#define HMAP_VALUE_SIZE (HMAP_CONTROL_SIZE * HMAP_GROUP_SIZE)
#define HMAP_LOAD_FACTOR 0.75
#define HMAP_EXPAND_FACTOR (2)

typedef enum e_hmap_control
{
    HMAP_EMPTY = 0b10000000,
    HMAP_DELETED = 0b11111111,
    HMAP_FULL_MASK = 0b01111111
} t_hmap_control;

#ifdef __SSE2__
# include <emmintrin.h>
# include <immintrin.h>
// TODO SSSE3 tmmintrin.h

# define HMAP_I128         __m128i
# define HMAP_I128_0XFF    _mm_cvtsi32_si128(0xFF)
# define HMAP_I128_DELETED _mm_cvtsi32_si128(HMAP_DELETED)
# define HMAP_I128_EMPTY   _mm_cvtsi32_si128(HMAP_EMPTY)

#else
#if defined(__x86_64__) || defined(__x86_64) || defined(_M_AMD64) || \
    defined(_M_X64) || defined(_M_X86) || defined(__i386)
# pragma message "Missing SSE2 -march= or -msse2 CFLAGS. Using slower functions instead"
#endif

 typedef unsigned char t_hmap_i128[HMAP_CONTROL_SIZE];

# define HMAP_I128 t_hmap_i128

#endif

/*
** __m128i control -> t_hmap_control(char)[16]
*/
typedef struct B
{
    HMAP_I128 control;
    TK        key[HMAP_CONTROL_SIZE];
} B;

typedef struct A
{
    size_t num_groups;
    size_t size;
    B *groups;
    T *values;
    float max_load_factor;
    void   (*free)(T*);
    T      (*copy)(T*);
    void   (*free_key)(TK*);
    TK     (*copy_key)(TK*);
    size_t (*hash)(TK*);
    int    (*equal)(TK*, TK*);
} A;

struct s_hmap_hash
{
    size_t meta : 7;
    size_t position : __WORDSIZE - 7;
};

typedef union u_hmap_hash
{
    struct s_hmap_hash	h;
    size_t		s;
} t_hmap_hash;

//#include <ctl/pair.h>
#include <ctl/bits/iterator_vtable.h>

typedef struct I
{
    CTL_T_ITER_FIELDS;
} I;

#include <ctl/bits/iterators.h>

static inline I JOIN(I, iter)(A* self, T* ref)
{
    static I zero;
    I iter = zero;
    iter.ref = ref;
    iter.end = &self->values[self->size]; // 1 past the end
    iter.container = self;
    return iter;
}

static inline I JOIN(I, iter_index)(A* self, size_t index)
{
    static I zero;
    I iter = zero;
    iter.ref = &self->values[index];
    iter.end = &self->values[self->size]; // 1 past the end
    iter.container = self;
    return iter;
}

static inline I
JOIN(A, begin)(A* self)
{
    return JOIN(I, iter)(self, &self->values[0]);
}
static inline I
JOIN(A, end)(A* self)
{
    return JOIN(I, iter)(self, &self->values[self->size]); // 1 past the end
}
static inline T*
JOIN(I, ref)(I* iter)
{
    return iter->ref;
}
// We don't support uset ranges. But hmap ranges are easier, even if random.
static inline int
JOIN(I, done)(I* iter)
{
    return iter->ref == iter->end;
}

static inline void
JOIN(I, next)(I* iter)
{
    iter->ref++;
}
static inline I*
JOIN(I, advance)(I* iter, long i)
{
    iter->ref += i;
    return iter;
}
static inline void
JOIN(I, advance_end)(I* iter, long n)
{
    iter->end += n;
}
static inline void
JOIN(I, range)(I *first, I *last)
{
    last->end = first->end = last->ref;
    ASSERT(first->end >= first->ref);
}
static inline void
JOIN(I, set_pos)(I *iter, I *other)
{
    iter->ref = other->ref;
}

static inline void
JOIN(I, set_end)(I *iter, I *last)
{
    iter->end = last->ref;
    ASSERT(iter->end >= iter->ref);
}
static inline void
JOIN(I, set_done)(I* iter)
{
    iter->ref = iter->end;
}
static inline void
JOIN(I, prev)(I* iter)
{
    iter->ref--;
}

static inline int
JOIN(A, _equal)(A* self, TK* a, TK* b)
{
    ASSERT(self->equal || !"equal undefined");
    return self->equal(a, b);
}

static inline A JOIN(A, init_from)(A *copy);
static inline A JOIN(A, copy)(A *self);
static inline void JOIN(A, insert)(A *self, T value);
static inline void JOIN(A, inserter)(A *self, T value);

#include <ctl/bits/container.h>

// No huge hash tables with wordsize 64. We support only 32bit max_size.
static inline uint32_t
JOIN(A, __next_power2)(uint32_t n)
{
#ifdef __GNUC__
    return n >= 8 ? 1 << (32 - __builtin_clz(n-1)) : 8;
#else
    return 1 << (uint32_t)ceil(log2((double)n));
#endif
}

static inline B*
JOIN(B, group_hash)(A* self, size_t hash)
{
    return &self->groups[ hash % self->num_groups ];
}

static inline B*
JOIN(B, group)(A* self, TK* key)
{
    t_hmap_hash hash;
    hash.s = self->hash(key);
    return &self->groups[hash.h.position % self->num_groups];
}

static inline size_t
JOIN(B, group_index)(A* self, TK* key)
{
    t_hmap_hash hash;
    hash.s = self->hash(key);
    return hash.h.position % self->num_groups;
}

/* need gi and ref
static inline void
JOIN(A, _free_node)(A* self, B* n)
{
#ifndef POD
    ASSERT(self->free || !"no hmap free without POD");
    if(self->free)
        self->free(&n->value);
#else
    ASSERT(!self->free || !"uset free with POD");
#endif
    free(n);
    self->size--;
}
*/

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
    return (float) self->size / (float) self->num_groups;
}

// new_size must fit the growth policy power2
static inline void
JOIN(A, _reserve)(A* self, const size_t new_size)
{
    if (self->num_groups == new_size)
        return;
    size_t old_bucket_count = self->num_groups;
    // FIXME
    #define BUCKET_SIZE 32
    self->num_groups = (new_size + BUCKET_SIZE - 1) / BUCKET_SIZE;
    if (self->groups)
    {
        B* groups;
        int r = posix_memalign((void**)&groups, 32, self->num_groups * sizeof(B));
#if !defined(_ASSERT_H) || defined(NDEBUG)
	(void)r;
#endif
        ASSERT(!r && "posix_memalign in hmap");
        memmove(&groups, &self->groups, old_bucket_count * sizeof(B));
        size_t i = self->num_groups;
#ifdef __SSE2__
        while (i--)
            self->groups[i].control = _mm_set1_epi8((char)HMAP_EMPTY);
#else
        size_t j;
        while (i-- && (j = HMAP_CONTROL_SIZE))
            while (j--)
                self->groups[i].control[j] = HMAP_EMPTY;
#endif
        /*
        for (uint32_t i = 0; i < self->num_groups; i++) {
            for (size_t j = 0; j < BUCKET_SIZE; j++) {
                self->groups[i].keys[j] = INVALID_KEY;
            }
        }
        */
    }
    else
    {
        int r = posix_memalign((void**)&self->groups, 32, self->num_groups * sizeof(B));
#if !defined(_ASSERT_H) || defined(NDEBUG)
	(void)r;
#endif
        ASSERT(!r && "posix_memalign in hmap");
        size_t i = self->num_groups;
#ifdef __SSE2__
        while (i--)
            self->groups[i].control = _mm_set1_epi8((char)HMAP_EMPTY);
#else
        size_t j;
        while (i-- && (j = HMAP_CONTROL_SIZE))
            while (j--)
                self->groups[i].control[j] = HMAP_EMPTY;
#endif
        //LOG("_reserve %zu calloc => %zu\n", self->num_groups, new_size);
    }
    //if (self->size > 127)
    //    self->max_bucket_count = JOIN(A, max_bucket_count(self));
    //else
    //    self->max_bucket_count = new_size; // ignore custom load factors here
    ASSERT (self->groups && "out of memory");
}

static inline void JOIN(A, _rehash)(A* self, size_t count);

static inline void
JOIN(A, reserve)(A* self, size_t desired_count)
{
    if ((int32_t)desired_count <= 0)
        return;
    const size_t new_size = JOIN(A, __next_power2)(desired_count);
    if (new_size <= self->num_groups)
        return;
    JOIN(A, _rehash)(self, new_size);
}

static inline TK JOIN(A, implicit_copy_key)(TK *key)
{
    return *key;
}

static inline A
JOIN(A, init)(size_t (*_hash)(TK*), int (*_equal)(TK*, TK*))
{
    static A zero;
    A self = zero;
    self.groups = (B*)malloc(sizeof(B) * HMAP_GROUP_SIZE);
    self.values = (T*)malloc(sizeof(T) * HMAP_VALUE_SIZE);
    if (self.groups == NULL || self.values == NULL)
    {
        free (self.groups);
        free (self.values);
        return self;
    }
    self.hash = _hash;
    self.equal = _equal;
#ifdef POD
    self.copy = JOIN(A, implicit_copy);
#else
    self.free = JOIN(T, free);
    self.copy = JOIN(T, copy);
#endif
#ifdef PODK
    self.copy_key = JOIN(A, implicit_copy_key);
#else
    self.free_key = JOIN(TK, free);
    self.copy_key = JOIN(TK, copy);
#endif
    _JOIN(A, _set_default_methods)(&self);
    self.max_load_factor = HMAP_LOAD_FACTOR;
    self.num_groups = HMAP_GROUP_SIZE;
    size_t i = self.num_groups;
#ifdef __SSE2__
    while (i--)
        self.groups[i].control = _mm_set1_epi8((char)HMAP_EMPTY);
#else
    size_t j;
    while (i-- && (j = HMAP_CONTROL_SIZE))
        while (j--)
            self.groups[i].control[j] = HMAP_EMPTY;
#endif
    return self;
}

static inline A
JOIN(A, init_from)(A* copy)
{
    static A zero;
    A self = zero;
    self.copy_key = copy->copy_key;
    self.free_key = copy->free_key;
    self.free = copy->free;
    self.copy = copy->copy;
    self.hash = copy->hash;
    self.equal = copy->equal;
    self.max_load_factor = copy->max_load_factor;
    return self;
}

static inline void
JOIN(A, rehash)(A* self, size_t desired_count)
{
    if (desired_count == self->num_groups)
        return;
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, reserve)(&rehashed, desired_count);
    /* FIXME
    foreach(A, self, it)
    {
        B** groups = JOIN(A, _cached_bucket)(&rehashed, it.node);
        if (it.node != *groups)
            JOIN(B, push)(groups, it.node);
    }
    */
    rehashed.size = self->size;
    //LOG ("rehash temp. from %lu to %lu, load %f\n", rehashed.size, rehashed.bucket_count,
    //     JOIN(A, load_factor)(self));
    free(self->groups);
    //LOG ("free old\n");
    *self = rehashed;
}

// count: guaranteed growth policy power2
static inline void
JOIN(A, _rehash)(A* self, size_t count)
{
    // we do allow shrink here
    if (count == self->num_groups)
        return;
    A rehashed = JOIN(A, init)(self->hash, self->equal);
    //LOG("_rehash %zu => %zu\n", self->size, count);
    JOIN(A, _reserve)(&rehashed, count);
    //foreach(A, self, it)
    //{
    //    B** groups = JOIN(A, _cached_bucket)(&rehashed, it.node);
    //    if (it.node != *groups)
    //        JOIN(B, push)(groups, it.node);
    //}
    rehashed.size = self->size;
    //LOG ("_rehash from %lu to %lu, load %f\n", rehashed.size, count,
    //     JOIN(A, load_factor)(self));
    free(self->groups);
    *self = rehashed;
    return;
}

static inline size_t JOIN(B, value_index)(A* self, T* ref)
{
    return ref - self->values;
}

#ifndef __SSE2__
static inline int JOIN(B, _get_match_mask)(char byte, t_hmap_i128 control)
{
  int i;
  int out;

  out = 0;
  i = HMAP_CONTROL_SIZE;
  while (i--)
    if (control[i] == byte)
      out |= 1 << i;
  return out;
}
#endif

/* Don't consume (free) the key. The user must free it by himself.
 * Returns self->num_groups if not found.
 */
static inline size_t
JOIN(A, find_index)(A* self, TK key)
{
    if (self->size)
    {
        t_hmap_hash hash;
        size_t gi;
	hash.s = self->hash(&key);
        gi = hash.h.position % self->num_groups;
        while (1) {
            int i = -1;
            B g = self->groups[gi];
#ifdef __SSE2__
            /* As explained in the talk:
             *  _mm_set1_epi8 -> bytes1[16]{H2(hash)}
             *  _mmcmpeq_epi8 -> cmp(bytes1[16], bytes2[16])->bytes3[16] (m: 0xFF, f: 0x00)
             *  _mm_movemask_epi8 -> bytes3[16] -> bytes[2] (0xFF -> 1, 0x00 -> 0)
             * Given a meta 96, finds in a group of 16 metas all that match 96
             * and represent the match in a 16 bit mask:
             *  7F,DF,96,32,F1,F8,EB,43,7F,DF,96,32,F1,F8,EB,43 _ 96 -> 0b0010000000100000
             */
            int match = _mm_movemask_epi8(
                _mm_cmpeq_epi8(_mm_set1_epi8(hash.h.meta), g.control));
#else
            int match = JOIN(B, _get_match_mask)(hash.h.meta, g.control);
#endif
            while (++i < HMAP_CONTROL_SIZE)
                if (match & (1 << i) && LIKELY(self->equal(&g.key[i], &key)))
                    return gi * HMAP_CONTROL_SIZE + i;
            if (LIKELY(match != 0b1111111111111111))
                return self->num_groups;
            gi = (gi + 1) % self->num_groups;
        }
    }
    return self->num_groups;
}

static inline bool
_JOIN(A, find_bool)(A* self, TK key)
{
  return JOIN(A, find_index)(self, key) < self->num_groups;
}

static inline I
JOIN(A, find)(A* self, TK key)
{
    size_t index = JOIN(A, find_index)(self, key);
    if (index < self->num_groups)
        return JOIN(I, iter_index)(self, index);
    else
        return JOIN(A, end)(self);
}

// only power2 growth policy
static inline void
JOIN(A, _pre_insert_grow)(A* self)
{
    if (self->size >= HMAP_LOAD_FACTOR * self->num_groups * HMAP_CONTROL_SIZE)
        JOIN(A, _rehash)(self, HMAP_EXPAND_FACTOR * self->num_groups);
}

static inline void
JOIN(A, insert)(A* self, TK key, T value)
{
    t_hmap_hash hash;
    size_t gi;
    hash.s = self->hash(&key);
    gi = hash.h.position % self->num_groups;
    while (1)
    {
        int i = -1;
        B g = self->groups[gi];
#ifdef __SSE2__
        int match = _mm_movemask_epi8(
            _mm_cmpeq_epi8(_mm_set1_epi8(hash.h.meta), g.control));
#else
        int match = JOIN(B, _get_match_mask)(hash.h.meta, g.control);
#endif
        while (++i < HMAP_CONTROL_SIZE)
            if (match & (1 << i))
            {
                // FIXME collisions? need to equal
                ((char *)&self->groups[gi].control)[i] = (char)hash.h.meta;
                self->groups[gi].key[i] = key;
                self->values[gi * HMAP_CONTROL_SIZE + i] = value;
                ++self->size;
                JOIN(A, _pre_insert_grow)(self);
                return;
            }
        gi = (gi + 1) % self->num_groups;
    }
}

static inline I
JOIN(A, insert_found)(A* self, TK key, T value, int* foundp)
{
    t_hmap_hash hash;
    size_t gi;
    hash.s = self->hash(&key);
    gi = hash.h.position % self->num_groups;
    while (1)
    {
        int i = -1;
        B g = self->groups[gi];
#ifdef __SSE2__
        int match = _mm_movemask_epi8(
            _mm_cmpeq_epi8(_mm_set1_epi8(hash.h.meta), g.control));
#else
        int match = JOIN(B, _get_match_mask)(hash.h.meta, g.control);
#endif
        while (++i < HMAP_CONTROL_SIZE)
            if (match & (1 << i))
            {
                // FIXME collisions?
                if (LIKELY(self->equal(&g.key[i], &key)))
                    *foundp = 1;
                ((char *)&self->groups[gi].control)[i] = (char)hash.h.meta;
                self->groups[gi].key[i] = key;
                self->values[gi * HMAP_CONTROL_SIZE + i] = value;
                ++self->size;
                JOIN(A, _pre_insert_grow)(self);
                return JOIN(I, iter)(self, &self->values[gi * HMAP_CONTROL_SIZE + i]);
            }
        gi = (gi + 1) % self->num_groups;
    }
}

/*
static inline I
JOIN(A, emplace)(A* self, T* value)
{
    size_t index = JOIN(A, find_index)(self, *value);
    if ((index < self->num_groups)
    {
        FREE_VALUE(self, *value);
        return JOIN(I, iter_index)(self, index);
    }

    JOIN(A, _pre_insert_grow)(self);
    node = *JOIN(A, push_cached)(self, value); //??
    return JOIN(I, iter)(self, node);
}

static inline I
JOIN(A, emplace_found)(A* self, T* value, int* foundp)
{
    size_t index = JOIN(A, find_index)(self, *value);
    if ((index < self->num_groups)
    {
        *foundp = 1;
        FREE_VALUE(self, *value);
        return JOIN(I, iter_index)(self, index);
    }

    JOIN(A, _pre_insert_grow)(self);
    *foundp = 0;
    node = *JOIN(A, push_cached)(self, value); //??
    return JOIN(I, iter)(self, node);
}

static inline I
JOIN(A, emplace_hint)(I* pos, T* value)
{
    A* self = pos->container;
    if (!JOIN(I, done)(pos))
    {
#ifdef CTL_USET_CACHED_HASH
        size_t hash = self->hash(value);
        B** groups = JOIN(A, _bucket_hash)(self, hash);
#else
        B** groups = JOIN(A, _bucket)(self, *value);
#endif
        for(B* n = *groups; n; n = n->next)
        {
#ifdef CTL_USET_CACHED_HASH
            if(n->cached_hash != hash)
                continue;
#endif
            if(self->equal(value, &n->value))
            {
                FREE_VALUE(self, *value);
                // TODO move-to-front
                return JOIN(I, iter)(self, n);
            }
        }
        // not found
        B* node = JOIN(B, init)(*value);
        FREE_VALUE(self, *value);
        JOIN(B, push)(groups, node);
        pos->container->size++;
        pos->node = node;
        JOIN(I, update)(pos);
        pos->groups = groups;
        return *pos;
    }
    else
    {
        JOIN(A, _pre_insert_grow)(self);
        B* node = *JOIN(A, push_cached)(self, value);
        return JOIN(I, iter)(self, node);
    }
}
*/

static inline void
JOIN(A, clear)(A* self)
{
    size_t gi = self->num_groups;
    while (gi--)
#ifdef __SSE2__
        self->groups[gi].control = _mm_set1_epi8((char)HMAP_EMPTY);
#else
    {
        i = HMAP_CONTROL_SIZE;
        while (i--)
            self->groups[gi].control[i] = HMAP_EMPTY;
    }
#endif
    if (self->free)
    {
        gi = self->size;
        while (gi--)
            self->free(&self->values[gi]);
    }
    self->size = 0;
}

static inline void
JOIN(A, free)(A* self)
{
    //LOG("free calloc %zu, %zu\n", self->num_groups, self->size);
    JOIN(A, clear)(self);
    free(self->groups);
    self->groups = NULL;
    self->num_groups = 0;
}

static inline size_t
JOIN(A, count)(A* self, TK key)
{
    if (_JOIN(A, find_bool)(self, key))
        return 1UL;
    else
        return 0UL;
}

// C++20
static inline bool
JOIN(A, contains)(A* self, TK key)
{
    if (_JOIN(A, find_bool)(self, key))
        return true;
    else
        return false;
}

/* FIXME priority
static inline void
JOIN(A, erase)(A* self, TK key)
{
    B** groups = JOIN(A, _bucket)(self, value);
    B* prev = NULL;
    B* n = *groups;
    while (n)
    {
        B* next = n->next;
        if(self->equal(&key, &n->value))
        {
            JOIN(A, _linked_erase)(self, groups, n, prev, next);
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
    for(size_t i = 0; i < self->num_groups; i++)
    {
        B** groups = &self->groups[i];
        B* prev = NULL;
        B* n = *groups;
        while(n)
        {
            B* next = n->next;
            if(_match(&n->value))
            {
                JOIN(A, _linked_erase)(self, groups, n, prev, next);
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
    A other = JOIN(A, init)(self->hash, self->equal);
    JOIN(A, _reserve)(&other, self->num_groups);
    foreach(A, self, it) {
        // FIXME key and value
        JOIN(A, insert)(&other, self->copy(it.ref));
    }
    return other;
}

static inline A
JOIN(A, union)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    JOIN(A, _reserve)(&self, MAX(a->num_groups, b->num_groups));
    foreach(A, a, it1)
        JOIN(A, insert)(&self, self.copy(it1.ref));
    foreach(A, b, it2)
        JOIN(A, insert)(&self, self.copy(it2.ref));
    return self;
}

static inline A
JOIN(A, intersection)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    foreach(A, a, it)
        if (_JOIN(A, find_bool)(b, *it.ref))
            JOIN(A, insert)(&self, self.copy(it.ref));
    return self;
}

static inline A
JOIN(A, difference)(A* a, A* b)
{
    A self = JOIN(A, init)(a->hash, a->equal);
    foreach(A, a, it)
        if (!_JOIN(A, find_bool)(b, *it.ref))
            JOIN(A, insert)(&self, self.copy(it.ref));
    A self = JOIN(A, copy)(a);
    foreach(A, b, it)
        JOIN(A, erase)(&self, *it.ref);
    return self;
}

static inline A
JOIN(A, symmetric_difference)(A* a, A* b)
{
    A self = JOIN(A, union)(a, b);
    foreach(A, a, it)
        if (_JOIN(A, find_bool)(b, *it.ref))
            JOIN(A, erase)(&self, *it.ref);
    return self;
}

// different to the shared equal
static inline int
JOIN(A, equal)(A* self, A* other)
{
    size_t count_a = 0;
    size_t count_b = 0;
    // TODO: check equality of key AND value!
    foreach(A, self, it)
        if(_JOIN(A, find_bool)(self, *it.ref))
            count_a += 1;
    foreach(A, other, it2)
        if(_JOIN(A, find_bool)(other, *it2.ref))
            count_b += 1;
    return count_a == count_b;
}
*/

static inline void
JOIN(A, swap)(A* self, A* other)
{
    A temp = *self;
    *self = *other;
    *other = temp;
}

static inline bool
JOIN(A, inserter)(A* self, TK key, T value)
{
    if(_JOIN(A, find_bool)(self, key))
    {
        // already exists: keep
        if (self->free)
            self->free(&value);
        return false;
    }
    else
    {
        //JOIN(A, erase)(self, key);
        JOIN(A, insert)(self, key, value);
        return true;
    }
}

/*
// specialize, using our inserter (i.e. replace if different)
// This one changes in place.
static inline void
JOIN(A, generate)(A* self, JOIN(B, pair)* _gen(void))
{
    size_t size = self->size;
    JOIN(A, clear)(self);
    for (size_t i = 0; i < size; i++)
    {
        JOIN(B, pair) pair = _gen();
        JOIN(A, inserter)(self, pair.first, &pair.second);
    }
}

// These just insert in-place.
// The STL can be considered broken here, as it relies on the random iteration
// order to keep the rest. We shrink to n.
static inline void
JOIN(A, generate_n)(A* self, size_t n, T _gen(void))
{
    JOIN(A, clear)(self);
    for (size_t i = 0; i < n; i++)
    {
        //TK tmp = _gen();
        JOIN(A, insert)(self, tmp, 0);
    }
}

// non-destructive, returns a copy
static inline A
JOIN(A, transform)(A* self, T _unop(T*))
{
    A other = JOIN(A, init_from)(self);
    foreach(A, self, it)
    {
        T copy = self->copy(it.ref);
        T tmp = _unop(&copy);
        JOIN(A, insert)(&other, tmp);
        if (self->free)
            self->free(&copy);
    }
    return other;
}
*/

#undef POD
#undef PODK
#ifndef HOLD
#undef A
#undef B
#undef GI
#undef I
#undef T
#undef TK
#else
#undef HOLD
#endif
#undef CTL_UMAP

#undef HMAP_CONTROL_SIZE
#undef HMAP_GROUP_SIZE
#undef HMAP_VALUE_SIZE
#undef HMAP_LOAD_FACTOR
#undef HMAP_EXPAND_FACTOR
#undef HMAP_I128
#undef HMAP_I128_0XFF
#undef HMAP_I128_DELETED
#undef HMAP_I128_EMPTY

#ifdef USE_INTERNAL_VERIFY
#undef USE_INTERNAL_VERIFY
#endif
