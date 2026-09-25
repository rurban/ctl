/* hashmap: open-addressing hashmap that auto-selects its hash/equal
   policy from the key type TK. Same probing/growth design as
   <ctl/swisstable.h>, just with a smart no-argument `_init()`:

   - string keys (a single-token char* alias, e.g. `typedef char *charp;
     #define TK charp`) default to wyhash (see <ctl/bits/wyhash.h>) and
     strcmp, matching swisstable's documented string-key policy.
   - every other (integral/POD-scalar) key defaults to the "stanford
     hash" avalanche mix (see <ctl/bits/stanford_hash.h>).

   Override the auto-detected policy explicitly by defining
   CTL_HMAP_STRING_KEY or CTL_HMAP_INTEGRAL_KEY before the include, or
   bypass detection with `_init_with(hash, equal)`. Non-POD or struct
   keys need an explicit hash/equal pair via `_init_with`, same as
   <ctl/swisstable.h>.

   Tunable policies: same growth, cached-hash and DDOS security knobs
   as <ctl/unordered_set.h> (see there for the full writeup), reusing
   the identical CTL_USET_* macro names so one `#define` before any
   hash-container include configures all of them for the translation
   unit:

     - CTL_USET_GROWTH_PRIMED / CTL_USET_GROWTH_POWER2 (default PRIMED)
       and CTL_USET_GROWTH_FACTOR, same meaning as unordered_set.h,
       applied to `capacity` instead of `bucket_count`.
     - CTL_USET_CACHED_HASH stores the hash next to each entry, to
       short-circuit `equal()` on probe misses.
     - CTL_USET_SECURITY_COLLCOUNTING against DDOS-crafted probe runs:
       0 ignore, 2 sleep (default), 3 abort. Modes 1/4/5 (sorted
       vector / tree fallback) are chained-hashtable-only concepts
       (unordered_set/unordered_map); selecting them here is a
       compile error.

   SPDX-License-Identifier: MIT */
#ifndef TK
#error "Key type TK undefined for <ctl/hashmap.h>"
#endif
#ifndef T
#error "Value type T undefined for <ctl/hashmap.h>"
#endif
#ifndef POD
#error "<ctl/hashmap.h> currently requires POD key and value types"
#endif

#ifdef CTL_USET_GROWTH_PRIMED // the default
#undef CTL_USET_GROWTH_POWER2
#endif
#ifdef CTL_USET_GROWTH_POWER2
#undef CTL_USET_GROWTH_PRIMED
#endif
#ifndef CTL_USET_GROWTH_FACTOR
#ifdef CTL_USET_GROWTH_POWER2
#define CTL_USET_GROWTH_FACTOR 2
#else
#define CTL_USET_GROWTH_FACTOR 1.618
#endif
#endif
#ifndef CTL_USET_SECURITY_COLLCOUNTING // defaults to sleep
#define CTL_USET_SECURITY_COLLCOUNTING 2
#endif
#if CTL_USET_SECURITY_COLLCOUNTING == 1 || CTL_USET_SECURITY_COLLCOUNTING == 4 || CTL_USET_SECURITY_COLLCOUNTING == 5
#error "CTL_USET_SECURITY_COLLCOUNTING 1/4/5 (sorted vector / tree fallback) apply only to the chained <ctl/unordered_set.h>; <ctl/hashmap.h> is open-addressing and supports 0 (ignore), 2 (sleep) and 3 (abort)."
#endif

#if CTL_USET_SECURITY_COLLCOUNTING == 2 // sleep
#ifndef _WIN32
#include <unistd.h>
#ifndef CTL_USET_SECURITY_ACTION
#define CTL_USET_SECURITY_ACTION sleep(1)
#endif
#else
#define WIN32_LEAN_AND_MEAN
#define VC_EXTRALEAN
#include <windows.h>
#ifndef CTL_USET_SECURITY_ACTION
#define CTL_USET_SECURITY_ACTION Sleep(500)
#endif
#endif
#elif CTL_USET_SECURITY_COLLCOUNTING == 3 // abort
#include <stdlib.h>
#ifndef CTL_USET_SECURITY_ACTION
#define CTL_USET_SECURITY_ACTION abort()
#endif
#endif

#include <ctl/bits/prime.h>
#include <ctl/bits/stanford_hash.h>
#include <ctl/bits/wyhash.h>
#include <ctl/ctl.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#define CTL_HMAP
#define C JOIN(hmap, TK)
#define A JOIN(C, T)
#define E JOIN(A, entry)
#define I JOIN(A, it)
typedef struct E
{
    TK key;
    T value;
    bool used;
#ifdef CTL_USET_CACHED_HASH
    size_t cached_hash;
#endif
} E;
typedef struct A
{
    E *entries;
    size_t size, capacity;
    float max_load_factor;
    size_t (*hash)(TK *);
    int (*equal)(TK *, TK *);
} A;
typedef struct I
{
    A *container;
    E *entry;
} I;

// bucket index of an already computed hash, per growth policy
static inline size_t JOIN(A, _slot_hash)(A *self, size_t hash)
{
#ifdef CTL_USET_GROWTH_POWER2
    return hash & (self->capacity - 1);
#else
    return hash % self->capacity;
#endif
}
static inline size_t JOIN(A, _slot)(A *self, TK *key) { return JOIN(A, _slot_hash)(self, self->hash(key)); }
// next probe position, per growth policy
static inline size_t JOIN(A, _probe)(A *self, size_t slot)
{
#ifdef CTL_USET_GROWTH_POWER2
    return (slot + 1) & (self->capacity - 1);
#else
    return (slot + 1) % self->capacity;
#endif
}
// smallest valid (power2 or primed) capacity able to hold `want`
static inline size_t JOIN(A, _valid_capacity)(size_t want)
{
#ifdef CTL_USET_GROWTH_POWER2
    return ctl_next_power2((uint32_t)(want < 8 ? 8 : want));
#else
    return ctl_next_prime(want < 8 ? 8 : want);
#endif
}
static inline bool JOIN(A, _resize)(A *self, size_t capacity)
{
    E *entries = calloc(capacity, sizeof(*entries));
    if (!entries)
        return false;
    E *old = self->entries;
    size_t old_capacity = self->capacity;
    self->entries = entries;
    self->capacity = capacity;
    size_t size = self->size;
    self->size = 0;
    for (size_t i = 0; i < old_capacity; i++)
        if (old[i].used)
        {
#ifdef CTL_USET_CACHED_HASH
            size_t slot = JOIN(A, _slot_hash)(self, old[i].cached_hash);
#else
            size_t slot = JOIN(A, _slot)(self, &old[i].key);
#endif
            while (self->entries[slot].used)
                slot = JOIN(A, _probe)(self, slot);
            self->entries[slot] = old[i];
            self->size++;
        }
    free(old);
    return self->size == size;
}
static inline A JOIN(A, init_with)(size_t (*hash)(TK *), int (*equal)(TK *, TK *))
{
    A self = {0};
    self.hash = hash;
    self.equal = equal;
    self.max_load_factor = 0.75f;
    JOIN(A, _resize)(&self, 8);
    return self;
}
static inline bool JOIN(A, empty)(A *self) { return self->size == 0; }
static inline size_t JOIN(A, max_size)(void) { return 4294967296 / sizeof(E); }
static inline float JOIN(A, load_factor)(A *self) { return self->capacity ? (float)self->size / (float)self->capacity : 0.0f; }
static inline void JOIN(A, max_load_factor)(A *self, float factor) { self->max_load_factor = factor; }
static inline E *JOIN(A, _first_used)(A *self, E *from)
{
    E *end = &self->entries[self->capacity];
    while (from < end && !from->used)
        from++;
    return from;
}
static inline I JOIN(A, begin)(A *self)
{
    I it;
    it.container = self;
    it.entry = JOIN(A, _first_used)(self, self->entries);
    return it;
}
static inline I JOIN(A, end)(A *self)
{
    I it;
    it.container = self;
    it.entry = &self->entries[self->capacity];
    return it;
}
static inline int JOIN(I, done)(I *it) { return it->entry == &it->container->entries[it->container->capacity]; }
static inline void JOIN(I, next)(I *it) { it->entry = JOIN(A, _first_used)(it->container, it->entry + 1); }
static inline TK *JOIN(I, key)(I *it) { return &it->entry->key; }
static inline T *JOIN(I, ref)(I *it) { return &it->entry->value; }

// Default for integral/POD-scalar keys: the stanford-hash avalanche mix.
static inline size_t JOIN(A, _stanford_hash)(TK *key) { return stanford_hash((size_t)*key); }
static inline int JOIN(A, _scalar_equal)(TK *a, TK *b) { return *a == *b; }
// Default for string keys: wyhash + strcmp.
static inline size_t JOIN(A, _wystring_hash)(TK *key) { const char *s = (const char *)(size_t)*key; return (size_t)wyhash(s, strlen(s), 0, _wyp); }
static inline int JOIN(A, _string_equal)(TK *a, TK *b) { return strcmp((const char *)(size_t)*a, (const char *)(size_t)*b) == 0; }

static inline bool JOIN(A, _key_is_string)(void)
{
#if defined CTL_HMAP_STRING_KEY
    return true;
#elif defined CTL_HMAP_INTEGRAL_KEY
    return false;
#else
#define _HMAP_STRINGIFY_HELPER(x) #x
#define _HMAP_STRINGIFY(x) _HMAP_STRINGIFY_HELPER(x)
#define _HMAP_STREQ(a, b) (!strcmp((a), (b)))
    const char *name = _HMAP_STRINGIFY(TK);
    return _HMAP_STREQ(name, "charp") || _HMAP_STREQ(name, "ucharp") || _HMAP_STREQ(name, "cstr") ||
           _HMAP_STREQ(name, "str") || _HMAP_STREQ(name, "string") || _HMAP_STREQ(name, "cstring") ||
           _HMAP_STREQ(name, "u8ident") || _HMAP_STREQ(name, "u8string");
#undef _HMAP_STRINGIFY_HELPER
#undef _HMAP_STRINGIFY
#undef _HMAP_STREQ
#endif
}
static inline A JOIN(A, init)(void)
{
    return JOIN(A, _key_is_string)() ? JOIN(A, init_with)(JOIN(A, _wystring_hash), JOIN(A, _string_equal))
                                      : JOIN(A, init_with)(JOIN(A, _stanford_hash), JOIN(A, _scalar_equal));
}

static inline T *JOIN(A, find)(A *self, TK key)
{
    if (!self->size)
        return NULL;
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&key);
    size_t slot = JOIN(A, _slot_hash)(self, hash);
#else
    size_t slot = JOIN(A, _slot)(self, &key);
#endif
#if CTL_USET_SECURITY_COLLCOUNTING
    unsigned int count = 0;
#endif
    for (size_t probes = 0; probes < self->capacity; probes++, slot = JOIN(A, _probe)(self, slot))
    {
        E *entry = &self->entries[slot];
        if (!entry->used)
            return NULL;
#ifdef CTL_USET_CACHED_HASH
        if (entry->cached_hash != hash)
            continue;
#endif
        if (self->equal(&entry->key, &key))
            return &entry->value;
#if CTL_USET_SECURITY_COLLCOUNTING
        // with max 2^32 keys, 128 collisions is safely considered a DDOS attack.
        if (++count & 128)
            CTL_USET_SECURITY_ACTION;
#endif
    }
    return NULL;
}
static inline int JOIN(A, contains)(A *self, TK key) { return JOIN(A, find)(self, key) != NULL; }
static inline size_t JOIN(A, count)(A *self, TK key) { return JOIN(A, contains)(self, key) ? 1 : 0; }
static inline void JOIN(A, equal_range)(A *self, TK key, I *lower, I *upper)
{
    T *val = JOIN(A, find)(self, key);
    lower->container = self;
    upper->container = self;
    if (val)
    {
        E *entry = (E *)((char *)val - offsetof(E, value));
        lower->entry = entry;
        upper->entry = JOIN(A, _first_used)(self, entry + 1);
    }
    else
    {
        lower->entry = &self->entries[self->capacity];
        upper->entry = lower->entry;
    }
}
static inline bool JOIN(A, insert)(A *self, TK key, T value)
{
    ASSERT(self->hash && self->equal);
    if ((float)(self->size + 1) >= (float)self->capacity * self->max_load_factor &&
        !JOIN(A, _resize)(self, JOIN(A, _valid_capacity)((size_t)((double)self->capacity * CTL_USET_GROWTH_FACTOR))))
        return false;
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&key);
    size_t slot = JOIN(A, _slot_hash)(self, hash);
#else
    size_t slot = JOIN(A, _slot)(self, &key);
#endif
#if CTL_USET_SECURITY_COLLCOUNTING
    unsigned int count = 0;
#endif
    while (self->entries[slot].used)
    {
#ifdef CTL_USET_CACHED_HASH
        if (self->entries[slot].cached_hash == hash && self->equal(&self->entries[slot].key, &key))
#else
        if (self->equal(&self->entries[slot].key, &key))
#endif
        {
            self->entries[slot].key = key;
            self->entries[slot].value = value;
            return false;
        }
#if CTL_USET_SECURITY_COLLCOUNTING
        if (++count & 128)
            CTL_USET_SECURITY_ACTION;
#endif
        slot = JOIN(A, _probe)(self, slot);
    }
#ifdef CTL_USET_CACHED_HASH
    self->entries[slot] = (E){key, value, true, hash};
#else
    self->entries[slot] = (E){key, value, true};
#endif
    self->size++;
    return true;
}
static inline bool JOIN(A, erase)(A *self, TK key)
{
    if (!self->size)
        return false;
#ifdef CTL_USET_CACHED_HASH
    size_t hash = self->hash(&key);
    size_t slot = JOIN(A, _slot_hash)(self, hash);
#else
    size_t slot = JOIN(A, _slot)(self, &key);
#endif
#if CTL_USET_SECURITY_COLLCOUNTING
    unsigned int count = 0;
#endif
    for (size_t probes = 0; probes < self->capacity; probes++, slot = JOIN(A, _probe)(self, slot))
    {
        E *entry = &self->entries[slot];
        if (!entry->used)
            return false;
#ifdef CTL_USET_CACHED_HASH
        if (entry->cached_hash != hash)
            continue;
#endif
        if (self->equal(&entry->key, &key))
        {
            entry->used = false;
            self->size--;
            return JOIN(A, _resize)(self, self->capacity);
        }
#if CTL_USET_SECURITY_COLLCOUNTING
        if (++count & 128)
            CTL_USET_SECURITY_ACTION;
#endif
    }
    return false;
}
static inline void JOIN(A, clear)(A *self)
{
    for (size_t i = 0; i < self->capacity; i++)
        self->entries[i].used = false;
    self->size = 0;
}
static inline size_t JOIN(A, _grown_capacity)(A *self, size_t min_count)
{
    size_t capacity = JOIN(A, _valid_capacity)(min_count);
    while ((float)self->size >= (float)capacity * self->max_load_factor)
        capacity = JOIN(A, _valid_capacity)(capacity + 1);
    return capacity;
}
static inline bool JOIN(A, rehash)(A *self, size_t bucket_count)
{
    size_t capacity = JOIN(A, _grown_capacity)(self, bucket_count);
    return capacity <= self->capacity ? true : JOIN(A, _resize)(self, capacity);
}
static inline bool JOIN(A, reserve)(A *self, size_t count)
{
    size_t needed = 8;
    while ((float)needed * self->max_load_factor < (float)count)
        needed <<= 1;
    return JOIN(A, rehash)(self, needed);
}
static inline void JOIN(A, swap)(A *self, A *other) { SWAP(A, self, other); }
static inline A JOIN(A, copy)(A *self)
{
    A other = *self;
    other.entries = malloc(self->capacity * sizeof(E));
    if (other.entries)
        memcpy(other.entries, self->entries, self->capacity * sizeof(E));
    return other;
}
static inline void JOIN(A, assign)(A *self, A *other)
{
    free(self->entries);
    *self = JOIN(A, copy)(other);
}
static inline void JOIN(A, free)(A *self)
{
    free(self->entries);
    *self = (A){0};
}
#undef CTL_HMAP
#undef C
#undef A
#undef E
#undef I
#undef TK
#undef T
#undef POD
