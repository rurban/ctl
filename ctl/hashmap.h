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

#include <ctl/bits/stanford_hash.h>
#include <ctl/bits/wyhash.h>
#include <ctl/ctl.h>
#include <stdbool.h>
#include <string.h>

#define CTL_HMAP
#define C JOIN(hmap, TK)
#define A JOIN(C, T)
#define E JOIN(A, entry)
typedef struct E
{
    TK key;
    T value;
    bool used;
} E;
typedef struct A
{
    E *entries;
    size_t size, capacity;
    size_t (*hash)(TK *);
    int (*equal)(TK *, TK *);
} A;

static inline size_t JOIN(A, _slot)(A *self, TK *key) { return self->hash(key) & (self->capacity - 1); }
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
            size_t slot = JOIN(A, _slot)(self, &old[i].key);
            while (self->entries[slot].used)
                slot = (slot + 1) & (capacity - 1);
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
    JOIN(A, _resize)(&self, 8);
    return self;
}

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
    size_t slot = JOIN(A, _slot)(self, &key);
    for (size_t probes = 0; probes < self->capacity; probes++)
    {
        E *entry = &self->entries[slot];
        if (!entry->used)
            return NULL;
        if (self->equal(&entry->key, &key))
            return &entry->value;
        slot = (slot + 1) & (self->capacity - 1);
    }
    return NULL;
}
static inline int JOIN(A, contains)(A *self, TK key) { return JOIN(A, find)(self, key) != NULL; }
static inline bool JOIN(A, insert)(A *self, TK key, T value)
{
    ASSERT(self->hash && self->equal);
    if ((self->size + 1) * 4 >= self->capacity * 3 && !JOIN(A, _resize)(self, self->capacity * 2))
        return false;
    size_t slot = JOIN(A, _slot)(self, &key);
    while (self->entries[slot].used)
    {
        if (self->equal(&self->entries[slot].key, &key))
        {
            self->entries[slot].key = key;
            self->entries[slot].value = value;
            return false;
        }
        slot = (slot + 1) & (self->capacity - 1);
    }
    self->entries[slot] = (E){key, value, true};
    self->size++;
    return true;
}
static inline bool JOIN(A, erase)(A *self, TK key)
{
    if (!self->size)
        return false;
    size_t slot = JOIN(A, _slot)(self, &key);
    for (size_t probes = 0; probes < self->capacity; probes++)
    {
        E *entry = &self->entries[slot];
        if (!entry->used)
            return false;
        if (self->equal(&entry->key, &key))
        {
            entry->used = false;
            self->size--;
            return JOIN(A, _resize)(self, self->capacity);
        }
        slot = (slot + 1) & (self->capacity - 1);
    }
    return false;
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
#undef TK
#undef T
#undef POD
