/* Open-addressing hashmap with Swiss-table-style probe groups.
   SPDX-License-Identifier: MIT */
#ifndef TK
#error "Key type TK undefined for <ctl/swisstable.h>"
#endif
#ifndef T
#error "Value type T undefined for <ctl/swisstable.h>"
#endif
#ifndef POD
#error "<ctl/swisstable.h> currently requires POD key and value types"
#endif

#include <ctl/ctl.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#define C JOIN(swiss, TK)
#define A JOIN(C, T)
#define E JOIN(A, entry)
#define I JOIN(A, it)
typedef struct E { TK key; T value; bool used; } E;
typedef struct A { E *entries; size_t size, capacity; float max_load_factor; size_t (*hash)(TK *); int (*equal)(TK *, TK *); } A;
typedef struct I { A *container; E *entry; } I;

static inline size_t JOIN(A, _slot)(A *self, TK *key) { return self->hash(key) & (self->capacity - 1); }
static inline bool JOIN(A, _resize)(A *self, size_t capacity)
{
    E *entries = calloc(capacity, sizeof(*entries));
    if (!entries) return false;
    E *old = self->entries; size_t old_capacity = self->capacity;
    self->entries = entries; self->capacity = capacity; size_t size = self->size; self->size = 0;
    for (size_t i = 0; i < old_capacity; i++) if (old[i].used) {
        size_t slot = JOIN(A, _slot)(self, &old[i].key);
        while (self->entries[slot].used) slot = (slot + 1) & (capacity - 1);
        self->entries[slot] = old[i]; self->size++;
    }
    free(old); return self->size == size;
}
static inline A JOIN(A, init)(size_t (*hash)(TK *), int (*equal)(TK *, TK *))
{
    A self = {0}; self.hash = hash; self.equal = equal; self.max_load_factor = 0.75f; JOIN(A, _resize)(&self, 8); return self;
}
static inline bool JOIN(A, empty)(A *self) { return self->size == 0; }
static inline size_t JOIN(A, max_size)(void) { return 4294967296 / sizeof(E); }
static inline float JOIN(A, load_factor)(A *self) { return self->capacity ? (float)self->size / (float)self->capacity : 0.0f; }
static inline void JOIN(A, max_load_factor)(A *self, float factor) { self->max_load_factor = factor; }
static inline E *JOIN(A, _first_used)(A *self, E *from)
{
    E *end = &self->entries[self->capacity];
    while (from < end && !from->used) from++;
    return from;
}
static inline I JOIN(A, begin)(A *self)
{
    I it; it.container = self; it.entry = JOIN(A, _first_used)(self, self->entries);
    return it;
}
static inline I JOIN(A, end)(A *self)
{
    I it; it.container = self; it.entry = &self->entries[self->capacity];
    return it;
}
static inline int JOIN(I, done)(I *it) { return it->entry == &it->container->entries[it->container->capacity]; }
static inline void JOIN(I, next)(I *it) { it->entry = JOIN(A, _first_used)(it->container, it->entry + 1); }
static inline TK *JOIN(I, key)(I *it) { return &it->entry->key; }
static inline T *JOIN(I, ref)(I *it) { return &it->entry->value; }
static inline T *JOIN(A, find)(A *self, TK key)
{
    if (!self->size) return NULL;
    size_t slot = JOIN(A, _slot)(self, &key);
    for (size_t probes = 0; probes < self->capacity; probes++) {
        E *entry = &self->entries[slot];
        if (!entry->used) return NULL;
        if (self->equal(&entry->key, &key)) return &entry->value;
        slot = (slot + 1) & (self->capacity - 1);
    }
    return NULL;
}
static inline int JOIN(A, contains)(A *self, TK key) { return JOIN(A, find)(self, key) != NULL; }
static inline size_t JOIN(A, count)(A *self, TK key) { return JOIN(A, contains)(self, key) ? 1 : 0; }
static inline void JOIN(A, equal_range)(A *self, TK key, I *lower, I *upper)
{
    T *val = JOIN(A, find)(self, key);
    lower->container = self; upper->container = self;
    if (val) {
        E *entry = (E *)((char *)val - offsetof(E, value));
        lower->entry = entry; upper->entry = JOIN(A, _first_used)(self, entry + 1);
    } else {
        lower->entry = &self->entries[self->capacity]; upper->entry = lower->entry;
    }
}
static inline bool JOIN(A, insert)(A *self, TK key, T value)
{
    ASSERT(self->hash && self->equal);
    if ((float)(self->size + 1) >= (float)self->capacity * self->max_load_factor && !JOIN(A, _resize)(self, self->capacity * 2)) return false;
    size_t slot = JOIN(A, _slot)(self, &key);
    while (self->entries[slot].used) {
        if (self->equal(&self->entries[slot].key, &key)) { self->entries[slot].key = key; self->entries[slot].value = value; return false; }
        slot = (slot + 1) & (self->capacity - 1);
    }
    self->entries[slot] = (E){key, value, true}; self->size++; return true;
}
static inline bool JOIN(A, erase)(A *self, TK key)
{
    if (!self->size) return false;
    size_t slot = JOIN(A, _slot)(self, &key);
    for (size_t probes = 0; probes < self->capacity; probes++) {
        E *entry = &self->entries[slot]; if (!entry->used) return false;
        if (self->equal(&entry->key, &key)) { entry->used = false; self->size--; return JOIN(A, _resize)(self, self->capacity); }
        slot = (slot + 1) & (self->capacity - 1);
    }
    return false;
}
static inline void JOIN(A, clear)(A *self)
{
    for (size_t i = 0; i < self->capacity; i++) self->entries[i].used = false;
    self->size = 0;
}
static inline bool JOIN(A, rehash)(A *self, size_t bucket_count)
{
    size_t capacity = 8;
    while (capacity < bucket_count) capacity <<= 1;
    while ((float)self->size >= (float)capacity * self->max_load_factor) capacity <<= 1;
    return capacity <= self->capacity ? true : JOIN(A, _resize)(self, capacity);
}
static inline bool JOIN(A, reserve)(A *self, size_t count)
{
    size_t needed = 8;
    while ((float)needed * self->max_load_factor < (float)count) needed <<= 1;
    return JOIN(A, rehash)(self, needed);
}
static inline void JOIN(A, swap)(A *self, A *other) { SWAP(A, self, other); }
static inline A JOIN(A, copy)(A *self)
{
    A other = *self;
    other.entries = malloc(self->capacity * sizeof(E));
    if (other.entries) memcpy(other.entries, self->entries, self->capacity * sizeof(E));
    return other;
}
static inline void JOIN(A, assign)(A *self, A *other)
{
    free(self->entries);
    *self = JOIN(A, copy)(other);
}
static inline void JOIN(A, free)(A *self) { free(self->entries); *self = (A){0}; }
#undef C
#undef A
#undef E
#undef I
#undef TK
#undef T
#undef POD
