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
#define C JOIN(swiss, TK)
#define A JOIN(C, T)
#define E JOIN(A, entry)
typedef struct E { TK key; T value; bool used; } E;
typedef struct A { E *entries; size_t size, capacity; size_t (*hash)(TK *); int (*equal)(TK *, TK *); } A;

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
    A self = {0}; self.hash = hash; self.equal = equal; JOIN(A, _resize)(&self, 8); return self;
}
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
static inline bool JOIN(A, insert)(A *self, TK key, T value)
{
    ASSERT(self->hash && self->equal);
    if ((self->size + 1) * 4 >= self->capacity * 3 && !JOIN(A, _resize)(self, self->capacity * 2)) return false;
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
static inline void JOIN(A, free)(A *self) { free(self->entries); *self = (A){0}; }
#undef C
#undef A
#undef E
#undef TK
#undef T
#undef POD
