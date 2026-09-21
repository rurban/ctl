/* Packed boolean vector. SPDX-License-Identifier: MIT */
#ifndef CTL_BVECTOR_H
#define CTL_BVECTOR_H
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
typedef struct bvec { uint64_t *words; size_t size, capacity; } bvec;
static inline bvec bvec_init(void) { return (bvec){0}; }
static inline int bvec_empty(const bvec *self) { return self->size == 0; }
static inline size_t bvec_size(const bvec *self) { return self->size; }
static inline size_t bvec_capacity(const bvec *self) { return self->capacity; }
static inline bool bvec_at(const bvec *self, size_t index) { assert(index < self->size); return (self->words[index >> 6] >> (index & 63)) & 1u; }
static inline void bvec_reserve(bvec *self, size_t capacity) { if (capacity > self->capacity) { size_t words = (capacity + 63) >> 6; uint64_t *p = (uint64_t *)realloc(self->words, words * sizeof(*p)); assert(p); for (size_t i = (self->capacity + 63) >> 6; i < words; i++) p[i] = 0; self->words = p; self->capacity = words << 6; } }
static inline void bvec_set(bvec *self, size_t index, bool value) { assert(index < self->size); uint64_t bit = UINT64_C(1) << (index & 63); if (value) self->words[index >> 6] |= bit; else self->words[index >> 6] &= ~bit; }
static inline void bvec_push_back(bvec *self, bool value) { if (self->size == self->capacity) bvec_reserve(self, self->capacity ? self->capacity * 2 : 64); size_t index = self->size++; if (value) self->words[index >> 6] |= UINT64_C(1) << (index & 63); else self->words[index >> 6] &= ~(UINT64_C(1) << (index & 63)); }
static inline void bvec_pop_back(bvec *self) { assert(self->size); self->size--; self->words[self->size >> 6] &= ~(UINT64_C(1) << (self->size & 63)); }
static inline void bvec_clear(bvec *self) { self->size = 0; }
static inline void bvec_free(bvec *self) { free(self->words); *self = bvec_init(); }
#endif
