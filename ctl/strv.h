/* strv: a non-owning view over a contiguous run of char, like std::string_view.
   SPDX-License-Identifier: MIT */
#ifndef CTL_STRV_H
#define CTL_STRV_H

#include <assert.h>
#include <stddef.h>
#include <string.h>

#define STRV_NPOS ((size_t)-1)

typedef struct strv
{
    const char *data;
    size_t size;
} strv;

static inline strv strv_init(const char *c_str)
{
    strv self;
    self.data = c_str;
    self.size = c_str ? strlen(c_str) : 0;
    return self;
}

static inline strv strv_init_n(const char *data, size_t size)
{
    strv self;
    self.data = data;
    self.size = size;
    return self;
}

static inline int strv_empty(strv *self)
{
    return self->size == 0;
}

static inline size_t strv_size(strv *self)
{
    return self->size;
}

static inline const char *strv_data(strv *self)
{
    return self->data;
}

static inline char strv_at(strv *self, size_t index)
{
    assert(index < self->size);
    return self->data[index];
}

static inline char strv_front(strv *self)
{
    return strv_at(self, 0);
}

static inline char strv_back(strv *self)
{
    assert(self->size);
    return self->data[self->size - 1];
}

static inline const char *strv_begin(strv *self)
{
    return self->data;
}

static inline const char *strv_end(strv *self)
{
    return self->data + self->size;
}

// [offset, offset + count). count == STRV_NPOS means "to the end".
static inline strv strv_substr(strv *self, size_t offset, size_t count)
{
    assert(offset <= self->size);
    size_t remaining = self->size - offset;
    if (count > remaining)
        count = remaining;
    return strv_init_n(self->data + offset, count);
}

static inline int strv_compare(strv *self, strv *other)
{
    size_t min = self->size < other->size ? self->size : other->size;
    int c = min ? memcmp(self->data, other->data, min) : 0;
    if (c)
        return c;
    if (self->size < other->size)
        return -1;
    if (self->size > other->size)
        return 1;
    return 0;
}

static inline int strv_equal(strv *self, strv *other)
{
    return self->size == other->size && (self->size == 0 || memcmp(self->data, other->data, self->size) == 0);
}

// first index of needle in self, or STRV_NPOS.
static inline size_t strv_find(strv *self, strv *needle)
{
    if (needle->size == 0)
        return 0;
    if (needle->size > self->size)
        return STRV_NPOS;
    for (size_t i = 0; i + needle->size <= self->size; i++)
        if (memcmp(self->data + i, needle->data, needle->size) == 0)
            return i;
    return STRV_NPOS;
}

static inline int strv_starts_with(strv *self, strv *prefix)
{
    return prefix->size <= self->size && (prefix->size == 0 || memcmp(self->data, prefix->data, prefix->size) == 0);
}

static inline int strv_ends_with(strv *self, strv *suffix)
{
    return suffix->size <= self->size &&
           (suffix->size == 0 || memcmp(self->data + (self->size - suffix->size), suffix->data, suffix->size) == 0);
}

#endif
