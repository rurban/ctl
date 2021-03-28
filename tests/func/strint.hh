#ifndef __STRINT__H__
#define __STRINT__H__

#include "ctl/string.h"
#include <stdlib.h>
#include <ctype.h>

#include <string>

// THESE STRINT STRUCTS BEHAVE IDENTICALLY AND ARE USED AS THE BASIS
// FOR TESTING COPY / FREE / CONSTRUCT FOR STL AND CTL CONTAINERS.

typedef std::pair<std::string,int> STRINT;

typedef struct
{
    str key;
    int value;
} strint;

static inline strint
strint_init(str key, int value)
{
    strint self = { key, value };
    return self;
}

static inline void
strint_free(strint* self)
{
    str_free(&self->key);
}

static inline int
strint_compare(strint* a, strint* b)
{
    return str_key_compare (&a->key, &b->key);
}

static inline size_t
strint_hash(strint* a)
{
    const char* key = a->key.vector;
    return key && *key ? ctl_string_hash(key) : 0UL;
}

static inline strint
strint_copy(strint* self)
{
    strint copy = strint_init(str_init(""), 0);
    copy.key = self->key;
    copy.value = self->value;
    return copy;
}

static inline int
strint_isupper(strint* d)
{
    return isupper(d->key.vector[0]);
}

static inline int
STRINT_isupper(STRINT d)
{
    return isupper(*d.first.c_str());
}

static inline int
char_isupper(char* k)
{
    return isupper(*k);
}

static inline int
strint_equal(strint* a, strint* b)
{
    return str_key_compare (&a->key, &b->key) == 0;
}

#endif
