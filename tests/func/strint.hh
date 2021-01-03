#ifndef __STRINT__H__
#define __STRINT__H__

#include "ctl/string.h"
#include <stdlib.h>
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

static size_t
FNV1a(const char *key)
{
  size_t h;
  h = 2166136261u;
  for (unsigned i = 0; i < strlen(key); i++) {
    h ^= (unsigned char)key[i];
    h *= 16777619;
  }
  return h;
}

static inline int
strint_compare(strint* a, strint* b)
{
    return str_key_compare (&a->key, &b->key);
}

static inline size_t
strint_hash(strint* a)
{
    return (size_t)FNV1a(str_c_str(&a->key));
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
strint_is_odd(strint* d)
{
    return d->value % 2;
}

static inline int
strint_match(strint* a, strint* b)
{
    return str_key_compare (&a->key, &b->key) == 0;
}

#endif
