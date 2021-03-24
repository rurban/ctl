#ifndef __CHARPINT__H__
#define __CHARPINT__H__

// analog to strint.hh

#include <stdlib.h>
#include <ctype.h>

#ifdef __cplusplus
#include <string>
typedef std::pair<char*,int> CHARPINT;
#endif

typedef struct
{
    char* key;
    int value;
} charpint;

static inline charpint
charpint_init(char* key, int value)
{
    charpint self = { key, value };
    return self;
}

static inline void
charpint_free(charpint* self)
{
    free(self->key);
}

static inline int
charpint_compare(charpint* a, charpint* b)
{
    return strcmp (a->key, b->key);
}

static inline int
charpint_equal(charpint* a, charpint* b)
{
    return strcmp (a->key, b->key) == 0;
}

static size_t FNV1a(const char *key)
{
    size_t h;
    h = 2166136261u;
    for (unsigned i = 0; i < strlen(key); i++)
    {
        h ^= (unsigned char)key[i];
        h *= 16777619;
    }
    return h;
}

static inline size_t
charpint_hash(charpint* a)
{
    const char* key = a->key;
    return key && *key ? (size_t)FNV1a(key) : 0UL;
}

static inline size_t
charp_hash(char** key)
{
    return key && *key ? (size_t)FNV1a(*key) : 0UL;
}

static inline int
charp_equal(char** a, char** b)
{
    return (a && b)
        ? strcmp (*a, *b) == 0
        : a == b;
}

static inline void
charp_free(char** s)
{
    free(*s);
}

static inline char*
charp_copy(char** s)
{
    char *copy = (char *)malloc(strlen(*s) + 1);
    strcpy(copy, *s);
    return copy;
}

static inline charpint
charpint_copy(charpint* self)
{
    return charpint_init(charp_copy(&self->key), self->value);
}

#endif
