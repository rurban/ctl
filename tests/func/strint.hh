#ifndef __STRINT__H__
#define __STRINT__H__

#include <../../ctl/string.h>
#include <stdlib.h>

// THESE STRINT STRUCTS BEHAVE IDENTICALLY AND ARE USED AS THE BASIS
// FOR TESTING COPY / FREE / CONSTRUCT FOR STL AND CTL CONTAINERS.

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
    str_free(self->key);
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
    return strcmp(*a->key, *b->key);
}

static inline size_t
strint_hash(strint* a)
{
    return (size_t)FNV1a(a->key);
}

static inline strint
strint_copy(strint* self)
{
    strint copy = strint_init(0);
    *copy.key = *self->key;
    *copy.value = self->value;
    return copy;
}

static inline int
strint_is_odd(strint* d)
{
    return *d->value % 2;
}

static inline int
strint_match(strint* a, strint* b)
{
    return *a->value == *b->value;
}

struct STRINT
{
    string key;
    int value;
    STRINT(string _key, int _value): value { new int {_value} }
    {
    }
    STRINT(char* _key, int _value)
        : key(_key)
    {
        value = new int (_value);
    }
    STRINT(): STRINT(NULL,0)
    {
    }
    ~STRINT()
    {
        delete value;
    }
    STRINT(const STRINT& a): STRINT()
    {
        *key = *a.key;
        *value = *a.value;
    }
    STRINT& operator=(const STRINT& a)
    {
        delete key;
        delete value;
        key = new int;
        value = new int;

        *key = *a.key;
        *value = *a.value;
        return *this;
    }
    STRINT& operator=(STRINT&& a)
    {
        delete key;
        delete value;
        key = new int;
        value = new int;

        *key = *a.key;
        *value = *a.value;
        a.key = nullptr;
        a.value = nullptr;
        return *this;
    }
    STRINT(STRINT&& a)
    {
        key = a.key;
        value = a.value;
        a.value = nullptr;
        a.key = nullptr;
    }
    bool operator<(const STRINT& a) const
    {
        return *key < *a.key;
    }
    bool operator==(const STRINT& a) const
    {
        return *key == *a.key;
    }
    size_t hash(const STRINT& a) const
    {
        return strint_hash (*a);
    }
};

class STRINT_hash {
public:
    std::size_t operator()(const STRINT& a) const
    {
        return strint_hash(a.key.c_str());
    }
};

static inline bool
STRINT_is_odd(STRINT& d)
{
    return *d.value % 2;
}

#endif
