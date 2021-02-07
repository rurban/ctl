#ifndef __DIGI__H__
#define __DIGI__H__

#include <stdlib.h>

// THESE DIGI STRUCTS BEHAVE IDENTICALLY AND ARE USED AS THE BASIS
// FOR TESTING COPY / FREE / CONSTRUCT FOR STL AND CTL CONTAINERS.

typedef struct
{
    int* value;
} digi;

static inline digi
digi_init(int value)
{
    digi self = {
        (int*) malloc(sizeof(*self.value))
    };
    *self.value = value;
    return self;
}

static inline void
digi_free(digi* self)
{
    free(self->value);
}

static inline int
digi_compare(digi* a, digi* b)
{
    return *a->value < *b->value;
}

static inline digi
digi_copy(digi* self)
{
    digi copy = digi_init(0);
    *copy.value = *self->value;
    return copy;
}

static inline int
digi_is_odd(digi* d)
{
    return *d->value % 2;
}

static inline int
digi_equal(digi* a, digi* b)
{
    return *a->value == *b->value;
}

static inline uint32_t
int_hash_func (uint32_t key)
{
  key = ((key >> 16) ^ key) * 0x45d9f3b;
  key = ((key >> 16) ^ key) * 0x45d9f3b;
  key = (key >> 16) ^ key;
  return key;
}

static inline size_t
digi_hash(digi* a)
{
    return (size_t)int_hash_func(*a->value);
}

struct DIGI
{
    int* value;
    DIGI(int _value): value { new int {_value} }
    {
    }
    DIGI(): DIGI(0)
    {
    }
    ~DIGI()
    {
        delete value;
    }
    DIGI(const DIGI& a): DIGI()
    {
        *value = a.value ? *a.value : 0;
    }
    DIGI& operator=(const DIGI& a)
    {
        delete value;
        value = new int;
        *value = *a.value;
        return *this;
    }
#if __cplusplus >= 201103L
    DIGI& operator=(DIGI&& a)
    {
        delete value;
        value = a.value;
        a.value = nullptr;
        return *this;
    }
    DIGI(DIGI&& a)
    {
        value = a.value;
        a.value = nullptr;
    }
#endif
    bool operator<(const DIGI& a) const
    {
        return *value < *a.value;
    }
    bool operator==(const DIGI& a) const
    {
        return *value == *a.value;
    }
    int operator*() const
    {
        return *value;
    }
    size_t hash(const DIGI& a) const
    {
        return (size_t)int_hash_func(*a.value);
    }
};

class DIGI_hash {
public:
    size_t operator()(const DIGI& a) const
    {
        return (size_t)int_hash_func(*a.value);
    }
};

static int _generator_state = 0;
static inline digi
digi_generate(void)
{
    return digi_init(++_generator_state);
}
static inline DIGI
DIGI_generate(void)
{
    return DIGI{++_generator_state};
}

static inline void
digi_generate_reset()
{
    _generator_state = 0;
}

static inline bool
DIGI_is_odd(DIGI& d)
{
    return *d.value % 2;
}

static inline bool
DIGIc_is_odd(const DIGI d)
{
    return *d.value % 2;
}

static inline digi
digi_untrans (digi* d)
{
    return digi_init(*d->value >> 1);
}
static inline DIGI
DIGI_untrans (const DIGI& d)
{
    return DIGI{*d.value >> 1};
}
static inline digi
digi_bintrans (digi* d1, digi* d2)
{
    return digi_init(*d1->value ^ *d2->value);
}
static inline DIGI
DIGI_bintrans (const DIGI& d1, const DIGI& d2)
{
    return DIGI{*d1.value ^ *d2.value};
}

#endif
