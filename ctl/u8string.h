/* We don't even have <u8string> yet in the libstdc++!
   Do normalized NFD comparisons. Check validity.
   SPDX-License-Identifier: MIT */
#ifndef __CTL_U8STRING_H__
#define __CTL_U8STRING_H__

#ifdef T
# error "Template type T defined for <ctl/u8string.h>"
#endif

#ifndef __cpp_lib_char8_t
typedef unsigned char char8_t;
#endif

// check backends
#ifdef _LIBUNISTRING_VERSION
# include <uninorm.h>
#endif

#define POD
#undef A
#define T char8_t
#define A u8str
#define u8str_char8_t u8str
#define vec u8str

enum u8str_norm {
    NORM_NONE = 0,
    NFD,  /* fastest, not composed */
    NFC,  /* composed */
    NFKD, /* compat, for fc search only */
    NFKC, /* compat */
    FCD,  /* not reordered */
    FCC,  /* contiguous composition only */
};

typedef struct A
{
    T* vector;
    size_t size;
    size_t capacity;
    void (*free)(T*);
    T (*copy)(T*);
    int (*compare)(T*, T*);
    int (*equal)(T*, T*);
    struct str *normstr;
    unsigned valid:1;      /* is already validated */
    unsigned repair:1;     /* do repair */
    unsigned normalized:3; /* 6 normalize enums. NONE,NFD,NFC,...*/
    unsigned same_norm:1;  /* optimization normstr.vector == vector */
} A;

#define HOLD
#define u8str_init  u8str___INIT
#define u8str_equal u8str___EQUAL
#define u8str_find  u8str___FIND
//#define at __AT
#undef A
#include <ctl/vector.h>
#undef A
#define A u8str
#ifdef u8id_char8_t
#  define HOLD
#endif
#undef u8str_init
#undef u8str_equal
#undef u8str_find
//#undef at

#include <string.h>

// for simplicity start with a signed char*? or demand char8_t and u8"" literals?
static inline A
JOIN(A, init)(const T* c_str)
{
    A self = u8str___INIT();
    size_t len = strlen((char*)c_str);
    size_t min = 15;
    JOIN(A, reserve)(&self, len < min ? min : len);
    for(const T* s = c_str; *s; s++)
        JOIN(A, push_back)(&self, (T)*s);
    return self;
}

// Compare with append, and push_back to add a single char8_t
static inline void
u8str_str_push_back(A* self, A s)
{
    if(self->size == self->capacity)
        JOIN(A, reserve)(self, self->capacity == 0 ? s.size : (2 * self->capacity) + s.size);
    for(size_t i = 0; i < s.size; i++)
        self->vector[self->size + i] = s.vector[i];
    self->size += s.size;
}

static inline void
JOIN(A, append)(A* self, const T* s)
{
    size_t start = self->size;
    size_t len = strlen((char*)s);
    JOIN(A, resize)(self, self->size + len, '\0');
    for(size_t i = 0; i < len; i++)
        self->vector[start + i] = s[i];
}

static inline void
JOIN(A, insert_str)(A* self, size_t index, const T* s)
{
    size_t start = self->size;
    size_t len = strlen((char*)s);
    JOIN(A, resize)(self, self->size + len, '\0');
    self->size = start;
    while(len != 0)
    {
        len--;
        JOIN(A, insert)(self, index, s[len]);
    }
}

static inline void
JOIN(A, replace)(A* self, size_t index, size_t size, const T* s)
{
    size_t end = index + size;
    if(end >= self->size)
        end = self->size;
    for(size_t i = index; i < end; i++)
        JOIN(A, erase)(self, index);
    JOIN(A, insert_str)(self, index, s);
}

static inline T*
JOIN(A, c_str)(A* self)
{
    return JOIN(A, data)(self);
}

static inline size_t
JOIN(A, find)(A* self, const T* s)
{
    T* c_str = self->vector;
    char* found = strstr((char*)c_str, (char*)s);
    if(found)
        return found - (char*)c_str;
    return SIZE_MAX;
}

static inline int
JOIN(A, count)(A* self, T c)
{
    size_t count = 0;
    for(size_t i = 0; i < self->size; i++)
        if(self->vector[i] == c)
            count++;
    return count;
}

static inline size_t
JOIN(A, rfind)(A* self, const T* s)
{
    T* c_str = self->vector;
    for(size_t i = self->size; i != SIZE_MAX; i--)
    {
        char* found = strstr((char*)&c_str[i], (char*)s);
        if(found)
            return found - (char*)c_str;
    }
    return SIZE_MAX;
}

static inline size_t
JOIN(A, find_first_of)(A* self, const T* s)
{
    for(size_t i = 0; i < self->size; i++)
    for(const T* p = s; *p; p++)
        if(self->vector[i] == *p)
            return i;
    return SIZE_MAX;
}

static inline size_t
JOIN(A, find_last_of)(A* self, const T* s)
{
    for(size_t i = self->size; i != SIZE_MAX; i--)
    for(const T* p = s; *p; p++)
        if(self->vector[i] == *p)
            return i;
    return SIZE_MAX;
}

static inline size_t
JOIN(A, find_first_not_of)(A* self, const T* s)
{
    for(size_t i = 0; i < self->size; i++)
    {
        size_t count = 0;
        for(const T* p = s; *p; p++)
            if(self->vector[i] == *p)
                count++;
        if(count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline size_t
JOIN(A, find_last_not_of)(A* self, const T* s)
{
    for(size_t i = self->size - 1; i != SIZE_MAX; i--)
    {
        size_t count = 0;
        for(const T* p = s; *p; p++)
            if(self->vector[i] == *p)
                count++;
        if(count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline A
JOIN(A, substr)(A* self, size_t index, size_t size)
{
    A s = JOIN(A, init)((T*)"");
    JOIN(A, resize )(&s, size, '\0');
    for(size_t i = 0; i < size; i++)
        // FIXME
        s.vector[i] = self->vector[index + i];
    return s;
}

/* decompose only */
static inline str*
JOIN(A, NFD)(A* self)
{
    if (self->normalized == NFD)
        return self->same_norm ? (str*)self : self->normstr;
    if (!self->normstr)
    {
        str _norm = str_init("");
        str_resize(&_norm, self->capacity * 2, '\0');
        self->normstr = &_norm;
    }
    str *norm = self->normstr;
#ifdef _LIBUNISTRING_VERSION
    norm->vector = (char*)u8_normalize(UNINORM_NFD, self->vector, self->size,
                                       norm->vector, &norm->size);
#else
    // TODO other backends
    strcpy (norm->vector, (char*)self->vector);
#endif
    if (strcmp(norm->vector, (char*)self->vector) == 0)
        self->same_norm = 1;
       // free norm?
    return self->normstr;
}

/* decompose, reorder, compose */
static inline str*
JOIN(A, NFC)(A* self)
{
    if (self->normalized == NFC)
        return self->same_norm ? (str*)self : self->normstr;
    if (!self->normstr)
    {
        str _norm = str_init("");
        str_resize(&_norm, self->capacity * 2, '\0');
        self->normstr = &_norm;
    }
    str *norm = self->normstr;
#ifdef _LIBUNISTRING_VERSION
    norm->vector = (char*)u8_normalize(UNINORM_NFC, self->vector, self->size,
                                       norm->vector, &norm->size);
#else
    // TODO other backends
    strcpy (norm->vector, (char*)self->vector);
#endif 
    /*
    dest = self->norm_value;
    dmax = self->norm_capacity;
    while (dmax > 0) {
         char *p = self->vector;
         uint32_t cp = u8str_decode((char8_t**)&self->vector);
         int c = u8str_decomp (dest, dmax, cp, 0);
         if (c > 0) {
            dest -= c;
            dmax += c;
         } else if (c == 0) {
            *dest++ = *src;
            dmax--;
         } else {
            // error("u8str_decomp: decomposition error", -c)
            return;
         }
    }
    */
    self->normalized = NFC;
    if (strcmp(norm->vector, (char*)self->vector) == 0)
        self->same_norm = 1;
    return self->normstr;
}

static inline A*
JOIN(A, normalize)(A* self)
{
    JOIN(A, NFC)(self);
    return self;
}

/* Assuming arg `s` is normalized.
   W3C recommends not to normalize. We think different.
 */
static inline int
JOIN(A, compare)(A* self, const T* s)
{
    if (!self->normalized)
    {
        JOIN(A, normalize)(self);
        return strcmp (self->normstr->vector, (char*)s);
    }
    else
        return strcmp ((char*)self->vector, (char*)s);
}

static inline int
JOIN(A, key_compare)(A* self, A* s)
{
    if (!self->normalized)
    {
        JOIN(A, normalize)(self);
        return strcmp (self->normstr->vector, (char*)s->vector);
    }
    else
        return strcmp ((char*)self->vector, (char*)s->vector);
}

#ifdef HOLD /* for u8ident.h */
# undef HOLD
#else
# undef POD
# undef T
# undef A
# undef I
# undef vec
# undef u8str
# undef u8str_char8_t
#endif

#endif
