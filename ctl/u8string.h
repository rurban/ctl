#ifndef __CTL_U8STRING_H__
#define __CTL_U8STRING_H__

#ifdef T
#error "Template type T defined for <ctl/u8string.h>"
#endif

#ifndef __cpp_lib_char8_t
typedef unsigned char char8_t;
#endif

#define HOLD
#define T char8_t
#ifndef vec
# define u8str_char8_t u8str
# define vec u8str
# define A u8str
#endif

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
    str rawstr;
    str *normstr;
    void (*free)(T*);
    T (*copy)(T*);
#ifdef COMPARE
    int (*compare)(T*, T*);
#endif
    unsigned valid:1;      /* is already validated */
    unsigned repair:1;     /* do repair */
    unsigned normalized:3; /* 6 normalize enums. NONE,NFD,NFC,...*/
    unsigned same_norm:1;  /* optimization norm_value == value */
} A;

#define compare __COMPARE
#include <ctl/string.h>
#undef compare

/* decompose only */
static inline str*
JOIN(A, NFD)(A* self)
{
    if (self->normalized == NFD)
        return self;
    if (!self->normstr)
    {
        str norm = str_init(self->rawstr.vector);
        self->normstr = &norm;
    }
    return self->normstr;
}

/* decompose, reorder, compose */
static inline str*
JOIN(A, NFC)(A* self)
{
    if (self->normalized == NFC)
        return self;
    if (!self->normstr)
    {
        str _norm = str_init(self->rawstr.vector);
        self->normstr = &_norm;
    }
    str *norm = self->normstr;
    norm->capacity = self->rawstr.size * 2;
    norm->vector = (T*) malloc (norm->capacity);
    // TODO
    strcpy ((char*)norm->vector, (char*)self->rawstr.vector);
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
    return self->normstr;
}

static inline A*
JOIN(A, normalize)(A* self)
{
    JOIN(A, NFC)(self);
    return self;
}

/* Assuming s is normalized.
   W3C recommends not to normalize. We think different.
 */
static inline int
JOIN(A, compare)(A* self, const T* s)
{
    if (!self->normalized)
    {
        JOIN(A, normalize)(self);
        return strcmp ((char*)self->normstr->vector, (char*)s);
    }
    else
        return strcmp ((char*)self->rawstr.vector, (char*)s);
}

#ifdef HOLD /* for u8ident.h */
# undef HOLD
#else
# undef T
# undef A
# undef u8str
#endif

#endif
