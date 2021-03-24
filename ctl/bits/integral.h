/* Type utilities, to apply default equal, compare, hash methods for integral
 * types, and simple char* keys.
 *
 * SPDX-License-Identifier: MIT
 */

// is_integral type utilities, to make equal and compare optional for simple POD types
/*
#define _define_integral_compare(T)                                  \
    static inline int _##T##_compare(T* a, T* b) { return *a < *b; } \
    static inline int _##T##_equal(T* a, T* b) {                     \
       return !_##T##_compare(a, b) && !_##T##_compare(b, a); }

_define_integral_compare(int)
_define_integral_compare(long)
#undef _define_integral_compare
*/

#include <string.h>

#define CTL_STRINGIFY_HELPER(n) #n
#define CTL_STRINGIFY(n) CTL_STRINGIFY_HELPER(n)
#define _strEQ(s1, s2c)    !strcmp(s1, s2c "")
#define _strEQcc(s1c, s2c) !strcmp(s1c "", s2c "")

static inline bool _JOIN(A, _type_is_string)(const char* typ)
{
    return _strEQ(typ, "str") || _strEQ(typ, "char*") ||
           _strEQ(typ, "unsigned char*") || _strEQ(typ, "ucharp") ||
           _strEQ(typ, "u8string") || _strEQ(typ, "u8ident");
}

static inline int _JOIN(A, _default_charp_equal)(const char **s1, const char **s2)
{
    return strcmp(*s1, *s2) == 0;
}
static inline int _JOIN(A, _default_charp_compare)(const char **s1, const char **s2)
{
    return strcmp(*s1, *s2) < 0;
}

#if defined CTL_USET || defined CTL_UMAP

#if (defined POD && !defined TK) || (defined PODK && defined TK)
# ifdef TK
static inline size_t _JOIN(A, _default_charp_hash)(TK *key)
# else
static inline size_t _JOIN(A, _default_charp_hash)(T *key)
# endif
{
#if 1
    /* For now FNV1a, not wyhash nor o1hash */
    const unsigned char *s = (const unsigned char *)key;
    size_t h = 2166136261u;
    for (unsigned i = 0; i < strlen(s); i++)
    {
        h ^= s[i];
        h *= 16777619;
    }
    return h;
#endif
}
#endif // POD

// not C++
#ifndef __cplusplus
#define __set_charp_hash(self, t)                                                                                        \
    {                                                                                                                  \
        /*__typeof__(t) tmp = (self);*/                                                                                \
        if (__builtin_types_compatible_p(__typeof__(t), char *) ||                                                     \
            __builtin_types_compatible_p(__typeof__(t), unsigned char *) ||                                            \
            __builtin_types_compatible_p(__typeof__(t), int8_t *) ||                                                   \
            __builtin_types_compatible_p(__typeof__(t), uint8_t *))                                                    \
            self->hash = _JOIN(A, _default_charp_hash);                                                               \
    }
#elif (defined POD && !defined TK) || (defined PODK && defined TK)
# define __set_charp_hash(self, t) self->hash = _JOIN(A, _default_charp_hash);
#else
# define __set_charp_hash(self, t) {}
#endif

#endif // USET,UMAP

// default integral methods (POD defines only the value)
#if defined(POD) && !defined(NOT_INTEGRAL)

static inline int _JOIN(A, _default_integral_compare3)(T *a, T *b)
{
    return *a > *b ? 1 : *a < *b ? -1 : 0;
}
static inline int _JOIN(A, _default_integral_compare)(T *a, T *b)
{
    return *a < *b;
}

static inline int _JOIN(A, _default_integral_equal)(T *a, T *b)
{
    return *a == *b;
    // or the slow 2x compare, which is used in _equal.
    /*return _JOIN(A, _default_integral_compare)(a, b) == 0 &&
             _JOIN(A, _default_integral_compare)(b, a) == 0;
    */
}

#if defined CTL_USET || defined CTL_UMAP
static inline size_t _JOIN(A, _default_integral_hash)(T *a)
{
    return (size_t)*a;
}
#endif // USET,UMAP

// unused
static inline bool _JOIN(A, _type_is_integral)(const char* typ)
{
    return _strEQ(typ, "int") || _strEQ(typ, "long") ||
           _strEQ(typ, "bool") || _strEQ(typ, "char") ||
           _strEQ(typ, "short") || _strEQ(typ, "float") ||
           _strEQ(typ, "double") || _strEQ(typ, "char8_t") ||
           _strEQ(typ, "wchar_t") || _strEQ(typ, "char16_t") ||
           _strEQ(typ, "char32_t") || _strEQ(typ, "long_double") ||
           _strEQ(typ, "long_long") || _strEQ(typ, "int8_t") ||
           _strEQ(typ, "uint8_t") || _strEQ(typ, "uint16_t") ||
           _strEQ(typ, "uint32_t") || _strEQ(typ, "uint64_t") ||
           _strEQ(typ, "int16_t") || _strEQ(typ, "int32_t") ||
           _strEQ(typ, "int64_t") || _strEQ(typ, "unsigned_int") ||
           _strEQ(typ, "unsigned_long") || _strEQ(typ, "unsigned_long_long") ||
           _strEQ(typ, "unsigned_char") ||
           /* and some common abbrevations */
           _strEQ(typ, "uchar") || _strEQ(typ, "uint") ||
           _strEQ(typ, "ulong") || _strEQ(typ, "ldbl") ||
           _strEQ(typ, "llong");
}

static inline void _JOIN(A, _set_default_methods)(A *self)
{
#ifdef TK
    if (_JOIN(A, _type_is_string)(CTL_STRINGIFY(TK)))
    {
# if defined CTL_UMAP
        if (!self->hash)
            __set_charp_hash(self, TK)
# else
        if (!self->compare)
#  if defined CTL_STR
            self->compare = str_key_compare;
#  else
            self->compare = (JOIN(A, compare_fn)) _JOIN(A, _default_charp_compare);
#  endif // STR
# endif
        if (!self->equal)
# if defined CTL_STR
            self->equal = str_equal;
# else
            self->equal = (JOIN(A, equal_fn)) _JOIN(A, _default_charp_equal);
# endif // STR
    }

#else // !TK

# if defined CTL_USET || defined CTL_UMAP
    if (!self->hash)
        self->hash = _JOIN(A, _default_integral_hash);
# else
    if (!self->compare)
        self->compare = _JOIN(A, _default_integral_compare);
# endif // USET,UMAP
    if (!self->equal)
        self->equal = _JOIN(A, _default_integral_equal);

#endif // TK
}

#else // defined(POD) && !defined(NOT_INTEGRAL)
// default string methods

// non-integral string types
static inline void _JOIN(A, _set_default_methods)(A *self)
{

#ifdef TK
    if (_JOIN(A, _type_is_string)(CTL_STRINGIFY(TK)))
    {
# if defined CTL_UMAP
        if (!self->hash)
            __set_charp_hash(self, T)
# elif defined CTL_STR
        if (!self->compare)
            self->compare = str_key_compare;
# else
        if (!self->compare)
            self->compare = (JOIN(A, compare_fn)) _JOIN(A, _default_charp_compare);
# endif // UMAP,STR
        if (!self->equal)
# if defined CTL_STR
            self->equal = str_equal;
# else
            self->equal = (JOIN(A, equal_fn)) _JOIN(A, _default_charp_equal);
# endif // STR
    }
#endif // TK

    if (_JOIN(A, _type_is_string)(CTL_STRINGIFY(T)))
    {
#if defined CTL_USET || defined CTL_UMAP
        if (!self->hash)
            __set_charp_hash(self, T)
#elif defined CTL_STR
        if (!self->compare)
            self->compare = str_key_compare;
# else
        if (!self->compare)
            self->compare = (JOIN(A, compare_fn)) _JOIN(A, _default_charp_compare);
#endif // USET,STR
        if (!self->equal)
# if defined CTL_STR
            self->equal = str_equal;
# else
            self->equal = (JOIN(A, equal_fn)) _JOIN(A, _default_charp_equal);
# endif // STR
    }
}

#endif // defined(POD) && !defined(NOT_INTEGRAL)
