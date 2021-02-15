/* Type utilities, to apply default equal, compare, hash methods for intergral types.
   See MIT LICENSE.
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

static inline size_t _JOIN(A, _default_integral_hash)(T *a)
{
    return (size_t)*a;
}

#include <string.h>

#if defined str || defined u8string || defined charp || defined u8ident || defined ucharp

static inline size_t _JOIN(A, _default_string_hash)(T *key)
{
    size_t h;
    /* FNV1a, not wyhash */
    h = 2166136261u;
    for (unsigned i = 0; i < strlen((char *)key); i++)
    {
        h ^= (unsigned char)key[i];
        h *= 16777619;
    }
    return h;
}

#endif

#define CTL_STRINGIFY_HELPER(n) #n
#define CTL_STRINGIFY(n) CTL_STRINGIFY_HELPER(n)
#define _strEQcc(s1c, s2c) !strcmp(s1c "", s2c "")

static inline bool _JOIN(A, _type_is_integral)()
{
    return _strEQcc(CTL_STRINGIFY(T), "int") || _strEQcc(CTL_STRINGIFY(T), "long") ||
           _strEQcc(CTL_STRINGIFY(T), "bool") || _strEQcc(CTL_STRINGIFY(T), "char") ||
           _strEQcc(CTL_STRINGIFY(T), "short") || _strEQcc(CTL_STRINGIFY(T), "float") ||
           _strEQcc(CTL_STRINGIFY(T), "double") || _strEQcc(CTL_STRINGIFY(T), "char8_t") ||
           _strEQcc(CTL_STRINGIFY(T), "wchar_t") || _strEQcc(CTL_STRINGIFY(T), "char16_t") ||
           _strEQcc(CTL_STRINGIFY(T), "char32_t") || _strEQcc(CTL_STRINGIFY(T), "long_double") ||
           _strEQcc(CTL_STRINGIFY(T), "long_long") || _strEQcc(CTL_STRINGIFY(T), "int8_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint8_t") || _strEQcc(CTL_STRINGIFY(T), "uint16_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint32_t") || _strEQcc(CTL_STRINGIFY(T), "uint64_t") ||
           _strEQcc(CTL_STRINGIFY(T), "int16_t") || _strEQcc(CTL_STRINGIFY(T), "int32_t") ||
           _strEQcc(CTL_STRINGIFY(T), "int64_t") || _strEQcc(CTL_STRINGIFY(T), "unsigned_int") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_long") || _strEQcc(CTL_STRINGIFY(T), "unsigned_long_long") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_char") ||
           /* and some common abbrevations */
           _strEQcc(CTL_STRINGIFY(T), "uchar") || _strEQcc(CTL_STRINGIFY(T), "uint") ||
           _strEQcc(CTL_STRINGIFY(T), "ulong") || _strEQcc(CTL_STRINGIFY(T), "ldbl") ||
           _strEQcc(CTL_STRINGIFY(T), "llong");
}

// not C++
#ifndef __cplusplus
#define __set_str_hash(self, t)                                                                                        \
    {                                                                                                                  \
        typeof(t) tmp = (x);                                                                                           \
        if (__builtin_types_compatible_p(typeof(t), char *))                                                           \
            self->hash = _JOIN(A, _default_string_hash);                                                               \
        else if (__builtin_types_compatible_p(typeof(t), unsigned char *))                                             \
            self->hash = _JOIN(A, _default_string_hash);                                                               \
    }
#else
#define __set_str_hash(self, t) self->hash = _JOIN(A, _default_string_hash)
#endif

static inline void _JOIN(A, _set_default_methods)(A *self)
{
#if !defined CTL_STR
#if defined str || defined u8string || defined charp || defined u8ident || defined ucharp
    {
#ifdef CTL_USET
        if (!self->hash)
            __set_str_hash(self, T);
#else
        if (!self->compare)
            self->compare = str_key_compare;
#endif
        if (!self->equal)
            self->equal = str_equal;
    }
    else
#endif
#endif
#ifdef CTL_USET
        if (!self->hash)
            self->hash = _JOIN(A, _default_integral_hash);
#else
    if (!self->compare)
        self->compare = _JOIN(A, _default_integral_compare);
#endif
    if (!self->equal)
        self->equal = _JOIN(A, _default_integral_equal);
}

#else

// non-integral types have no default methods. you need to set
static inline void _JOIN(A, _set_default_methods)(A *self)
{
    (void)self;
}

#endif
