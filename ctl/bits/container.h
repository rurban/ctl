/* Common bits for all containers.
   See MIT LICENSE. */

// DO NOT STANDALONE INCLUDE.
#if !defined CTL_LIST && !defined CTL_SET && !defined CTL_USET && \
    !defined CTL_VEC && !defined CTL_DEQ
#error "No CTL container defined for <ctl/bits/container.h>"
#endif

#include <stdbool.h>

static inline int
JOIN(A, empty)(A* self)
{
    return self->size == 0;
}

static inline size_t
JOIN(A, size)(A* self)
{
    return self->size;
}

static inline size_t
JOIN(A, max_size)()
{
    return 4294967296 / sizeof(T); // 32bit at most. avoid DDOS
}

static inline I
JOIN(I, each)(A* a)
{
    return JOIN(A, empty)(a)
         ? JOIN(I, range)(a, NULL, NULL)
         : JOIN(I, range)(a, JOIN(A, begin)(a), JOIN(A, end)(a));
}

static inline T
JOIN(A, implicit_copy)(T* self)
{
    return *self;
}

// not valid for uset, str
#if !defined(CTL_USET) && !defined(CTL_STR)
static inline int
JOIN(A, equal)(A* self, A* other)
{
    if(self->size != other->size)
        return 0;
    I a = JOIN(I, each)(self);
    I b = JOIN(I, each)(other);
    while(!a.done && !b.done)
    {
        if(self->equal)
        {
            if(!self->equal(a.ref, b.ref))
                return 0;
        }
        else
        {
            if(self->compare(a.ref, b.ref) ||
               self->compare(b.ref, a.ref))
                return 0;
        }
        a.step(&a);
        b.step(&b);
    }
    return 1;
}
#endif

// Type utilities

// is_integral type utilities, to make equal and compare optional for simple POD types
/*
#define _define_integral_compare(T)                                  \
    static inline int _##T##_compare(T* a, T* b) { return *a < *b; } \
    static inline int _##T##_equal(T* a, T* b)   { return _##T##_compare(a, b) == 0; }

_define_integral_compare(int)
_define_integral_compare(long)
#undef _define_integral_compare
*/

#if defined(POD) && !defined(NOT_INTEGRAL)

static inline int
_JOIN(A, _default_integral_compare)(T* a, T* b)
{
    return *a > *b;
}

static inline int
_JOIN(A, _default_integral_equal)(T* a, T* b)
{
    return *a == *b;
    // or the slow
    /*return _JOIN(A, _default_integral_compare)(a, b) == 0 &&
             _JOIN(A, _default_integral_compare)(b, a) == 0;
    */
}

static inline size_t
_JOIN(A, _default_integral_hash)(T* a)
{
    return *a;
}

#include <string.h>

# if defined str || defined u8string || \
        defined charp || defined u8ident || \
        defined ucharp

static inline size_t
_JOIN(A, _default_string_hash)(T* key)
{
  size_t h;
  /* FNV1a, not wyhash */
  h = 2166136261u;
  for (unsigned i = 0; i < strlen((char*)key); i++) {
    h ^= (unsigned char)key[i];
    h *= 16777619;
  }
  return h;
}

#endif

#define CTL_STRINGIFY_HELPER(n) #n
#define CTL_STRINGIFY(n) CTL_STRINGIFY_HELPER(n)
#define _strEQcc(s1c, s2c) !strcmp (s1c "", s2c "")

static inline bool
_JOIN(A, _type_is_integral)()
{
    return _strEQcc(CTL_STRINGIFY(T), "int") ||
           _strEQcc(CTL_STRINGIFY(T), "long") ||
           _strEQcc(CTL_STRINGIFY(T), "bool") ||
           _strEQcc(CTL_STRINGIFY(T), "char") ||
           _strEQcc(CTL_STRINGIFY(T), "short") ||
           _strEQcc(CTL_STRINGIFY(T), "float") ||
           _strEQcc(CTL_STRINGIFY(T), "double") ||
           _strEQcc(CTL_STRINGIFY(T), "char8_t") ||
           _strEQcc(CTL_STRINGIFY(T), "wchar_t") ||
           _strEQcc(CTL_STRINGIFY(T), "char16_t") ||
           _strEQcc(CTL_STRINGIFY(T), "char32_t") ||
           _strEQcc(CTL_STRINGIFY(T), "long_double") ||
           _strEQcc(CTL_STRINGIFY(T), "long_long") ||
           _strEQcc(CTL_STRINGIFY(T), "int8_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint8_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint16_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint32_t") ||
           _strEQcc(CTL_STRINGIFY(T), "uint64_t") ||
           _strEQcc(CTL_STRINGIFY(T), "int16_t") ||
           _strEQcc(CTL_STRINGIFY(T), "int32_t") ||
           _strEQcc(CTL_STRINGIFY(T), "int64_t") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_int") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_long") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_long_long") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_char") ||
            /* and some common abbrevations */
           _strEQcc(CTL_STRINGIFY(T), "uchar") ||
           _strEQcc(CTL_STRINGIFY(T), "uint") ||
           _strEQcc(CTL_STRINGIFY(T), "ulong") ||
           _strEQcc(CTL_STRINGIFY(T), "ldbl") ||
           _strEQcc(CTL_STRINGIFY(T), "llong");
}

// not C++
#ifndef __cplusplus
#define __set_str_hash(self,t)                                    \
    {                                                             \
        typeof (t) tmp = (x);                                     \
        if (__builtin_types_compatible_p (typeof (t), char*))     \
            self->hash = _JOIN(A, _default_string_hash);          \
        else if (__builtin_types_compatible_p (typeof (t), unsigned char*)) \
            self->hash = _JOIN(A, _default_string_hash);          \
    }
#else
#define __set_str_hash(self,t)                                    \
    self->hash = _JOIN(A, _default_string_hash)
#endif

static inline void
_JOIN(A, _set_default_methods)(A* self)
{
#if !defined CTL_STR
# if defined str || defined u8string || \
        defined charp || defined u8ident || \
        defined ucharp
    {
#  ifdef CTL_USET
        __set_str_hash(self,T);
        // FIXME u8 compare and equal are different
        if (!self->compare) // default arg
            self->compare = _JOIN(A, _default_string_compare);
#  else
        self->compare = _JOIN(A, _default_string_compare);
#  endif
        self->equal = _JOIN(A, _default_string_equal);
    }
    else
# endif
#endif
#ifdef CTL_USET
    self->hash = _JOIN(A, _default_integral_hash);
    if (!self->compare) // default arg
        self->compare = _JOIN(A, _default_integral_compare);
#else
    self->compare = _JOIN(A, _default_integral_compare);
#endif
    self->equal = _JOIN(A, _default_integral_equal);
}
#else

// non-integral types have no default methods. you need to set
static inline void
_JOIN(A, _set_default_methods)(A* self) { (void) self; }

#endif

static inline int
JOIN(A, _equal)(A* self, T* a, T* b)
{
    if(self->equal)
        return self->equal(a, b);
    else
        return !self->compare(a, b) &&
               !self->compare(b, a);
}

// if parent, include only for the child later.
// parents are vec: str, pqu. deq: queue, stack. set: map, uset: umap
// ignore str: u8str, u8id for now.
#undef _IS_PARENT_CHILD_FOLLOWS
#if defined CTL_VEC && (defined CTL_STACK || defined CTL_STR  || defined CTL_U8STR)
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_DEQ && (defined CTL_QUEUE || defined CTL_STACK)
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_SET && defined CTL_MAP
#define _IS_PARENT_CHILD_FOLLOWS
#endif
#if defined CTL_USET && defined CTL_UMAP
#define _IS_PARENT_CHILD_FOLLOWS
#endif

#ifndef _IS_PARENT_CHILD_FOLLOWS
#include <ctl/algorithm.h>
#endif
#undef _IS_PARENT_CHILD_FOLLOWS
