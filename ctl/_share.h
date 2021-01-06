// Commonalities; expandable by all containers.
//
// DO NOT STANDALONE INCLUDE.
//

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
    return *a < *b ? 1 : *a == *b ? 0 : -1;
}

static inline int
_JOIN(A, _default_integral_equal)(T* a, T* b)
{
    return *a == *b;
    // or the slow *a == *b:
    /*return _JOIN(A, _default_integral_compare)(a, b) == 0 &&
             _JOIN(A, _default_integral_compare)(b, a) == 0;
    */
}

#include <string.h>

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
           _strEQcc(CTL_STRINGIFY(T), "unsigned_int") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_long") ||
           _strEQcc(CTL_STRINGIFY(T), "unsigned_char");
}
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

#ifdef DEBUG

static inline I*
JOIN(A, find_if)(A* self, I* first, I* last, int _match(T*))
{
    foreach(A, self, it)
        if(_match(it.ref))
            return first;
    return last;
}

static inline I*
JOIN(A, find_if_not)(A* self, I* first, I* last, int _match(T*))
{
    foreach(A, self, it)
        if(!_match(it.ref))
            return first;
    return last;
}

static inline bool
JOIN(A, all_of)(A* self, I* first, I* last, int _match(T*))
{
    return JOIN(A, find_if_not)(self, first, last, _match) == last;
}

static inline bool
JOIN(A, any_of)(A* self, I* first, I* last, int _match(T*))
{
    return JOIN(A, find_if)(self, first, last, _match) != last;
}

static inline bool
JOIN(A, none_of)(A* self, I* first, I* last, int _match(T*))
{
    return JOIN(A, find_if)(self, first, last, _match) == last;
}

#endif
