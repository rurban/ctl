/* A vector class
   SPDX-License-Identifier: MIT */
#ifndef __CTL_STRING__H__
#define __CTL_STRING__H__

#ifdef T
#error "Template type T defined for <ctl/string.h>"
#endif

#define CTL_STR
#define vec_char str
#define HOLD
#define POD
#define T char
#define MUST_ALIGN_16(T) (sizeof(T) == sizeof(char))
#define str_init str___INIT
#define str_equal str___EQUAL
#define str_find str___FIND

#define foreach(C, T, self, it) \
   if (self->size) \
     for(T* it = &self->vector[0]; \
         it < &self->vector[self->size]; \
         it++)
#define foreach_ref(C, T, self, it, ref) \
   T* ref; \
   if (self->size) \
       for(T* it = ref = &self->vector[0]; \
           it < &self->vector[self->size]; \
           it++, ref = it)
#define foreach_range(C, T, self, it, first, last) \
   if (last) \
       for(T* it = first; \
           it < last; \
           it++)
#define foreach_ref_range(C, T, self, it, ref, first, last) \
    T* ref; \
    if (last) \
        for(T* it = ref = first; \
            it < last; \
            it++, ref = it)

#include <ctl/vector.h>

#undef str_init
#undef str_equal
#undef str_find
#undef vec_char

#include <stdint.h>
#include <string.h>

// if we compare char by char, for algorithms like sort
static inline int
str_char_compare(char* a, char* b)
{
    return *a > *b;
}

static inline int
str_char_equal(char* a, char* b)
{
    return *a == *b;
}

static inline str
str_init(const char* c_str)
{
    str self = str___INIT();
    size_t len = strlen(c_str);
#ifndef _LIBCPP_STD_VER
    size_t min = 15;
#else
    size_t min = 22;
#endif
    self.compare = str_char_compare;
    self.equal = str_char_equal;
    str_reserve(&self, len < min ? min : len);
    for(const char* s = c_str; *s; s++)
        str_push_back(&self, *s);
    return self;
}

static inline void
str_append(str* self, const char* s)
{
    size_t start = self->size;
    size_t len = strlen(s);
    str_resize(self, self->size + len, '\0');
    for(size_t i = 0; i < len; i++)
        self->vector[start + i] = s[i];
}

static inline void
str_insert_str(str* self, size_t index, const char* s)
{
    size_t start = self->size;
    size_t len = strlen(s);
    str_resize(self, self->size + len, '\0');
    self->size = start;
    while(len != 0)
    {
        len--;
        str_insert(self, index, s[len]);
    }
}

static inline void
str_replace(str* self, size_t index, size_t size, const char* s)
{
    size_t end = index + size;
    if(end >= self->size)
        end = self->size;
    for(size_t i = index; i < end; i++)
        str_erase(self, index);
    str_insert_str(self, index, s);
}

static inline char*
str_c_str(str* self)
{
    return str_data(self);
}

static inline size_t
str_find(str* self, const char* s)
{
    char* c_str = self->vector;
    char* found = strstr(c_str, s);
    if(found)
        return found - c_str;
    return SIZE_MAX;
}

static inline int
str_count(str* self, char c)
{
    size_t count = 0;
    for(size_t i = 0; i < self->size; i++)
        if(self->vector[i] == c)
            count++;
    return count;
}

static inline size_t
str_rfind(str* self, const char* s)
{
    char* c_str = self->vector;
    for(size_t i = self->size; i != SIZE_MAX; i--)
    {
        char* found = strstr(&c_str[i], s);
        if(found)
            return found - c_str;
    }
    return SIZE_MAX;
}

static inline size_t
str_find_first_of(str* self, const char* s)
{
    for(size_t i = 0; i < self->size; i++)
    for(const char* p = s; *p; p++)
        if(self->vector[i] == *p)
            return i;
    return SIZE_MAX;
}

static inline size_t
str_find_last_of(str* self, const char* s)
{
    for(size_t i = self->size; i != SIZE_MAX; i--)
    for(const char* p = s; *p; p++)
        if(self->vector[i] == *p)
            return i;
    return SIZE_MAX;
}

static inline size_t
str_find_first_not_of(str* self, const char* s)
{
    for(size_t i = 0; i < self->size; i++)
    {
        size_t count = 0;
        for(const char* p = s; *p; p++)
            if(self->vector[i] == *p)
                count++;
        if(count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline size_t
str_find_last_not_of(str* self, const char* s)
{
    for(size_t i = self->size - 1; i != SIZE_MAX; i--)
    {
        size_t count = 0;
        for(const char* p = s; *p; p++)
            if(self->vector[i] == *p)
                count++;
        if(count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline str
str_substr(str* self, size_t index, size_t size)
{
    str substr = str_init("");
#ifndef _LIBCPP_STD_VER // gcc shrinks, llvm not
#endif
    str_resize (&substr, size, '\0');
    for(size_t i = 0; i < size; i++)
        substr.vector[i] = self->vector[index + i];
    return substr;
}

/* STL clash */
static inline int
str_compare(str* self, const char* s)
{
    return strcmp (self->vector, s);
}

/* STL clash
static inline int
str_equal(str* self, const char* s)
{
    return str_compare(self, other) == 0;
}
*/

static inline int
str_key_compare(str* self, str* other)
{
    return strcmp (self->vector, other->vector);
}

static inline int
str_equal(str* self, str* other)
{
    return strcmp (self->vector, other->vector) == 0;
}

#ifndef HOLD
#undef POD
#undef vec_char
#undef T
#undef IT
#else
#undef HOLD
#endif
#undef CTL_STR

#undef foreach
#undef foreach_ref
#undef foreach_range
#undef foreach_ref_range

#endif // once
