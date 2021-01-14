/* A vector class
   SPDX-License-Identifier: MIT */
#ifndef __STR__H__
#define __STR__H__

#ifdef T
#error "Template type T defined for <ctl/string.h>"
#endif

#define CTL_STR
#define vec_char str
#define POD
#define T char
#define MUST_ALIGN_16(T) (sizeof(T) == sizeof(char))
#define str_init str___INIT
#define str_equal str___EQUAL
#define str_find str___FIND
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
        self->value[start + i] = s[i];
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
    char* c_str = self->value;
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
        if(self->value[i] == c)
            count++;
    return count;
}

static inline size_t
str_rfind(str* self, const char* s)
{
    char* c_str = self->value;
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
        if(self->value[i] == *p)
            return i;
    return SIZE_MAX;
}

static inline size_t
str_find_last_of(str* self, const char* s)
{
    for(size_t i = self->size; i != SIZE_MAX; i--)
    for(const char* p = s; *p; p++)
        if(self->value[i] == *p)
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
            if(self->value[i] == *p)
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
            if(self->value[i] == *p)
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
    str_resize (&substr, size, '\0');
    for(size_t i = 0; i < size; i++)
        substr.value[i] = self->value[index + i];
    return substr;
}

/* STL clash */
static inline int
str_compare(str* self, const char* s)
{
    return strcmp (self->value, s);
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
    return strcmp (self->value, other->value);
}

#undef CTL_STR
#endif
