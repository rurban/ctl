/* A vector class
   SPDX-License-Identifier: MIT */
#ifndef __CTL_STRING__H__
#define __CTL_STRING__H__

#ifdef T
#error "Template type T defined for <ctl/string.h>"
#endif

#define CTL_STR
#define HOLD
#define POD
#define T char
#define vec_char str
#define MUST_ALIGN_16(T) (sizeof(T) == sizeof(char))
#define str_init str___INIT
#define str_equal str___EQUAL
#define str_find str___FIND
#define str_begin str_it_begin
#define str_end str_it_end

#define str_foreach(self, it)                                                                                          \
    if ((self)->size)                                                                                                  \
        for (char *it = &(self)->vector[0]; it < &(self)->vector[(self)->size]; it++)
#define str_foreach_range(it, first, last)                                                                             \
    if (last)                                                                                                          \
        for (char *it = first; it < last; it++)

#include <ctl/vector.h>

#undef str_init
#undef str_equal
#undef str_find
#undef str_begin
#undef str_end
#undef vec_char

#include <stdint.h>
#include <string.h>

static inline char *str_begin(str *self)
{
    return &self->vector[0];
}

static inline char *str_end(str *self)
{
    return &self->vector[self->size];
}

// if we compare char by char, for algorithms like sort
static inline int str_char_compare(char *a, char *b)
{
    return *a < *b;
}

static inline int str_char_equal(char *a, char *b)
{
    return *a == *b;
}

static inline str str_init(const char *c_str)
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
    for (const char *s = c_str; *s; s++)
        str_push_back(&self, *s);
    return self;
}

static inline void str_append(str *self, const char *s)
{
    size_t start = self->size;
    size_t len = strlen(s);
    str_resize(self, self->size + len, '\0');
    for (size_t i = 0; i < len; i++)
        self->vector[start + i] = s[i];
}

static inline void str_insert_str(str *self, size_t index, const char *s)
{
    size_t start = self->size;
    size_t len = strlen(s);
    str_resize(self, self->size + len, '\0');
    self->size = start;
    while (len != 0)
    {
        len--;
        str_insert_index(self, index, s[len]);
    }
}

static inline void str_replace(str *self, size_t index, size_t size, const char *s)
{
    size_t end = index + size;
    if (end >= self->size)
        end = self->size;
    for (size_t i = index; i < end; i++)
        str_erase_index(self, index);
    str_insert_str(self, index, s);
}

static inline char *str_c_str(str *self)
{
    return str_data(self);
}

static inline size_t str_find(str *self, const char *s)
{
    char *c_str = self->vector;
    char *found = strstr(c_str, s);
    if (found)
        return found - c_str;
    return SIZE_MAX;
}

static inline int str_count(str *self, char c)
{
    size_t count = 0;
    for (size_t i = 0; i < self->size; i++)
        if (self->vector[i] == c)
            count++;
    return count;
}

static inline size_t str_rfind(str *self, const char *s)
{
    char *c_str = self->vector;
    for (size_t i = self->size; i != SIZE_MAX; i--)
    {
        char *found = strstr(&c_str[i], s);
        if (found)
            return found - c_str;
    }
    return SIZE_MAX;
}

// i.e. strcspn, but returning the first found match
static inline bool str_find_first_of_range(str_it *range1, str_it *range2)
{

    if (str_it_done(range1) || str_it_done(range2))
        return false;
    str *self = range1->container;
    str *other = range2->container;
    // temp. set \0 at range1->end and range2->end.
    // this looks expensive, but glibc is much faster than naively as below.
    // it splits range2 into 4 parallelizable tables.
    char e1 = 0, e2 = 0;
    size_t off;
    if (range1->end != &self->vector[self->size])
    {
        e1 = *range1->end;
        *range1->end = '\0';
    }
    if (UNLIKELY(range2->end != &other->vector[other->size]))
    {
        e2 = *range2->end;
        *range2->end = '\0';
    }
    off = strcspn(range1->ref, range2->ref);
    if (e1)
        *range1->end = e1;
    if (UNLIKELY(e2))
        *range2->end = e2;
    size_t start1 = range1->ref - self->vector;
    off += start1;
    if (&self->vector[off] < range1->end)
    {
        range1->ref = &self->vector[off];
        return true;
    }
    else
    {
        str_it_set_done(range1);
        return false;
    }
}

// see algorithm.h for the range variant
static inline size_t str_find_first_of(str *self, const char *s)
{
#if 1
    size_t i = strcspn(self->vector, s);
    return i >= self->size ? SIZE_MAX : i;
#else
    for (size_t i = 0; i < self->size; i++)
        for (const char *p = s; *p; p++)
            if (self->vector[i] == *p)
                return i;
    return SIZE_MAX;
#endif
}

static inline size_t str_find_last_of(str *self, const char *s)
{
    for (size_t i = self->size; i != SIZE_MAX; i--)
        for (const char *p = s; *p; p++)
            if (self->vector[i] == *p)
                return i;
    return SIZE_MAX;
}

static inline size_t str_find_first_not_of(str *self, const char *s)
{
    for (size_t i = 0; i < self->size; i++)
    {
        size_t count = 0;
        for (const char *p = s; *p; p++)
            if (self->vector[i] == *p)
                count++;
        if (count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline size_t str_find_last_not_of(str *self, const char *s)
{
    for (size_t i = self->size - 1; i != SIZE_MAX; i--)
    {
        size_t count = 0;
        for (const char *p = s; *p; p++)
            if (self->vector[i] == *p)
                count++;
        if (count == 0)
            return i;
    }
    return SIZE_MAX;
}

static inline str str_substr(str *self, size_t index, size_t size)
{
    str substr = str_init("");
#ifndef _LIBCPP_STD_VER // gcc shrinks, llvm not
#endif
    str_resize(&substr, size, '\0');
    for (size_t i = 0; i < size; i++)
        substr.vector[i] = self->vector[index + i];
    return substr;
}

/* STL clash */
static inline int str_compare(str *self, const char *s)
{
    return strcmp(self->vector, s);
}

/* STL clash
static inline int
str_equal(str* self, const char* s)
{
    return str_compare(self, other) == 0;
}
*/

static inline int str_key_compare(str *self, str *other)
{
    return strcmp(self->vector, other->vector);
}

static inline int str_equal(str *self, str *other)
{
    return strcmp(self->vector, other->vector) == 0;
}

#undef POD
#ifndef HOLD
#undef vec_char
#undef T
#else
#undef HOLD
#endif
#undef CTL_STR

#endif // once
