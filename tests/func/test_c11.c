#include "../test.h"

#include <ctl/string.h> // MULTIPLE INCLUDES OKAY.
#include <ctl/string.h>

#ifdef POD
// this breaks FREE_VALUE
#error "POD leftover from ctl/string.h"
#endif

#define POD
#define T int
#include <ctl/unordered_set.h>

#ifdef POD
#error "POD leftover"
#endif

size_t int_hash(int *x)
{
    return abs(*x);
}

int int_equal(int *a, int *b)
{
    return *a == *b;
}

#include "charpint.hh"

size_t _str_hash(str *s)
{
    return FNV1a(*(const char **)s);
}

int _str_equal(str *a, str *b)
{
    return strcmp(*(char **)a, *(char **)b) == 0;
}

int _str_cmp(str *a, str *b)
{
    return strcmp(*(char **)a, *(char **)b);
}

#define T str
#include <ctl/set.h>

#ifdef POD
#error "POD leftover"
#endif

// we known about this special case
#define POD
#define NOT_INTEGRAL
typedef char *charp;
#define T charp
#include <ctl/set.h>

#ifdef POD
#error "POD leftover"
#endif

#define PODK
#define TK charp
#define T int
#include <ctl/unordered_map.h>

#ifdef PODK
#error "PODK leftover"
#endif

#define PODK
#define TK charp
#define T int
#include <ctl/map.h>

#ifdef PODK
#error "PODK leftover"
#endif

#define POD
#define T int
#include <ctl/stack.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/priority_queue.h>

#ifdef POD
#error "POD leftover"
#endif

// already defined by test.h
//#define POD
//#define T int
//#include <ctl/queue.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/list.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/forward_list.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/deque.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/set.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T char
#include <ctl/vector.h>

#ifdef POD
#error "POD leftover"
#endif

#define POD
#define T int
#include <ctl/vector.h>

#define POD
#define T unsigned
#include <ctl/vector.h>

#define POD
#define T float
#include <ctl/vector.h>

#define POD
#define T double
#include <ctl/vector.h>

#define POD
#define N 128
#define T double
#include <ctl/array.h>

#ifdef POD
#error "POD leftover"
#endif

typedef struct
{
    int x;
    int y;
} point;

#define POD
#define NOT_INTEGRAL
#define T point
#include <ctl/vector.h>

#ifdef POD
#error "POD leftover"
#endif

#define T str
#include <ctl/vector.h>

typedef struct
{
    vec_point path;
    str name;
} person;

static person person_init(size_t path_capacity, const char *first, const char *last)
{
    person self;
    self.path = vec_point_init();
    self.name = str_init(first);
    str_append(&self.name, " ");
    str_append(&self.name, last);
    vec_point_reserve(&self.path, path_capacity);
    return self;
}

static void person_free(person *self)
{
    vec_point_free(&self->path);
    str_free(&self->name);
}

static person person_copy(person *self)
{
    person copy = {
        vec_point_copy(&self->path),
        str_copy(&self->name),
    };
    return copy;
}

#define T person
#include <ctl/vector.h>

int main(void)
{
    {
        vec_int a = vec_int_init();
        vec_int_push_back(&a, 1);
        vec_int_push_back(&a, 2);
        vec_int_push_back(&a, 3);
        vec_int_push_back(&a, 4);
        vec_int_free(&a);
    }
    {
        const size_t size = 16;
        deq_int a = deq_int_init();
        for (size_t i = 0; i < size; i++)
            deq_int_push_back(&a, i);
        for (size_t i = 0; i < size; i++)
            deq_int_push_front(&a, i);
        deq_int_insert_index(&a, 1, 99);
        deq_int_sort(&a);
        deq_int_free(&a);
    }
    {
        list_int a = list_int_init();
        list_int_push_back(&a, 1);
        list_int_push_back(&a, 2);
        list_int_push_back(&a, 3);
        list_int_push_back(&a, 4);
        list_int_push_back(&a, 5);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 7);
        list_int_push_back(&a, 8);
        list_int_free(&a);
    }
    {
        slist_int a = slist_int_init();
        slist_int_push_front(&a, 1);
        slist_int_push_front(&a, 2);
        slist_int_push_front(&a, 3);
        slist_int_push_front(&a, 4);
        slist_int_push_front(&a, 5);
        slist_int_push_front(&a, 6);
        slist_int_push_front(&a, 7);
        slist_int_push_front(&a, 8);
        slist_int_unique(&a);
        slist_int_free(&a);
    }
    {
        vec_str b = vec_str_init();
        vec_str_push_back(&b, str_init("This"));
        vec_str_push_back(&b, str_init("is"));
        vec_str_push_back(&b, str_init("a"));
        vec_str_push_back(&b, str_init("test"));
        vec_str_resize(&b, 512, str_init(""));
        vec_str_free(&b);
    }
    {
        vec_person c = vec_person_init();
        vec_person_push_back(&c, person_init(128, "FIRST", "JONES"));
        vec_person_push_back(&c, person_init(256, "LAST", "ALEXA"));
        vec_person_push_back(&c, person_init(512, "NAME", "ANOTHER"));
        vec_person d = vec_person_copy(&c);
        vec_person_free(&c);
        vec_person_free(&d);
    }
    {
        list_int a = list_int_init();
        list_int_push_back(&a, 1);
        list_int_push_back(&a, 1);
        list_int_push_back(&a, 1);
        list_int_push_back(&a, 2);
        list_int_push_back(&a, 3);
        list_int_push_back(&a, 3);
        list_int_push_back(&a, 4);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 6);
        list_int_push_back(&a, 8);
        list_int_push_back(&a, 8);
        list_int_unique(&a);
        list_int_free(&a);
    }
#ifdef DEBUG
    {
        int j = 0;
        uset_int a = uset_int_init(int_hash, int_equal);
        // TODO skip default a.equal
        for (int i = 0; i > -27; i--)
            uset_int_insert(&a, i);
        for (int i = 0; i < 27; i++)
            uset_int_insert(&a, i);
        foreach (uset_int, &a, it)
        {
            j = *it.ref;
        }
        printf("last int %d, ", j);
        foreach (uset_int, &a, it)
        {
            uset_int_node_bucket_size(it.node);
        }
        printf("uset load_factor: %f\n", uset_int_load_factor(&a));
        uset_int_free(&a);
    }
    {
        umap_charpint a = umap_charpint_init(charpint_hash, charpint_equal);
        // TODO a.equal = charpint_equal
        char c_char[36];
        for (int i = 0; i < 1000; i++)
        {
            snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
            charpint copy = charpint_copy(&(charpint){c_char, i});
            // str s = (str){.value = c_char};
            umap_charpint_insert(&a, copy);
        }
        foreach (umap_charpint, &a, it)
        {
            strcpy(c_char, it.ref->key);
        }
        printf("last key \"%s\", ", c_char);
        foreach (umap_charpint, &a, it)
        {
            umap_charpint_node_bucket_size(it.node);
        }
        printf("umap_charpint load_factor: %f\n", umap_charpint_load_factor(&a));
        umap_charpint_free(&a);
    }
#endif
    {
        map_charpint a = map_charpint_init(charpint_cmp);
        char c_char[36];
        for (int i = 0; i < 1000; i++)
        {
            snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
            // str s = (str){.value = c_char};
            map_charpint_insert(&a, charpint_copy(&(charpint){c_char, i}));
        }
        foreach (map_charpint, &a, it)
        {
            strcpy(c_char, it.ref->key);
        }
        printf("last key \"%s\", ", c_char);
        map_charpint_it it = map_charpint_begin(&a);
        printf("min {\"%s\", %d} ", it.ref->key, it.ref->value);
        map_charpint_node *b = map_charpint_node_max(it.node);
        printf("max {\"%s\", %d}\n", b->value.key, b->value.value);
        map_charpint_free(&a);
    }
    TEST_PASS(__FILE__);
}
