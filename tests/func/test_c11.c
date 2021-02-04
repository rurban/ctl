#include "../test.h"

#include <ctl/string.h> // MULTIPLE INCLUDES OKAY.
#include <ctl/string.h>
#include <ctl/string.h>
#include <ctl/string.h>

#define POD
#define T int
#include <ctl/unordered_set.h>

size_t
int_hash(int* x)
{ return abs(*x); }

int
int_equal(int* a, int* b)
{ return *a == *b; }

size_t
FNV1a(const char *key)
{
  size_t h;
  h = 2166136261u;
  for (unsigned i = 0; i < strlen(key); i++) {
    h ^= (unsigned char)key[i];
    h *= 16777619;
  }
  return h;
}

/* TODO: make that simpler as with STL pairs, treating them seperately */
typedef struct {
  char *key;
  int value;
} charint;

static inline size_t
charint_hash(charint *a) {
  return FNV1a(a->key);
}
static inline int
charint_equal(charint *a, charint *b) {
  return strcmp(a->key, b->key) == 0;
}
static inline int
charint_cmp(charint *a, charint *b) {
  return strcmp(a->key, b->key);
}
static inline void
charint_free(charint *a) {
  free(a->key);
}
static inline charint
charint_copy(charint *self) {
  char *copy_key = (char*) malloc(strlen(self->key) + 1);
  strcpy (copy_key, self->key);
  charint copy = {
    copy_key,
    self->value,
  };
  return copy;
}

#undef POD
#define T charint
#include <ctl/unordered_map.h>

#undef POD
#define T charint
#include <ctl/map.h>

size_t
_str_hash(str* s)
{ return FNV1a(*(const char **)s); }

int
_str_equal(str* a, str* b)
{ return strcmp(*(char**)a, *(char**)b) == 0; }

int
_str_cmp(str* a, str* b)
{ return strcmp(*(char**)a, *(char**)b); }

#define T str
#include <ctl/set.h>

// we known about this special case
#define POD
#define NOT_INTEGRAL
typedef char* charp;
#define T charp
#include <ctl/set.h>

#define POD
#define T int
#include <ctl/stack.h>

#define POD
#define T int
#include <ctl/priority_queue.h>

#define POD
#define T int
#include <ctl/queue.h>

#define POD
#define T int
#include <ctl/list.h>

#define POD
#define T int
#include <ctl/deque.h>

#define POD
#define T int
#include <ctl/set.h>

#define POD
#define T char
#include <ctl/vector.h>

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

typedef struct
{
    int x;
    int y;
} point;

#define POD
#define NOT_INTEGRAL
#define T point
#include <ctl/vector.h>

#define T str
#include <ctl/vector.h>

typedef struct
{
    vec_point path;
    str name;
} person;

static person
person_init(size_t path_capacity, const char* first, const char* last)
{
    person self;
    self.path = vec_point_init();
    self.name = str_init(first);
    str_append(&self.name, " ");
    str_append(&self.name, last);
    vec_point_reserve(&self.path, path_capacity);
    return self;
}

static void
person_free(person* self)
{
    vec_point_free(&self->path);
    str_free(&self->name);
}

static person
person_copy(person* self)
{
    person copy = {
        vec_point_copy(&self->path),
        str_copy(&self->name),
    };
    return copy;
}

#define T person
#include <ctl/vector.h>

int
main(void)
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
        for(size_t i = 0; i < size; i++) deq_int_push_back(&a, i);
        for(size_t i = 0; i < size; i++) deq_int_push_front(&a, i);
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
        for (int i=0; i > -27; i--)
          uset_int_insert(&a, i);
        for (int i=0; i < 27; i++)
          uset_int_insert(&a, i);
        foreach(uset_int, &a, it) { j = *it.ref; }
        printf("last int %d, ", j);
        foreach(uset_int, &a, it) { uset_int_node_bucket_size(it.node); }
        printf("uset load_factor: %f\n", uset_int_load_factor(&a));
        uset_int_free(&a);
    }
    {
        umap_charint a = umap_charint_init(charint_hash, charint_equal);
        // TODO a.equal = charint_equal
        char c_char[36];
        for (int i=0; i<1000; i++) {
          snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
          charint copy = charint_copy(&(charint){ c_char, i });
          //str s = (str){.value = c_char};
          umap_charint_insert(&a, copy);
        }
        foreach(umap_charint, &a, it) { strcpy (c_char, it.ref->key); }
        printf("last key \"%s\", ", c_char);
        foreach(umap_charint, &a, it) { umap_charint_node_bucket_size(it.node); }
        printf("umap_charint load_factor: %f\n", umap_charint_load_factor(&a));
        umap_charint_free(&a);
    }
#endif
    {
        map_charint a = map_charint_init(charint_cmp);
        char c_char[36];
        for (int i=0; i<1000; i++) {
          snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
          //str s = (str){.value = c_char};
          map_charint_insert(&a, charint_copy(&(charint){ c_char, i }));
        }
        foreach(map_charint, &a, it) { strcpy (c_char, it.ref->key); }
        printf("last key \"%s\", ", c_char);
        map_charint_it it = map_charint_begin(&a);
        printf("min {\"%s\", %d} ", it.ref->key, it.ref->value);
        map_charint_node* b = map_charint_node_max(it.node);
        printf("max {\"%s\", %d}\n", b->value.key, b->value.value);
        map_charint_free(&a);
    }
    TEST_PASS(__FILE__);
}
