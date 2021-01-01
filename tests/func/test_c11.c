#include "../test.h"

#include <ctl/string.h> // MULTIPLE INCLUDES OKAY.
#include <ctl/string.h>
#include <ctl/string.h>
#include <ctl/string.h>

#define POD
#define T int
#include <ctl/ust.h>

size_t
int_hash(int* x)
{ return abs(*x); }

int
int_equal(int* a, int* b)
{ return *a == *b; }

#define P
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

typedef struct
{
    int x;
    int y;
} point;

#define POD
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

static int
int_match(int* a, int* b)
{
    return *a == *b;
}

static int
int_compare(int* a, int* b)
{
    return *a < *b;
}

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
        deq_int_insert(&a, 1, 99);
        deq_int_sort(&a, int_compare);
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
        list_int_unique(&a, int_match);
        list_int_free(&a);
    }
    {
        ust_int a = ust_int_init(8, int_hash, int_equal);
        ust_int_insert(&a, -0);
        ust_int_insert(&a, -1);
        ust_int_insert(&a, -2);
        ust_int_insert(&a, -3);
        ust_int_insert(&a, -4);
        ust_int_insert(&a, -5);
        ust_int_insert(&a, -6);
        ust_int_insert(&a, -7);
        ust_int_insert(&a, -8);
        ust_int_insert(&a, -9);
        ust_int_insert(&a, -10);
        ust_int_insert(&a, -11);
        ust_int_insert(&a, -12);
        ust_int_insert(&a, -13);
        ust_int_insert(&a, -14);
        ust_int_insert(&a, -15);
        ust_int_insert(&a, -16);
        ust_int_insert(&a, -17);
        ust_int_insert(&a, -18);
        ust_int_insert(&a, -19);
        ust_int_insert(&a, -20);
        ust_int_insert(&a, -21);
        ust_int_insert(&a, -22);
        ust_int_insert(&a, -23);
        ust_int_insert(&a, -24);
        ust_int_insert(&a, -25);
        ust_int_insert(&a, -26);
        ust_int_insert(&a, -27);
        ust_int_insert(&a, 0);
        ust_int_insert(&a, 1);
        ust_int_insert(&a, 2);
        ust_int_insert(&a, 3);
        ust_int_insert(&a, 4);
        ust_int_insert(&a, 5);
        ust_int_insert(&a, 6);
        ust_int_insert(&a, 7);
        ust_int_insert(&a, 8);
        ust_int_insert(&a, 9);
        ust_int_insert(&a, 10);
        ust_int_insert(&a, 11);
        ust_int_insert(&a, 12);
        ust_int_insert(&a, 13);
        ust_int_insert(&a, 14);
        ust_int_insert(&a, 15);
        ust_int_insert(&a, 16);
        ust_int_insert(&a, 17);
        ust_int_insert(&a, 18);
        ust_int_insert(&a, 19);
        ust_int_insert(&a, 20);
        ust_int_insert(&a, 21);
        ust_int_insert(&a, 22);
        ust_int_insert(&a, 23);
        ust_int_insert(&a, 24);
        ust_int_insert(&a, 25);
        ust_int_insert(&a, 26);
        ust_int_insert(&a, 27);
        foreach(ust_int, &a, it) { printf("GOT %d\n", *it.ref); }
        foreach(ust_int, &a, it) { printf("SIZE %lu\n", ust_int_bucket_size(it.node)); }
        printf("%f\n", ust_int_load_factor(&a));
        ust_int_free(&a);
    }
    TEST_PASS(__FILE__);
}
