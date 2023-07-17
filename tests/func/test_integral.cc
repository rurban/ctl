/* See if all known integral types can use default compare, equal methods */
#include "../test.h"

#define POD
#define T int
#include <ctl/deque.h>

#define POD
#define T long
#include <ctl/list.h>

#define POD
#define T short
#include <ctl/list.h>

#define POD
#define T bool
#include <ctl/vector.h> // but no vector_bool specialization yet

#define POD
#define T char
#include <ctl/list.h>

#define POD
typedef unsigned char unsigned_char;
#define T unsigned_char
#include <ctl/list.h>

#define POD
#define T uint8_t
#include <ctl/stack.h>

#include "charpint.hh"

typedef char *charp;
#define TK charp
#define T int
#define POD
#include <ctl/map.h>

#define POD
#define T double
#include <ctl/vector.h>

// TODO check feature and include the header. see u8string
//#define POD
//#define T char8_t
//#include <ctl/vector.h>

#define POD
typedef long double long_double;
#define T long_double
#include <ctl/vector.h>

#define POD
typedef long double ldbl;
#define T ldbl
#include <ctl/vector.h>

#define POD
typedef long long long_long;
#define T long_long
#include <ctl/vector.h>

#define POD
typedef long long llong;
#define T llong
#include <ctl/vector.h>

#define POD
typedef unsigned long ulong;
#define T ulong
#include <ctl/vector.h>

#define POD
#define T uint8_t
#include <ctl/vector.h>

#define POD
#define T int32_t
#include <ctl/vector.h>

#define POD
#define T int8_t
#include <ctl/vector.h>

#define POD
#define T uint8_t
#include <ctl/deque.h>

#define POD
#define T long
#include <ctl/unordered_set.h>

#define POD
#define N 128
#define T int
#include <ctl/array.h>

#ifdef DEBUG
void print_deq_int(deq_int *a)
{
    for (size_t i = 0; i < a->size; i++)
        printf("%zu: %d\n", i, *deq_int_at(a, i));
    printf("\n");
}
#endif

int main(void)
{
#define TEST_LIST(type, v1, v2)                                                 \
    {                                                                           \
        type a = type##_init();                                                 \
        type##_push_back(&a, v1);                                               \
        type##_it found = type##_find(&a, v1);                                  \
        assert(!type##_it_done(&found)); /* equal */                            \
        type##_push_back(&a, v2);                                               \
        type b = type##_copy(&a);                                               \
        type##_sort(&a); /* compare */                                          \
        assert(type##_equal(&a, &b));                                           \
        type##_free(&a);                                                        \
        type##_free(&b);                                                        \
    }

    TEST_LIST(deq_int, 1, 2);
    TEST_LIST(list_long, 1L, 2L);
    TEST_LIST(list_short, 1, 2);
    // TEST_LIST(vec_bool, true, false);
    TEST_LIST(list_char, 1, 2);
    TEST_LIST(list_unsigned_char, 1, 2);

    {
        stack_uint8_t a = stack_uint8_t_init();
        stack_uint8_t_push(&a, 1);
        stack_uint8_t_it found = stack_uint8_t_find(&a, 1);
        assert(!stack_uint8_t_it_done(&found)); /* equal */
        stack_uint8_t_free(&a);
    }
    {
        map_charpint a = map_charpint_init(NULL);
        map_charpint_insert(&a, 1.f); // compare
        map_charpint_it found = map_charpint_find(&a, 1.f);
        assert(!map_charpint_it_done(&found)); // equal
        map_charpint_free(&a);
    }
    TEST_LIST(vec_double, 1.0, 2.0);
    {
        uset_long a = uset_long_init(NULL, NULL);
        uset_long_insert(&a, 1L);                    // hash
        uset_long_it found = uset_long_find(&a, 1L); // equal
        assert(!uset_long_it_done(&found));          // equal
        uset_long_free(&a);
    }
    {
        arr128_int a = arr128_int_init();
        for (int i = 0; i < 127; i++)
            arr128_int_set(&a, i, rand() % INT_MAX);
        arr128_int_set(&a, 127, 1);
        assert(arr128_int_find(&a, 1)); /* equal */
        arr128_int b = arr128_int_copy(&a);
        arr128_int_sort(&b); /* compare */
        arr128_int_sort(&a);
        assert(arr128_int_equal(&a, &b));
        arr128_int_free(&b);
        arr128_int_free(&a);
    }
    TEST_PASS(__FILE__);
}
