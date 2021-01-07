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

#define POD
#define T float
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

void print_deq_int(deq_int *a)
{
    for(size_t i = 0; i < a->size; i++)
        printf ("%zu: %d\n", i, *deq_int_at(a, i));
    printf ("\n");
}

int
main(void)
{
#define TEST_LIST(type, v1, v2) {             \
    type a = type##_init();                   \
    type##_push_back(&a, v1);                 \
    assert(type##_find(&a, v1)); /* equal */  \
    type##_push_back(&a, v2);                 \
    type b = type##_copy(&a);                 \
    type##_sort(&a);            /* compare */ \
    assert(type##_equal(&a, &b));             \
    type##_free(&a);                          \
    type##_free(&b);                          \
}
    
    TEST_LIST(deq_int, 1, 2);
    TEST_LIST(list_long, 1L, 2L);
    TEST_LIST(list_short, 1, 2);
    //TEST_LIST(vec_bool, true, false);
    TEST_LIST(list_char, 1, 2);
    TEST_LIST(list_unsigned_char, 1, 2);

    {
        stack_uint8_t a = stack_uint8_t_init();
        stack_uint8_t_push(&a, 1);
        assert(stack_uint8_t_find(&a, 1)); /* equal */
        stack_uint8_t_free(&a);
    }
    {
        map_float a = map_float_init(NULL);
        map_float_insert(&a, 1.f);       // compare
        assert(map_float_find(&a, 1.f)); // equal
        map_float_free(&a);
    }
    TEST_LIST(vec_double, 1.0, 2.0);
    {
        uset_long a = uset_long_init(NULL, NULL);
        uset_long_insert(&a, 1L);       // hash
        assert(uset_long_find(&a, 1L)); // equal
        uset_long_free(&a);
    }
    TEST_PASS(__FILE__);
}
