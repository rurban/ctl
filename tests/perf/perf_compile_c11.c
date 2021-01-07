#define POD
#define T int
#include <ctl/deque.h>

#define POD
#define T int
#include <ctl/list.h>

#define POD
#define T int
#include <ctl/queue.h>

#define POD
#define T int
#include <ctl/set.h>

#define POD
#define T int
#include <ctl/stack.h>

#define POD
#define T int
#include <ctl/vector.h>

#define POD
#define T int
#include <ctl/priority_queue.h>

#include <ctl/string.h>

#define POD
#define T short
#include <ctl/deque.h>

#define POD
#define T short
#include <ctl/list.h>

#define POD
#define T short
#include <ctl/queue.h>

#define POD
#define T short
#include <ctl/set.h>

#define POD
#define T short
#include <ctl/stack.h>

#define POD
#define T short
#include <ctl/vector.h>

#define POD
#define T short
#include <ctl/priority_queue.h>

#include <ctl/string.h>

#define POD
#define T float
#include <ctl/deque.h>

#define POD
#define T float
#include <ctl/list.h>

#define POD
#define T float
#include <ctl/queue.h>

#define POD
#define T float
#include <ctl/set.h>

#define POD
#define T float
#include <ctl/stack.h>

#define POD
#define T float
#include <ctl/vector.h>

#define POD
#define T float
#include <ctl/priority_queue.h>

#include <ctl/string.h>

#define POD
#define T double
#include <ctl/deque.h>

#define POD
#define T double
#include <ctl/list.h>

#define POD
#define T double
#include <ctl/queue.h>

#define POD
#define T double
#include <ctl/set.h>

#define POD
#define T double
#include <ctl/stack.h>

#define POD
#define T double
#include <ctl/vector.h>

#define POD
#define T double
#include <ctl/priority_queue.h>

#include <ctl/string.h>

static int
compare_key_int(int* a, int* b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int
compare_int(int* a, int* b)
{
    return *a < *b;
}

static int
compare_key_short(short* a, short* b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int
compare_short(short* a, short* b)
{
    return *a < *b;
}

static int
compare_key_float(float* a, float* b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int
compare_float(float* a, float* b)
{
    return *a < *b;
}

static int
compare_key_double(double* a, double* b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int
compare_double(double* a, double* b)
{
    return *a < *b;
}

void
A(void)
{
    deq_int a = deq_int_init();
    vec_int b = vec_int_init();
    list_int c = list_int_init();
    queue_int d = queue_int_init();
    set_int e = set_int_init(compare_key_int);
    stack_int f = stack_int_init();
    str g = str_init("test");
    pqu_int i = pqu_int_init(compare_int);

    deq_int_push_back(&a, 1);
    deq_int_push_front(&a, 1);
    vec_int_push_back(&b, 1);
    list_int_push_back(&c, 1);
    list_int_push_front(&c, 1);
    queue_int_push(&d, 1);
    set_int_insert(&e, 1);
    stack_int_push(&f, 1);
    pqu_int_push(&i, 1);

    deq_int_pop_back(&a);
    deq_int_pop_front(&a);
    vec_int_pop_back(&b);
    list_int_pop_back(&c);
    list_int_pop_front(&c);
    queue_int_pop(&d);
    set_int_erase(&e, 1);
    stack_int_pop(&f);
    pqu_int_pop(&i);

    deq_int_free(&a);
    list_int_free(&c);
    vec_int_free(&b);
    queue_int_free(&d);
    set_int_free(&e);
    stack_int_free(&f);
    str_free(&g);
    pqu_int_free(&i);
}

void
B(void)
{
    deq_short a = deq_short_init();
    vec_short b = vec_short_init();
    list_short c = list_short_init();
    queue_short d = queue_short_init();
    set_short e = set_short_init(compare_key_short);
    stack_short f = stack_short_init();
    str g = str_init("test");
    pqu_short i = pqu_short_init(compare_short);

    deq_short_push_back(&a, 1);
    deq_short_push_front(&a, 1);
    vec_short_push_back(&b, 1);
    list_short_push_back(&c, 1);
    list_short_push_front(&c, 1);
    queue_short_push(&d, 1);
    set_short_insert(&e, 1);
    stack_short_push(&f, 1);
    pqu_short_push(&i, 1);

    deq_short_pop_back(&a);
    deq_short_pop_front(&a);
    vec_short_pop_back(&b);
    list_short_pop_back(&c);
    list_short_pop_front(&c);
    queue_short_pop(&d);
    set_short_erase(&e, 1);
    stack_short_pop(&f);
    pqu_short_pop(&i);

    deq_short_free(&a);
    list_short_free(&c);
    vec_short_free(&b);
    queue_short_free(&d);
    set_short_free(&e);
    stack_short_free(&f);
    str_free(&g);
    pqu_short_free(&i);
}

void
C(void)
{
    deq_float a = deq_float_init();
    vec_float b = vec_float_init();
    list_float c = list_float_init();
   queue_float d = queue_float_init();
    set_float e = set_float_init(compare_key_float);
   stack_float f = stack_float_init();
    str g = str_init("test");
    pqu_float i = pqu_float_init(compare_float);

    deq_float_push_back(&a, 1.0);
    deq_float_push_front(&a, 1.0);
    vec_float_push_back(&b, 1.0);
    list_float_push_back(&c, 1.0);
    list_float_push_front(&c, 1.0);
    queue_float_push(&d, 1.0);
    set_float_insert(&e, 1.0);
    stack_float_push(&f, 1.0);
    pqu_float_push(&i, 1.0);

    deq_float_pop_back(&a);
    deq_float_pop_front(&a);
    vec_float_pop_back(&b);
    list_float_pop_back(&c);
    list_float_pop_front(&c);
    queue_float_pop(&d);
    set_float_erase(&e, 1.0);
    stack_float_pop(&f);
    pqu_float_pop(&i);

    deq_float_free(&a);
    list_float_free(&c);
    vec_float_free(&b);
    queue_float_free(&d);
    set_float_free(&e);
    stack_float_free(&f);
    str_free(&g);
    pqu_float_free(&i);
}

void
D(void)
{
    deq_double a = deq_double_init();
    vec_double b = vec_double_init();
    list_double c = list_double_init();
    queue_double d = queue_double_init();
    set_double e = set_double_init(compare_key_double);
    stack_double f = stack_double_init();
    str g = str_init("test");
    pqu_double i = pqu_double_init(compare_double);

    deq_double_push_back(&a, 1.0);
    deq_double_push_front(&a, 1.0);
    vec_double_push_back(&b, 1.0);
    list_double_push_back(&c, 1.0);
    list_double_push_front(&c, 1.0);
    queue_double_push(&d, 1.0);
    set_double_insert(&e, 1.0);
    stack_double_push(&f, 1.0);
    pqu_double_push(&i, 1.0);

    deq_double_pop_back(&a);
    deq_double_pop_front(&a);
    vec_double_pop_back(&b);
    list_double_pop_back(&c);
    list_double_pop_front(&c);
    queue_double_pop(&d);
    set_double_erase(&e, 1.0);
    stack_double_pop(&f);
    pqu_double_pop(&i);

    deq_double_free(&a);
    list_double_free(&c);
    vec_double_free(&b);
    queue_double_free(&d);
    set_double_free(&e);
    stack_double_free(&f);
    str_free(&g);
    pqu_double_free(&i);
}

int
main(void)
{
    A();
    B();
    C();
    D();
}
