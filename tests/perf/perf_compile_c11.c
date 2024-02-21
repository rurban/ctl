#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/deque.h>

#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/list.h>

#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/forward_list.h>

#define POD
#define T int
#include <ctl/queue.h>

#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/set.h>

#define POD
#define T int
#include <ctl/stack.h>

#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/vector.h>

#define POD
#define T int
#include <ctl/priority_queue.h>

#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/string.h>

#define POD
#define T int
#define N 1024
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/array.h>

static inline size_t int_hash(int *a) { return (size_t)ctl_int32_hash((uint32_t)*a); }
#define POD
#define T int
#ifdef ALGORITHM
#define INCLUDE_ALGORITHM
#endif
#include <ctl/unordered_set.h>

#define POD
#define T short
#include <ctl/deque.h>

#define POD
#define T short
#include <ctl/list.h>

#define POD
#define T short
#include <ctl/forward_list.h>

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
#include <ctl/forward_list.h>

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
#include <ctl/forward_list.h>

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

static int compare_key_int(int *a, int *b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int compare_int(int *a, int *b)
{
    return *a < *b;
}

static int compare_key_short(short *a, short *b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int compare_short(short *a, short *b)
{
    return *a < *b;
}

static int compare_key_float(float *a, float *b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int compare_float(float *a, float *b)
{
    return *a < *b;
}

static int compare_key_double(double *a, double *b)
{
    return (*a == *b) ? 0 : (*a < *b) ? -1 : 1;
}

static int compare_double(double *a, double *b)
{
    return *a < *b;
}

#define N 1024

void A(void)
{
    deq_int a = deq_int_init();
    vec_int b = vec_int_init();
    list_int c = list_int_init();
    slist_int c1 = slist_int_init();
    queue_int d = queue_int_init();
    set_int e = set_int_init(compare_key_int);
    stack_int f = stack_int_init();
    str g = str_init("test");
    pqu_int i = pqu_int_init(compare_int);
    arr1024_int j = arr1024_int_init();
    uset_int k = uset_int_init();

    for (int el = 0; el < N; el++)
    {
        deq_int_push_back(&a, el);
        deq_int_push_front(&a, el);
        vec_int_push_back(&b, el);
        list_int_push_back(&c, el);
        list_int_push_front(&c, el);
        slist_int_push_front(&c1, el);
        queue_int_push(&d, el);
        set_int_insert(&e, el);
        stack_int_push(&f, el);
        pqu_int_push(&i, el);
        arr1024_int_set(&j, el, el);
        uset_int_insert(&k, el);
    }

    deq_int_pop_back(&a);
    deq_int_pop_front(&a);
    vec_int_pop_back(&b);
    list_int_pop_back(&c);
    list_int_pop_front(&c);
    slist_int_pop_front(&c1);
    queue_int_pop(&d);
    set_int_erase(&e, 1);
    stack_int_pop(&f);
    pqu_int_pop(&i);
    arr1024_int_set(&j, 0, 0);
    uset_int_erase(&k, 1);

    list_int_sort(&c);
    slist_int_sort(&c1);

#ifdef ALGORITHM
    deq_int_sort(&a);
    vec_int_sort(&b);
    deq_int_count(&a, 0);
    vec_int_count(&b, 0);
    list_int_count(&c, 0);
    slist_int_count(&c1, 0);
    set_int_count(&e, 0);
    str_sort(&g);
    str_count(&g, 'A');
    arr1024_int_sort(&j);
    arr1024_int_count(&j, 0);
    uset_int_count(&k, 0);
#endif

    deq_int_free(&a);
    vec_int_free(&b);
    list_int_free(&c);
    slist_int_free(&c1);
    queue_int_free(&d);
    set_int_free(&e);
    stack_int_free(&f);
    str_free(&g);
    pqu_int_free(&i);
    arr1024_int_free(&j);
    uset_int_free(&k);
}

void B(void)
{
    deq_short a = deq_short_init();
    vec_short b = vec_short_init();
    list_short c = list_short_init();
    slist_short c1 = slist_short_init();
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
    slist_short_push_front(&c1, 1);
    queue_short_push(&d, 1);
    set_short_insert(&e, 1);
    stack_short_push(&f, 1);
    pqu_short_push(&i, 1);

    deq_short_pop_back(&a);
    deq_short_pop_front(&a);
    vec_short_pop_back(&b);
    list_short_pop_back(&c);
    list_short_pop_front(&c);
    slist_short_pop_front(&c1);
    queue_short_pop(&d);
    set_short_erase(&e, 1);
    stack_short_pop(&f);
    pqu_short_pop(&i);

    deq_short_free(&a);
    vec_short_free(&b);
    list_short_free(&c);
    slist_short_free(&c1);
    queue_short_free(&d);
    set_short_free(&e);
    stack_short_free(&f);
    str_free(&g);
    pqu_short_free(&i);
}

void C(void)
{
    deq_float a = deq_float_init();
    vec_float b = vec_float_init();
    list_float c = list_float_init();
    slist_float c1 = slist_float_init();
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
    slist_float_push_front(&c1, 1.0);
    queue_float_push(&d, 1.0);
    set_float_insert(&e, 1.0);
    stack_float_push(&f, 1.0);
    pqu_float_push(&i, 1.0);

    deq_float_pop_back(&a);
    deq_float_pop_front(&a);
    vec_float_pop_back(&b);
    list_float_pop_back(&c);
    list_float_pop_front(&c);
    slist_float_pop_front(&c1);
    queue_float_pop(&d);
    set_float_erase(&e, 1.0);
    stack_float_pop(&f);
    pqu_float_pop(&i);

    deq_float_free(&a);
    vec_float_free(&b);
    list_float_free(&c);
    slist_float_free(&c1);
    queue_float_free(&d);
    set_float_free(&e);
    stack_float_free(&f);
    str_free(&g);
    pqu_float_free(&i);
}

void D(void)
{
    deq_double a = deq_double_init();
    vec_double b = vec_double_init();
    list_double c = list_double_init();
    slist_double c1 = slist_double_init();
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
    slist_double_push_front(&c1, 1.0);
    queue_double_push(&d, 1.0);
    set_double_insert(&e, 1.0);
    stack_double_push(&f, 1.0);
    pqu_double_push(&i, 1.0);

    deq_double_pop_back(&a);
    deq_double_pop_front(&a);
    vec_double_pop_back(&b);
    list_double_pop_back(&c);
    list_double_pop_front(&c);
    slist_double_pop_front(&c1);
    queue_double_pop(&d);
    set_double_erase(&e, 1.0);
    stack_double_pop(&f);
    pqu_double_pop(&i);

    deq_double_free(&a);
    vec_double_free(&b);
    list_double_free(&c);
    slist_double_free(&c1);
    queue_double_free(&d);
    set_double_free(&e);
    stack_double_free(&f);
    str_free(&g);
    pqu_double_free(&i);
}

int main(void)
{
    A();
    B();
    C();
    D();
}
