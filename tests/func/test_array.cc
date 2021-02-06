#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define N 100
#include <ctl/array.h>

#include <array>
#include <algorithm>

#define N 100

void print_arr100(arr100_digi *a)
{
    foreach(arr100_digi, a, it)
        printf ("%d ", *it.ref->value);
    printf ("\n");
}

void print_array(std::array<DIGI,100> &b)
{
    for(auto& d: b)
        printf ("%d ", *d.value);
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 1000
#else
#define print_arr100(x)
#define print_array(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(arr100_digi* a)
{
    const size_t index = TEST_RAND(N);
    digi *vp = arr100_digi_at(a, index);
    return *vp->value;
}

#define CHECK(_x, _y) {                                           \
    assert(arr100_digi_size(&_x) == _y.size());                   \
    assert(arr100_digi_empty(&_x) == _y.empty());                 \
    assert(*_y.front().value == *arr100_digi_front(&_x)->value);  \
    assert(*_y.back().value == *arr100_digi_back(&_x)->value);    \
    std::array<DIGI,100>::iterator _iter = _y.begin();            \
    foreach(arr100_digi, &_x, _it) {                              \
        assert(*_it.ref->value == *_iter->value);                 \
        _iter++;                                                  \
    }                                                             \
    digi* _ref = arr100_digi_front(&_x);                          \
    for(auto& _d : _y) {                                          \
        assert(*(_ref->value) == *_d.value);                      \
        _ref++;                                                   \
    }                                                             \
    for(size_t _i = 0; _i < _y.size(); _i++)                      \
        assert(*_y.at(_i).value == *arr100_digi_at(&_x, _i)->value);\
}

#define CHECK_ITER(_it, b, _iter)                                 \
    if (_it.ref && _it.ref != &_it.container->vector[N])          \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*(_it.ref->value) == *(*_iter).value);             \
    } else                                                        \
        assert (_iter == b.end())

#define CHECK_REF(_ref, b, _iter)                                 \
    if (_iter != b.end())                                         \
        assert(*(_ref->value) == *(*_iter).value)

static void
get_random_iters (arr100_digi *a, arr100_digi_it *first_a, arr100_digi_it *last_a,
                  std::array<DIGI,100>& b, std::array<DIGI,100>::iterator &first_b,
                  std::array<DIGI,100>::iterator &last_b)
{
    size_t r1 = TEST_RAND(N / 2);
    const size_t rnd = TEST_RAND(N / 2);
    size_t r2 = MIN(r1 + rnd, N);
    LOG("iters %zu, %zu of %d\n", r1, r2, N);
    if (N)
    {
        arr100_digi_it it1 = arr100_digi_begin (a);
        first_b = b.begin();
        arr100_digi_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == N)
        {
            *last_a = arr100_digi_end(a);
            last_b = b.end();
        }
        else
        {
            arr100_digi_it it2 = arr100_digi_begin(a);
            arr100_digi_it_advance(&it2, r2);
            *last_a = it2;
            last_b = b.begin();
            last_b += r2;
        }
        first_a->end = last_a->ref;
    }
    else
    {
        arr100_digi_it end = arr100_digi_end (a);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
}

int
main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(15);

    arr100_digi a = arr100_digi_init();
    a.compare = digi_compare;
    a.equal = digi_equal;
    std::array<DIGI,100> b;
    for (int i=0; i<N; i++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE);
        b[i] = DIGI{value};
        a.vector[i] = digi_init(value);
    }

    for(size_t loop = 0; loop < loops; loop++)
    {

#define FOREACH_METH(TEST) \
        TEST(SELF) \
        TEST(FILL) \
        TEST(FILL_N) \
        TEST(SORT) \
        TEST(COPY) \
        TEST(SWAP) \
        TEST(ASSIGN) \
        TEST(EQUAL) \
        TEST(FIND) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(COUNT) \
        TEST(COUNT_IF) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE) \
        TEST(GENERATE) \
        TEST(GENERATE_RANGE) \
        TEST(TRANSFORM) \

#define FOREACH_DEBUG(TEST) \
        TEST(EQUAL_RANGE) \
        TEST(FIND_END) \
        TEST(FIND_END_IF) \
        TEST(FIND_END_RANGE) \
        TEST(FIND_END_IF_RANGE) \
        TEST(LOWER_BOUND) \
        TEST(UPPER_BOUND) \
        TEST(LOWER_BOUND_RANGE) \
        TEST(UPPER_BOUND_RANGE) \
        TEST(UNION) \
        TEST(DIFFERENCE) \
        TEST(SYMETRIC_DIFFERENCE) \
        TEST(INTERSECTION) \
        TEST(GENERATE_N) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM_IT) \
        TEST(TRANSFORM_RANGE) \

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

        enum {
            FOREACH_METH(GENERATE_ENUM)
#ifdef DEBUG
            FOREACH_DEBUG(GENERATE_ENUM)
#endif
            TEST_TOTAL
        };
#ifdef DEBUG
        static const char *test_names[] = {
            FOREACH_METH(GENERATE_NAME)
            FOREACH_DEBUG(GENERATE_NAME)
            ""
        };
#endif
        int which = TEST_RAND(TEST_TOTAL);
        if (test >= 0 && test < (int)TEST_TOTAL)
            which = test;
        LOG ("TEST=%d %s\n", which, test_names[which]);
        switch(which)
        {
            case TEST_SELF:
            {
                for (int i=0; i<N; i++)
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    b[i] = DIGI{value};
                    arr100_digi_set(&a, i, digi_init(value));
                }
                break;
            }
#if 0       // invalid for non-POD's
            case TEST_CLEAR:
            {
                b.fill(DIGI{0});
                arr100_digi_clear(&a);
                break;
            }
#endif
            case TEST_FILL:
            {
                const int value = TEST_RAND(TEST_MAX_VALUE);
                b.fill(DIGI{value});
                arr100_digi_fill(&a, digi_init(value));
                break;
            }
            case TEST_FILL_N:
            {
                const int n = TEST_RAND(N);
                const int value = TEST_RAND(TEST_MAX_VALUE);
                std::fill_n(b.begin(), n, DIGI{value});
                arr100_digi_fill_n(&a, n, digi_init(value));
                break;
            }
            case TEST_SORT:
            {
                arr100_digi_sort(&a);
                std::sort(b.begin(), b.end());
                break;
            }
            case TEST_COPY:
            {
                arr100_digi aa = arr100_digi_copy(&a);
                std::array<DIGI,100> bb = b;
                CHECK(aa, bb);
                arr100_digi_free(&aa);
                break;
            }
            case TEST_ASSIGN:
            {
                const int value = TEST_RAND(TEST_MAX_VALUE);
                size_t assign_size = TEST_RAND(N - 1);
                arr100_digi_assign(&a, assign_size, digi_init(value));
                for (size_t i=0; i<assign_size; i++)
                    b[i] = DIGI{value};
                break;
            }
            case TEST_SWAP:
            {
                arr100_digi aa = arr100_digi_copy(&a);
                arr100_digi aaa = arr100_digi_init();
                std::array<DIGI,100> bb = b;
                std::array<DIGI,100> bbb;
                arr100_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                arr100_digi_free(&aaa);
                break;
            }
            case TEST_EQUAL:
            {
                arr100_digi aa = arr100_digi_copy(&a);
                std::array<DIGI,100> bb = b;
                assert(arr100_digi_equal(&a, &aa));
                assert(b == bb);
                arr100_digi_free(&aa);
                break;
            }
            case TEST_FIND:
            {
                const size_t index = TEST_RAND(N);
                int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                    : *arr100_digi_at(&a, index)->value;
                digi key = digi_init(value);
                digi* aa = arr100_digi_find(&a, key);
                auto bb = std::find(b.begin(), b.end(), DIGI{value});
                bool found_a = aa != NULL;
                bool found_b = bb != b.end();
                assert(found_a == found_b);
                if(found_a && found_b)
                    assert(*aa->value == *bb->value);
                digi_free(&key);
                break;
            }
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : random_element(&a);
                digi key = digi_init(vb);
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr100_digi_it i = arr100_digi_find_range(&first_a, &last_a, key);
                auto it = std::find(first_b, last_b, vb);
                LOG("%d at [%ld]\n", *i.ref->value, i.ref - a.vector);
                CHECK_ITER(i, b, it); // broken
                digi_free (&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr100_digi_it i = arr100_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                auto it = std::find_if(first_b, last_b, DIGI_is_odd);
                print_arr100(&a);
                print_array(b);
                LOG("%d at [%ld]\n", *i.ref->value, i.ref - a.vector);
                CHECK_ITER(i, b, it);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr100_digi_it i = arr100_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto it = std::find_if_not(first_b, last_b, DIGI_is_odd);
                LOG("%d at [%ld]\n", *i.ref->value, i.ref - a.vector);
                CHECK_ITER(i, b, it);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr100_digi_all_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = std::all_of(first_b, last_b, DIGI_is_odd);
                /*if (aa != bb)
                {
                    print_arr100(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }*/
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr100_digi_none_of_range(&first_a, &last_a,
                                                    digi_is_odd);
                bool bb = std::none_of(first_b, last_b, DIGI_is_odd);
                if (aa != bb)
                {
                    print_arr100(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = arr100_digi_count_if_range(&first_a, &last_a,
                                                         digi_is_odd);
                size_t numb = std::count_if(first_b, last_b, DIGI_is_odd);
                if (numa != numb)
                {
                    print_arr100(&a);
                    print_array(b);
                    printf ("%d != %d FAIL\n", (int)numa, (int)numb);
                    fail++;
                }
                assert(numa == numb); //fails. off by one, counts one too much
                break;
            }
            case TEST_COUNT_RANGE:
            {
                int test_value = 0;
                int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                    : test_value;
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                // used to fail with 0,0 of 0
                size_t numa = arr100_digi_count_range(&first_a, &last_a, digi_init(v));
                size_t numb = std::count(first_b, last_b, DIGI{v});
                assert(numa == numb);
                break;
            }
            case TEST_ANY_OF:
            {
                bool is_a = arr100_digi_any_of(&a, digi_is_odd);
                bool is_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr100_digi_any_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = std::any_of(first_b, last_b, DIGI_is_odd);
                if (aa != bb)
                {
                    print_arr100(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_FIND_IF:
            {
                arr100_digi_it aa = arr100_digi_find_if(&a, digi_is_odd);
                auto bb = std::find_if(b.begin(), b.end(), DIGI_is_odd);
                if(bb == b.end())
                    assert(arr100_digi_it_done(&aa));
                else
                    assert(*(aa.ref->value) == *bb->value);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                arr100_digi_it aa = arr100_digi_find_if_not(&a, digi_is_odd);
                auto bb = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
                if(bb == b.end())
                    assert(arr100_digi_it_done(&aa));
                else
                    assert(*(aa.ref->value) == *bb->value);
                break;
            }
            case TEST_ALL_OF:
            {
                bool is_a = arr100_digi_all_of(&a, digi_is_odd);
                bool is_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = arr100_digi_none_of(&a, digi_is_odd);
                bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_COUNT:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = arr100_digi_count(&a, digi_init(key));
                int bb = std::count(b.begin(), b.end(), DIGI{key});
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF:
            {
                size_t count_a = arr100_digi_count_if(&a, digi_is_odd);
                size_t count_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
                assert(count_a == count_b);
                break;
            }
            case TEST_GENERATE:
            {
                digi_generate_reset();
                arr100_digi_generate(&a, digi_generate);
                digi_generate_reset();
                std::generate(b.begin(), b.end(), DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                digi_generate_reset();
                arr100_digi_generate_range(&first_a, &last_a, digi_generate);
                digi_generate_reset();
                std::generate(first_b, last_b, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM:
            {
                arr100_digi aa = arr100_digi_transform(&a, digi_untrans);
                std::array<DIGI,100> bb;
                std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                arr100_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_EQUAL_RANGE:
            case TEST_INTERSECTION:
            case TEST_DIFFERENCE:
                printf("nyi\n");
                break;
            case TEST_GENERATE_N: // TEST=40
            {
                size_t count = TEST_RAND(20);
                digi_generate_reset();
                arr100_digi_generate_n(&a, count, digi_generate);
                digi_generate_reset();
                std::generate_n(b.begin(), count, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_N_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t off = first_b - b.begin();
                size_t count = TEST_RAND(20 - off);
                digi_generate_reset();
                arr100_digi_generate_n_range(&first_a, count, digi_generate);
                digi_generate_reset();
                std::generate_n(first_b, count, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM_IT:
            {
                arr100_digi_it pos = arr100_digi_begin(&a);
                arr100_digi_it_advance(&pos, 1);
                arr100_digi aa = arr100_digi_transform_it(&a, &pos, digi_bintrans);
                std::array<DIGI,100> bb;
                std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), DIGI_bintrans);
                CHECK(aa, bb);
                CHECK(a, b);
                arr100_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_RANGE:
            {
                arr100_digi_it first_a, last_a;
                std::array<DIGI,100>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr100_digi aa = arr100_digi_init();
                arr100_digi_it dest = arr100_digi_begin(&aa);
                arr100_digi_it it = arr100_digi_transform_range(&first_a, &last_a, dest, digi_untrans);
                std::array<DIGI,100> bb;
                auto iter = std::transform(first_b, last_b, b.begin()+1, bb.begin(), DIGI_bintrans);
                CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                // heap use-after-free
                CHECK(a, b);
                arr100_digi_free(&aa);
                break;
            }
#endif
            default:
#ifdef DEBUG
                printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
                printf("unhandled testcase %d\n", which);
#endif
                break;
        }
        CHECK(a, b);
    }
    arr100_digi_free(&a);

    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
