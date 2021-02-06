#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#define POD
#define T double
#define N 20
#include <ctl/array.h>

#include <array>
#include <algorithm>

int double_is_odd (double *d) {
    return ((long)*d) % 2;
}
int DOUBLE_is_odd (double d) {
    return ((long)d) % 2;
}

static double _generator_state = 0.0;
void double_generate_reset () {
    _generator_state = 0.0;
}
double double_generate (void) {
    _generator_state += 1.0;
    return  _generator_state;
}
double double_untrans (double* v) {
    return 2.0 * *v;
}
double DOUBLE_untrans (double& v) {
    return 2.0 * v;
}
double double_bintrans (double* v1, double* v2) {
    return *v1 * *v2;
}
double DOUBLE_bintrans (double& v1, double& v2) {
    return v1 * v2;
}

#define N 20

void print_arr20(arr20_double *a)
{
    foreach(arr20_double, a, it)
        printf ("%f ", *it.ref);
    printf ("\n");
}

void print_array(std::array<double,20> &b)
{
    for(auto& d: b)
        printf ("%f ", d);
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 1000
#else
#define print_arr20(x)
#define print_array(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(arr20_double* a)
{
    const size_t index = TEST_RAND(N);
    double *vp = arr20_double_at(a, index);
    return *vp;
}

#define CHECK(_x, _y) {                                           \
    assert(arr20_double_size(&_x) == _y.size());                  \
    assert(arr20_double_empty(&_x) == _y.empty());                \
    assert(_y.front() == *arr20_double_front(&_x));               \
    assert(_y.back() == *arr20_double_back(&_x));                 \
    std::array<double,20>::iterator _iter = _y.begin();           \
    foreach(arr20_double, &_x, _it) {                             \
        assert(*_it.ref == *_iter);                               \
        _iter++;                                                  \
    }                                                             \
    double* _ref = arr20_double_front(&_x);                       \
    for(auto& _d : _y) {                                          \
        assert(*_ref == _d);                                      \
        _ref++;                                                   \
    }                                                             \
    for(size_t _i = 0; _i < _y.size(); _i++)                      \
        assert(_y.at(_i) == *arr20_double_at(&_x, _i));           \
}

#define CHECK_ITER(_it, b, _iter)                                 \
    if (_it.ref && _it.ref != &_it.container->vector[N])          \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*_it.ref == *_iter);                               \
    } else                                                        \
        assert (_iter == b.end())

static void
get_random_iters (arr20_double *a, arr20_double_it *first_a, arr20_double_it *last_a,
                  std::array<double,20>& b, std::array<double,20>::iterator &first_b,
                  std::array<double,20>::iterator &last_b)
{
    size_t r1 = TEST_RAND(N / 2);
    const size_t rnd = TEST_RAND(N / 2);
    size_t r2 = MIN(r1 + rnd, N);
    LOG("iters %zu, %zu of %d\n", r1, r2, N);
    if (N)
    {
        arr20_double_it it1 = arr20_double_begin (a);
        first_b = b.begin();
        arr20_double_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == N)
        {
            *last_a = arr20_double_end(a);
            last_b = b.end();
        }
        else
        {
            arr20_double_it it2 = arr20_double_begin(a);
            arr20_double_it_advance(&it2, r2);
            *last_a = it2;
            last_b = b.begin();
            last_b += r2;
        }
        first_a->end = last_a->ref;
    }
    else
    {
        arr20_double_it end = arr20_double_end (a);
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
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        arr20_double a = arr20_double_init();
        std::array<double,20> b;
        for (int i=0; i<N; i++)
        {
            double value = rand() * 1.0;
            b[i] = value;
            a.vector[i] = value;
        }

#define FOREACH_METH(TEST) \
        TEST(SELF) \
        TEST(FILL) \
        TEST(FILL_N) \
        TEST(SORT) \
        TEST(COPY) \
        TEST(SWAP) \
        TEST(ASSIGN) \
        TEST(EQUAL) \
        TEST(CLEAR) \
        TEST(FIND) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(COUNT) \
        TEST(COUNT_IF) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(GENERATE) \
        TEST(GENERATE_RANGE) \
        TEST(TRANSFORM) \

#define FOREACH_DEBUG(TEST) \
        TEST(EQUAL_RANGE) \
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
                    double value = rand() * 1.0;
                    b[i] = value;
                    *arr20_double_at(&a, i) = value;
                }
                break;
            }
            case TEST_CLEAR:
            {
                b.fill(double{0});
                arr20_double_clear(&a);
                break;
            }
            case TEST_FILL:
            {
                const double value = rand() * 1.0;
                b.fill(value);
                arr20_double_fill(&a, value);
                break;
            }
            case TEST_FILL_N:
            {
                const int n = TEST_RAND(N);
                const int value = TEST_RAND(TEST_MAX_VALUE);
                std::fill_n(b.begin(), n, value);
                arr20_double_fill_n(&a, n, value);
                break;
            }
            case TEST_SORT:
            {
                arr20_double_sort(&a);
                std::sort(b.begin(), b.end());
                break;
            }
            case TEST_COPY:
            {
                arr20_double aa = arr20_double_copy(&a);
                std::array<double,20> bb = b;
                CHECK(aa, bb);
                arr20_double_free(&aa);
                break;
            }
            case TEST_ASSIGN:
            {
                const double value = rand() * 1.0;
                size_t assign_size = TEST_RAND(N - 1);
                arr20_double_assign(&a, assign_size, value);
                for (size_t i=0; i<assign_size; i++)
                    b[i] = value;
                break;
            }
            case TEST_SWAP:
            {
                arr20_double aa = arr20_double_copy(&a);
                arr20_double aaa = arr20_double_init();
                std::array<double,20> bb = b;
                std::array<double,20> bbb;
                arr20_double_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                arr20_double_free(&aaa);
                arr20_double_free(&aa);
                break;
            }
            case TEST_EQUAL:
            {
                arr20_double aa = arr20_double_copy(&a);
                std::array<double,20> bb = b;
                assert(arr20_double_equal(&a, &aa));
                assert(b == bb);
                arr20_double_free(&aa);
                break;
            }
            case TEST_FIND:
            {
                const size_t index = TEST_RAND(N);
                int value = TEST_RAND(2) ? rand() * 1.0
                    : *arr20_double_at(&a, index);
                double key = value;
                double* aa = arr20_double_find(&a, key);
                auto bb = std::find(b.begin(), b.end(), value);
                bool found_a = aa != NULL;
                bool found_b = bb != b.end();
                assert(found_a == found_b);
                if(found_a && found_b)
                    assert(*aa == *bb);
                break;
            }
            case TEST_GENERATE:
            {
                double_generate_reset();
                arr20_double_generate(&a, double_generate);
                double_generate_reset();
                std::generate(b.begin(), b.end(), double_generate);
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF:
            {
                arr20_double_it aa = arr20_double_find_if(&a, double_is_odd);
                auto bb = std::find_if(b.begin(), b.end(), DOUBLE_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                arr20_double_it aa = arr20_double_find_if_not(&a, double_is_odd);
                auto bb = std::find_if_not(b.begin(), b.end(), DOUBLE_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_ALL_OF:
            {
                bool is_a = arr20_double_all_of(&a, double_is_odd);
                bool is_b = std::all_of(b.begin(), b.end(), DOUBLE_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_ANY_OF:
            {
                bool is_a = arr20_double_any_of(&a, double_is_odd);
                bool is_b = std::any_of(b.begin(), b.end(), DOUBLE_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = arr20_double_none_of(&a, double_is_odd);
                bool is_b = std::none_of(b.begin(), b.end(), DOUBLE_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_COUNT:
            {
                double v = TEST_RAND(2) ? rand() * 1.0 : 0.0;
                int aa = arr20_double_count(&a, v);
                int bb = std::count(b.begin(), b.end(), v);
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF:
            {
                size_t count_a = arr20_double_count_if(&a, double_is_odd);
                size_t count_b = std::count_if(b.begin(), b.end(), DOUBLE_is_odd);
                assert(count_a == count_b);
                break;
            }
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? rand() * 1.0 : random_element(&a);
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr20_double_it i = arr20_double_find_range(&first_a, &last_a, vb);
                auto it = std::find(first_b, last_b, vb);
                CHECK_ITER(i, b, it);
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr20_double_it i = arr20_double_find_if_range(&first_a, &last_a, double_is_odd);
                auto it = std::find_if(first_b, last_b, DOUBLE_is_odd);
                print_arr20(&a);
                print_array(b);
                CHECK_ITER(i, b, it);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr20_double_it i = arr20_double_find_if_not_range(&first_a, &last_a,
                                                                         double_is_odd);
                auto it = std::find_if_not(first_b, last_b, DOUBLE_is_odd);
                CHECK_ITER(i, b, it);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr20_double_all_of_range(&first_a, &last_a,
                                                       double_is_odd);
                bool bb = std::all_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr20(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr20_double_none_of_range(&first_a, &last_a,
                                                        double_is_odd);
                bool bb = std::none_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr20(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = arr20_double_count_if_range(&first_a, &last_a,
                                                         double_is_odd);
                size_t numb = std::count_if(first_b, last_b, DOUBLE_is_odd);
                if (numa != numb)
                {
                    print_arr20(&a);
                    print_array(b);
                    printf ("%d != %d FAIL\n", (int)numa, (int)numb);
                    fail++;
                }
                assert(numa == numb); //fails. off by one, counts one too much
                break;
            }
            case TEST_COUNT_RANGE:
            {
                double v = TEST_RAND(2) ? rand() * 1.0 : 0.0;
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                // used to fail with 0,0 of 0
                size_t numa = arr20_double_count_range(&first_a, &last_a, v);
                size_t numb = std::count(first_b, last_b, double{v});
                assert(numa == numb);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr20_double_any_of_range(&first_a, &last_a,
                                                       double_is_odd);
                bool bb = std::any_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr20(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_TRANSFORM:
            {
                arr20_double aa = arr20_double_transform(&a, double_untrans);
                std::array<double,20> bb;
                std::transform(b.begin(), b.end(), bb.begin(), DOUBLE_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                arr20_double_free(&aa);
                break;
            }
            case TEST_GENERATE_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                double_generate_reset();
                arr20_double_generate_range(&first_a, &last_a, double_generate);
                double_generate_reset();
                std::generate(first_b, last_b, double_generate);
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_EQUAL_RANGE:
            case TEST_INTERSECTION:
            case TEST_DIFFERENCE:
                printf("nyi\n");
                break;
            case TEST_GENERATE_N:
            {
                size_t count = TEST_RAND(20);
                double_generate_reset();
                arr20_double_generate_n(&a, count, double_generate);
                double_generate_reset();
                std::generate_n(b.begin(), count, double_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_N_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t off = first_b - b.begin();
                size_t count = TEST_RAND(20 - off);
                double_generate_reset();
                arr20_double_generate_n_range(&first_a, count, double_generate);
                double_generate_reset();
                std::generate_n(first_b, count, double_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM_IT:
            {
                arr20_double_it pos = arr20_double_begin(&a);
                arr20_double_it_advance(&pos, 1);
                arr20_double aa = arr20_double_transform_it(&a, &pos, double_bintrans);
                std::array<double,20> bb;
                std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), DOUBLE_bintrans);
                CHECK(aa, bb);
                CHECK(a, b);
                arr20_double_free(&aa);
                break;
            }
            case TEST_TRANSFORM_RANGE:
            {
                arr20_double_it first_a, last_a;
                std::array<double,20>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                arr20_double aa = arr20_double_init();
                arr20_double_it dest = arr20_double_begin(&aa);
                arr20_double_it it = arr20_double_transform_range(&first_a, &last_a, dest, double_untrans);
                std::array<double,20> bb;
                auto iter = std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), DOUBLE_bintrans);
                CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                CHECK(a, b);
                arr20_double_free(&aa);
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
        arr20_double_free(&a);
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
