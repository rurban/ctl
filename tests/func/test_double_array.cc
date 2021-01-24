#include "../test.h"

#define POD
#define T double
#define N 10000
#include <ctl/array.h>

#include <array>
#include <algorithm>

int double_is_odd (double *d) {
    return ((long)*d) % 2;
}
int DOUBLE_is_odd (double d) {
    return ((long)d) % 2;
}

#define N 10000

void print_arr10000(arr10000_double *a)
{
    foreach(arr10000_double, a, it)
        printf ("%f ", *it.ref);
    printf ("\n");
}

void print_array(std::array<double,10000> &b)
{
    for(auto& d: b)
        printf ("%f ", d);
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 1000
#else
#define print_arr10000(x)
#define print_array(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(arr10000_double* a)
{
    const size_t index = TEST_RAND(N);
    double *vp = arr10000_double_at(a, index);
    return *vp;
}

#define CHECK(_x, _y) {                                             \
    assert(arr10000_double_size(&_x) == _y.size());                 \
    assert(arr10000_double_empty(&_x) == _y.empty());               \
    assert(_y.front() == *arr10000_double_front(&_x));              \
    assert(_y.back() == *arr10000_double_back(&_x));                \
    std::array<double,10000>::iterator _iter = _y.begin();          \
    foreach(arr10000_double, &_x, _it) {                            \
        assert(*_it.ref == *_iter);                                 \
        _iter++;                                                    \
    }                                                               \
    arr10000_double_it _it = arr10000_double_it_each(&_x);          \
    for(auto& _d : _y) {                                            \
        assert(*_it.ref == _d);                                     \
        _it.step(&_it);                                             \
    }                                                               \
    for(size_t i = 0; i < _y.size(); i++)                           \
        assert(_y.at(i) == *arr10000_double_at(&_x, i));            \
}

#define CHECK_ITER(_it, b, _iter)                                 \
    if (_it != NULL)                                              \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*_it.ref == *_iter);                               \
    } else                                                        \
        assert (_iter == b.end())

#ifdef DEBUG
static void
get_random_iters (arr10000_double *a, arr10000_double_it *first_a, arr10000_double_it *last_a,
                  std::array<double,10000>& b, std::array<double,10000>::iterator &first_b,
                  std::array<double,10000>::iterator &last_b)
{
    size_t r1 = TEST_RAND(N / 2);
    const size_t rnd = TEST_RAND(N / 2);
    size_t r2 = MIN(r1 + rnd, N);
    LOG("iters %zu, %zu of %d\n", r1, r2, N);
    if (N)
    {
        arr10000_double_it it1 = arr10000_double_it_each (a);
        first_b = b.begin();
        for(size_t i = 0; i < r1; i++)
        {
            it1.step(&it1);
            first_b++;
        }
        *first_a = it1;
        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == N)
        {
            arr10000_double_it it2 = arr10000_double_it_range (a, NULL, NULL);
            *last_a = it2;
            last_b = b.end();
        }
        else
        {
            arr10000_double_it it2 = arr10000_double_it_each(a);
            last_b = b.begin();
            for(size_t i = 0; i < r2; i++)
            {
                it2.step(&it2);
                last_b++;
            }
            *last_a = it2;
        }
        first_a->end = last_a->ref;
    }
    else
    {
        arr10000_double_it end = arr10000_double_it_range (a, NULL, NULL);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
}
#endif

int
main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        arr10000_double a = arr10000_double_init();
        std::array<double,10000> b;
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
        TEST(FIND) \
        TEST(ALL_OF) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(NONE_OF) \
        TEST(COUNT) \
        TEST(COUNT_IF) \

#define FOREACH_DEBUG(TEST) \
        TEST(CLEAR) \
        TEST(EQUAL_RANGE) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(ANY_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE) \
        TEST(INTERSECTION) \
        TEST(DIFFERENCE) \

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
                    *arr10000_double_at(&a, i) = value;
                }
                break;
            }
#ifdef DEBUG
            case TEST_CLEAR:
            {
                b.fill(double{0});
                arr10000_double_clear(&a);
                break;
            }
#endif
            case TEST_FILL:
            {
                const double value = rand() * 1.0;
                b.fill(value);
                arr10000_double_fill(&a, value);
                break;
            }
            case TEST_FILL_N:
            {
                const int n = TEST_RAND(N);
                const int value = TEST_RAND(TEST_MAX_VALUE);
                std::fill_n(b.begin(), n, value);
                arr10000_double_fill_n(&a, n, value);
                break;
            }
            case TEST_SORT:
            {
                arr10000_double_sort(&a);
                std::sort(b.begin(), b.end());
                break;
            }
            case TEST_COPY:
            {
                arr10000_double aa = arr10000_double_copy(&a);
                std::array<double,10000> bb = b;
                CHECK(aa, bb);
                arr10000_double_free(&aa);
                break;
            }
            case TEST_ASSIGN:
            {
                const double value = rand() * 1.0;
                size_t assign_size = TEST_RAND(N - 1);
                arr10000_double_assign(&a, assign_size, value);
                for (size_t i=0; i<assign_size; i++)
                    b[i] = value;
                break;
            }
            case TEST_SWAP:
            {
                arr10000_double aa = arr10000_double_copy(&a);
                arr10000_double aaa = arr10000_double_init();
                std::array<double,10000> bb = b;
                std::array<double,10000> bbb;
                arr10000_double_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                arr10000_double_free(&aaa);
                arr10000_double_free(&aa);
                break;
            }
            case TEST_EQUAL:
            {
                arr10000_double aa = arr10000_double_copy(&a);
                std::array<double,10000> bb = b;
                assert(arr10000_double_equal(&a, &aa));
                assert(b == bb);
                arr10000_double_free(&aa);
                break;
            }
            case TEST_FIND:
            {
                const size_t index = TEST_RAND(N);
                int value = TEST_RAND(2) ? rand() * 1.0
                    : *arr10000_double_at(&a, index);
                double key = value;
                double* aa = arr10000_double_find(&a, key);
                auto bb = std::find(b.begin(), b.end(), value);
                bool found_a = aa != NULL;
                bool found_b = bb != b.end();
                assert(found_a == found_b);
                if(found_a && found_b)
                    assert(*aa == *bb);
                break;
            }
#ifdef DEBUG    // missing range algorithm
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? rand() * 1.0
                    : random_element(&a);
                double key = vb;
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                double *n = arr10000_double_find_range(&first_a, &last_a, key);
                auto it = std::find(first_b, last_b, vb);
                CHECK_ITER(n, b, it);
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                double *n = arr10000_double_find_if_range(&first_a, &last_a, double_is_odd);
                auto it = std::find_if(first_b, last_b, DOUBLE_is_odd);
                print_arr10000(&a);
                print_array(b);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                double *n = arr10000_double_find_if_not_range(&first_a, &last_a, double_is_odd);
                auto it = std::find_if_not(first_b, last_b, DOUBLE_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr10000_double_all_of_range(&first_a, &last_a,
                                                   double_is_odd);
                bool bb = std::all_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr10000(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr10000_double_any_of_range(&first_a, &last_a,
                                                       double_is_odd);
                bool bb = std::any_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr10000(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = arr10000_double_none_of_range(&first_a, &last_a,
                                                        double_is_odd);
                bool bb = std::none_of(first_b, last_b, DOUBLE_is_odd);
                if (aa != bb)
                {
                    print_arr10000(&a);
                    print_array(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = arr10000_double_count_if_range(&first_a, &last_a,
                                                         double_is_odd);
                size_t numb = std::count_if(first_b, last_b, DOUBLE_is_odd);
                if (numa != numb)
                {
                    print_arr10000(&a);
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
                arr10000_double_it first_a, last_a;
                std::array<double,10000>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                // used to fail with 0,0 of 0
                size_t numa = arr10000_double_count_range(&first_a, &last_a, v);
                size_t numb = std::count(first_b, last_b, double{v});
                assert(numa == numb);
                break;
            }
            case TEST_ANY_OF: // broken
            {
                bool is_a = arr10000_double_all_of(&a, double_is_odd);
                bool is_b = std::any_of(b.begin(), b.end(), DOUBLE_is_odd);
                if (is_a != is_b)
                {
                    print_arr10000(&a);
                    print_array(b);
                    printf ("%d != %d FAIL\n", (int)is_a, (int)is_b);
                    fail++;
                }
                //assert(is_a == is_b);
                break;
            }
            case TEST_EQUAL_RANGE:
            case TEST_INTERSECTION:
            case TEST_DIFFERENCE:
                break;
#endif
            case TEST_FIND_IF:
            {
                double* aa = arr10000_double_find_if(&a, double_is_odd);
                auto bb = std::find_if(b.begin(), b.end(), DOUBLE_is_odd);
                if(bb == b.end())
                    assert(arr10000_double_end(&a) == aa);
                else
                    assert(*bb == *aa);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                double* aa = arr10000_double_find_if_not(&a, double_is_odd);
                auto bb = std::find_if_not(b.begin(), b.end(), DOUBLE_is_odd);
                if(bb == b.end())
                    assert(arr10000_double_end(&a) == aa);
                else
                    assert(*bb == *aa);
                break;
            }
            case TEST_ALL_OF:
            {
                bool is_a = arr10000_double_all_of(&a, double_is_odd);
                bool is_b = std::all_of(b.begin(), b.end(), DOUBLE_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = arr10000_double_none_of(&a, double_is_odd);
                bool is_b = std::none_of(b.begin(), b.end(), DOUBLE_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_COUNT:
            {
                double v = TEST_RAND(2) ? rand() * 1.0 : 0.0;
                int aa = arr10000_double_count(&a, v);
                int bb = std::count(b.begin(), b.end(), v);
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF:
            {
                size_t count_a = arr10000_double_count_if(&a, double_is_odd);
                size_t count_b = std::count_if(b.begin(), b.end(), DOUBLE_is_odd);
                assert(count_a == count_b);
                break;
            }
        }
        CHECK(a, b);
        arr10000_double_free(&a);
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
