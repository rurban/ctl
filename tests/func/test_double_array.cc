#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#define POD
#define T double
#define N 20
#include <ctl/array.h>

#include <algorithm>
#include <array>
#include <vector>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(SELF)                                                                                                         \
    TEST(FILL)                                                                                                         \
    TEST(FILL_N)                                                                                                       \
    TEST(SORT)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(SWAP)                                                                                                         \
    TEST(ASSIGN)                                                                                                       \
    TEST(EQUAL)                                                                                                        \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(CLEAR)                                                                                                        \
    TEST(FIND)                                                                                                         \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(TRANSFORM)                                                                                                    \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_RANGE)                                                                                               \
    TEST(GENERATE_N)                                                                                                   \
    TEST(MISMATCH)                                                                                                     \
    TEST(SEARCH)                                                                                                       \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(SEARCH_N)                                                                                                     \
    TEST(SEARCH_N_RANGE)                                                                                               \
    TEST(ADJACENT_FIND)                                                                                                \
    TEST(ADJACENT_FIND_RANGE)                                                                                          \
    TEST(FIND_FIRST_OF)                                                                                                \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END)                                                                                                     \
    TEST(FIND_END_RANGE)                                                                                               \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)                                                                                          \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(REVERSE)                                                                                                      \
    TEST(REVERSE_RANGE)                                                                                                \
    TEST(DIFFERENCE_RANGE)                                                                                             \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(INTERSECTION_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(GENERATE_N_RANGE) /* 56 */                                                                                    \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

// clang-format off
enum
{
    FOREACH_METH(GENERATE_ENUM)
#ifdef DEBUG
    FOREACH_DEBUG(GENERATE_ENUM)
#endif
    TEST_TOTAL
};
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
#ifdef DEBUG
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""};
// clang-format on
#endif

int double_is_odd(double *d)
{
    return ((long)*d) % 2;
}
int DOUBLE_is_odd(double d)
{
    return ((long)d) % 2;
}

static double _generator_state = 0.0;
void double_generate_reset()
{
    _generator_state = 0.0;
}
double double_generate(void)
{
    _generator_state += 1.0;
    return _generator_state;
}
double double_untrans(double *v)
{
    return 2.0 * *v;
}
double DOUBLE_untrans(double &v)
{
    return 2.0 * v;
}
double double_bintrans(double *v1, double *v2)
{
    return *v1 * *v2;
}
double DOUBLE_bintrans(double &v1, double &v2)
{
    return v1 * v2;
}

#define N 20

#ifdef DEBUG
void print_arr20(arr20_double *a)
{
    foreach (arr20_double, a, it)
        printf("%e ", *it.ref);
    printf("\n");
}
void print_arr20_range(arr20_double_it *it)
{
    double* ref = &it->container->vector[0];
    double* end = &it->container->vector[N];
    while (ref < it->ref && ref < end)
    {
        printf("%e ", *ref);
        ref++;
    }
    printf("[");
    while (ref < it->end && ref < end)
    {
        printf("%e ", *ref);
        ref++;
    }
    printf(") ");
    while (ref < end)
    {
        printf("%e ", *ref);
        ref++;
    }
    printf("\n");
}

void print_array(std::array<double, 20> &b)
{
    for (auto &d : b)
        printf("%e ", d);
    printf("\n");
}
#define TEST_MAX_VALUE 1000
#else
#define print_arr20(x)
#define print_arr20_range(x)
#define print_array(x)
#define TEST_MAX_VALUE INT_MAX
#endif

static void gen_arrays(arr20_double *a, std::array<double,20> &b)
{
    *a = arr20_double_init();
    for (int i = 0; i < N; i++)
    {
        const double value = rand() * 1.0;
        a->vector[i] = value;
        b[i] = value;
    }
}

int random_element(arr20_double *a)
{
    const size_t index = TEST_RAND(N);
    double *vp = arr20_double_at(a, index);
    return *vp;
}
#define pick_random(x) random_element(x)

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(arr20_double_size(&_x) == _y.size());                                                                   \
        assert(arr20_double_empty(&_x) == _y.empty());                                                                 \
        assert(_y.front() == *arr20_double_front(&_x));                                                                \
        assert(_y.back() == *arr20_double_back(&_x));                                                                  \
        auto _iter = _y.begin();                                                                                       \
        foreach (arr20_double, &_x, _it)                                                                               \
        {                                                                                                              \
            assert(*_it.ref == *_iter);                                                                                \
            _iter++;                                                                                                   \
        }                                                                                                              \
        double *_ref = arr20_double_front(&_x);                                                                        \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_ref == _d);                                                                                       \
            _ref++;                                                                                                    \
        }                                                                                                              \
        for (size_t _i = 0; _i < _y.size(); _i++)                                                                      \
            assert(_y.at(_i) == *arr20_double_at(&_x, _i));                                                            \
    }

#define CHECK_N(_x, _y, n)                                                                                             \
    {                                                                                                                  \
        for (size_t _i = 0; _i < n; _i++)                                                                              \
            assert((_y).at(_i) == *arr20_double_at(&(_x), _i));                                                        \
    }

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if ((_it).ref && (_it).ref != &(_it).container->vector[N])                                                         \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!arr20_double_it_done(&(_it)))                                                                                 \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

static void get_random_iters(arr20_double *a, arr20_double_it *first_a, std::array<double, 20> &b,
                             std::array<double, 20>::iterator &first_b, std::array<double, 20>::iterator &last_b)
{
    arr20_double_it last_a;
    size_t r1 = TEST_RAND(N / 2);
    const size_t rnd = TEST_RAND(N / 2);
    size_t r2 = MIN(r1 + rnd, N);
    LOG("iters %zu, %zu of %d\n", r1, r2, N);
    if (N)
    {
        arr20_double_it it1 = arr20_double_begin(a);
        first_b = b.begin();
        arr20_double_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == N)
        {
            last_a = arr20_double_end(a);
            last_b = b.end();
        }
        else
        {
            arr20_double_it it2 = arr20_double_begin(a);
            arr20_double_it_advance(&it2, r2);
            last_a = it2;
            last_b = b.begin();
            last_b += r2;
        }
        first_a->end = last_a.ref;
    }
    else
    {
        arr20_double_it end = arr20_double_end(a);
        *first_a = end;
        last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.ref;
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        arr20_double a, aa, aaa;
        std::array<double, 20> b, bb, bbb;
        arr20_double_it range_a1, range_a2, it;
        arr20_double_it *pos;
        std::array<double, 20>::iterator first_b1, last_b1, first_b2, last_b2, iter;
        const int n = TEST_RAND(N);
        double value = rand() * 1.0;
        bool found_a, found_b;
        size_t num_a, num_b;

        a = arr20_double_init();

        for (int i = 0; i < N; i++)
        {
            value = rand() * 1.0;
            b[i] = value;
            a.vector[i] = value;
        }
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        }
        else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        LOG("TEST=%d %s\n", which, test_names[which]);
        RECORD_WHICH;
        switch (which)
        {
        case TEST_SELF: {
            for (int i = 0; i < N; i++)
            {
                value = rand() * 1.0;
                b[i] = value;
                *arr20_double_at(&a, i) = value;
            }
            break;
        }
        case TEST_CLEAR: {
            b.fill(double{0.});
            arr20_double_clear(&a);
            break;
        }
        case TEST_FILL: {
            b.fill(value);
            arr20_double_fill(&a, value);
            break;
        }
        case TEST_FILL_N: {
            std::fill_n(b.begin(), n, value);
            arr20_double_fill_n(&a, n, value);
            break;
        }
        case TEST_SORT: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            break;
        }
        case TEST_COPY: {
            aa = arr20_double_copy(&a);
            bb = b;
            CHECK(aa, bb);
            arr20_double_free(&aa);
            break;
        }
        case TEST_ASSIGN: {
            size_t assign_size = TEST_RAND(N - 1);
            arr20_double_assign(&a, assign_size, value);
            for (size_t i = 0; i < assign_size; i++)
                b[i] = value;
            break;
        }
        case TEST_SWAP: {
            aa = arr20_double_copy(&a);
            aaa = arr20_double_init();
            bb = b;
            arr20_double_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            arr20_double_free(&aaa);
            arr20_double_free(&aa);
            break;
        }
        case TEST_EQUAL: {
            aa = arr20_double_copy(&a);
            bb = b;
            assert(arr20_double_equal(&a, &aa));
            assert(b == bb);
            arr20_double_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = *arr20_double_at(&a, n);
            LOG("equal_value %e\n", value);
            print_arr20(&a);
            found_a = arr20_double_equal_value(&range_a1, value);
            found_b = first_b1 != last_b1;
            for (; first_b1 != last_b1; first_b1++)
            {
                if (value != *first_b1)
                {
                    found_b = false;
                    break;
                }
            }
            LOG("same_a: %d same_b: %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_EQUAL_RANGE: {
            aa = arr20_double_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr20_double_equal_range(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            found_b = std::equal(first_b1, last_b1, first_b2, last_b2);
            LOG("same_a: %d same_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
#else
            found_b = std::equal(first_b1, last_b1, first_b2);
            LOG("same_a: %d same_b %d\n", (int)found_a, (int)found_b);
            if (found_a != found_b)
                printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
            arr20_double_free(&aa);
            break;
        }
        case TEST_LEXICOGRAPHICAL_COMPARE: {
            aa = arr20_double_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr20_double_lexicographical_compare(&range_a1, &range_a2);
            found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
            LOG("same_a: %d same_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_FIND: {
            double key = TEST_RAND(2) ? value : *arr20_double_at(&a, n);
            double *d = arr20_double_find(&a, key);
            iter = std::find(b.begin(), b.end(), key);
            found_a = d != NULL;
            found_b = iter != b.end();
            assert(found_a == found_b);
            if (found_a && found_b)
                assert(*d == *iter);
            break;
        }
        case TEST_COUNT_RANGE: {
            value = TEST_RAND(2) ? value : 0;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            num_a = arr20_double_count_range(&range_a1, value);
            num_b = std::count(first_b1, last_b1, value);
            assert(num_a == num_b);
            break;
        }
        case TEST_GENERATE: {
            double_generate_reset();
            arr20_double_generate(&a, double_generate);
            double_generate_reset();
            std::generate(b.begin(), b.end(), double_generate);
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF: {
            it = arr20_double_find_if(&a, double_is_odd);
            iter = std::find_if(b.begin(), b.end(), DOUBLE_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_FIND_IF_NOT: {
            it = arr20_double_find_if_not(&a, double_is_odd);
            iter = std::find_if_not(b.begin(), b.end(), DOUBLE_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_ALL_OF: {
            found_a = arr20_double_all_of(&a, double_is_odd);
            found_b = std::all_of(b.begin(), b.end(), DOUBLE_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_ANY_OF: {
            found_a = arr20_double_any_of(&a, double_is_odd);
            found_b = std::any_of(b.begin(), b.end(), DOUBLE_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_NONE_OF: {
            found_a = arr20_double_none_of(&a, double_is_odd);
            found_b = std::none_of(b.begin(), b.end(), DOUBLE_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_COUNT: {
            value = TEST_RAND(2) ? value : 0.0;
            num_a = arr20_double_count(&a, value);
            num_b = std::count(b.begin(), b.end(), value);
            assert(num_a == num_b);
            break;
        }
        case TEST_COUNT_IF: {
            num_a = arr20_double_count_if(&a, double_is_odd);
            num_b = std::count_if(b.begin(), b.end(), DOUBLE_is_odd);
            assert(num_a == num_b);
            break;
        }
        case TEST_FIND_RANGE: {
            int vb = TEST_RAND(2) ? value : random_element(&a);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr20_double_find_range(&range_a1, vb);
            iter = std::find(first_b1, last_b1, vb);
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            CHECK_RANGE(range_a1, iter, last_b1);
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = arr20_double_find_if_range(&range_a1, double_is_odd);
            iter = std::find_if(first_b1, last_b1, DOUBLE_is_odd);
            print_arr20(&a);
            print_array(b);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = arr20_double_find_if_not_range(&range_a1, double_is_odd);
            iter = std::find_if_not(first_b1, last_b1, DOUBLE_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr20_double_all_of_range(&range_a1, double_is_odd);
            found_b = std::all_of(first_b1, last_b1, DOUBLE_is_odd);
            if (found_a != found_b)
            {
                print_arr20(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        }
        case TEST_NONE_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr20_double_none_of_range(&range_a1, double_is_odd);
            found_b = std::none_of(first_b1, last_b1, DOUBLE_is_odd);
            if (found_a != found_b)
            {
                print_arr20(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            num_a = arr20_double_count_if_range(&range_a1, double_is_odd);
            num_b = std::count_if(first_b1, last_b1, DOUBLE_is_odd);
            if (num_a != num_b)
            {
                print_arr20(&a);
                print_array(b);
                printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                fail++;
            }
            assert(num_a == num_b);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr20_double_any_of_range(&range_a1, double_is_odd);
            found_b = std::any_of(first_b1, last_b1, DOUBLE_is_odd);
            if (found_a != found_b)
            {
                print_arr20(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        }
        case TEST_TRANSFORM: {
            aa = arr20_double_transform(&a, double_untrans);
            std::transform(b.begin(), b.end(), bb.begin(), DOUBLE_untrans);
            CHECK(aa, bb);
            CHECK(a, b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_TRANSFORM_IT: {
            it = arr20_double_begin(&a);
            arr20_double_it_advance(&it, 1);
            aa = arr20_double_transform_it(&a, &it, double_bintrans);
            std::transform(b.begin(), b.end() - 1, b.begin() + 1, bb.begin(), DOUBLE_bintrans);
            aa.vector[19] = bb[19];
            CHECK(aa, bb);
            CHECK(a, b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_GENERATE_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            double_generate_reset();
            arr20_double_generate_range(&range_a1, double_generate);
            double_generate_reset();
            std::generate(first_b1, last_b1, double_generate);
            CHECK(a, b);
            break;
        }
        case TEST_GENERATE_N: {
            double_generate_reset();
            arr20_double_generate_n(&a, n, double_generate);
            double_generate_reset();
            std::generate_n(b.begin(), n, double_generate);
            CHECK(a, b);
            break;
        }
        case TEST_MISMATCH: {
            aa = arr20_double_init_from(&a);
            gen_arrays(&aa, bb);
            arr20_double_it b1, b2;
            b1 = arr20_double_begin(&a);
            b2 = arr20_double_begin(&aa);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            /* found_a = */ arr20_double_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
            auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
            int d1a = arr20_double_it_distance(&b1, &range_a1);
            int d2a = arr20_double_it_distance(&b2, &range_a2);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == std::distance(b.begin(), pair.first));
            assert(d2a == std::distance(bb.begin(), pair.second));
            arr20_double_free(&aa);
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_arr20(&a);
            it = arr20_double_adjacent_find(&a);
            iter = std::adjacent_find(b.begin(), b.end());
            CHECK_ITER(it, b, iter);
            LOG("found %s\n", arr20_double_it_done(&it) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr20(&a);
            pos = arr20_double_adjacent_find_range(&range_a1);
            iter = std::adjacent_find(first_b1, last_b1);
            CHECK_RANGE(*pos, iter, last_b1);
            // CHECK_ITER(*aa, b, bb);
            LOG("found %s\n", arr20_double_it_done(pos) ? "no" : "yes");
            break;
        }
        case TEST_SEARCH: // 42
        {
            print_arr20(&a);
            aa = arr20_double_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b2 - bb.begin();
                arr20_double_set(&aa, i, 0.);
                bb[i] = 0.;
            }
            // print_arr20(aa);
            it = arr20_double_search(&a, &range_a2);
            iter = std::search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", arr20_double_it_done(&it) ? "no" : "yes");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            CHECK_RANGE(it, iter, b.end());
            arr20_double_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            aa = arr20_double_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b2 - bb.begin();
                arr20_double_set(&aa, i, 0.);
                bb[i] = 0.;
            }
            print_arr20_range(&range_a2);
            range_a1 = arr20_double_begin(&a);
            found_a = arr20_double_search_range(&range_a1, &range_a2);
            iter = std::search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", found_a ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(found_a == !arr20_double_it_done(&range_a1));
            if (found_a)
                assert(iter != b.end());
            else
                assert(iter == b.end());
            CHECK_ITER(range_a1, b, iter);
            arr20_double_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_arr20(&a);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n %zu %e\n", count, value);
            it = arr20_double_search_n(&a, count, value);
            iter = std::search_n(b.begin(), b.end(), count, value);
            CHECK_ITER(it, b, iter);
            LOG("found %s at %zu\n", arr20_double_it_done(&it) ? "no" : "yes", arr20_double_it_index(&it));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n_range %zu %e\n", count, value);
            print_arr20_range(&range_a1);
            pos = arr20_double_search_n_range(&range_a1, count, value);
            iter = std::search_n(first_b1, last_b1, count, value);
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s at %zu\n", arr20_double_it_done(pos) ? "no" : "yes", arr20_double_it_index(pos));
            break;
        }
        case TEST_FIND_FIRST_OF: {
            print_arr20(&a);
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            it = arr20_double_find_first_of(&a, &range_a2);
            iter = std::find_first_of(b.begin(), b.end(), first_b2, last_b2);
            print_arr20(&aa);
            LOG("=> %zu vs %ld\n", arr20_double_it_index(&it), iter - b.begin());
            CHECK_ITER(it, b, iter);
            arr20_double_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr20(&a);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            print_arr20(&aa);

            found_a = arr20_double_find_first_of_range(&range_a1, &range_a2);
            iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                iter != last_b1 ? "yes" : "no", range_a1.ref - a.vector,
                iter - b.begin());
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            // CHECK_RANGE(range_a1, it, last_b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < 4; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            range_a2 = arr20_double_begin(&aa);
            print_arr20(&a);
            print_arr20(&aa);
            range_a2.end = range_a2.ref + 4;
            it = arr20_double_find_end(&a, &range_a2);
            iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.begin() + 4);
            found_a = !arr20_double_it_done(&it);
            found_b = iter != b.end();
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                iter - b.begin());
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < 4; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            range_a2 = arr20_double_begin(&aa);
            range_a2.end = range_a2.ref + 4;
#if __cpp_lib_erase_if >= 202002L
            it = arr20_double_find_end_range(&range_a1, &range_a2);
            iter = std::find_end(first_b1, last_b1, bb.begin(), bb.begin() + 4);
            CHECK_ITER(it, b, iter);
#endif
            arr20_double_free(&aa);
            break;
        }
        case TEST_LOWER_BOUND: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            LOG("lower_bound %e of ", value);
            print_arr20(&a);
            it = arr20_double_lower_bound(&a, value);
            iter = std::lower_bound(b.begin(), b.end(), value);
            if (iter != b.end())
            {
                LOG("%e: %e vs %e\n", value, *it.ref, *iter);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_UPPER_BOUND: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            LOG("upper_bound %e of ", value);
            print_arr20(&a);
            it = arr20_double_upper_bound(&a, value);
            iter = std::upper_bound(b.begin(), b.end(), value);
            if (iter != b.end())
            {
                LOG("%e: %e vs %e\n", value, *it.ref, *iter);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = arr20_double_lower_bound_range(&range_a1, value);
            iter = std::lower_bound(first_b1, last_b1, value);
            if (iter != last_b1)
            {
                LOG("%e: %e vs %e\n", value, *pos->ref, *iter);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = arr20_double_upper_bound_range(&range_a1, value);
            iter = std::upper_bound(first_b1, last_b1, value);
            if (iter != last_b1)
            {
                LOG("%e: %e vs %e\n", value, *pos->ref, *iter);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_BINARY_SEARCH: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            found_a = arr20_double_binary_search(&a, value);
            found_b = std::binary_search(b.begin(), b.end(), value);
            LOG("%e: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            found_a = arr20_double_binary_search_range(&range_a1, value);
            found_b = std::binary_search(first_b1, last_b1, value);
            LOG("%e: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_INCLUDES: {
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            print_arr20(&a);
            print_arr20(&aa);
            //arr20_double_it range_a2 = arr20_double_begin(&aa);
            //range_a2.end = range_a2.ref + 4;
            found_a = arr20_double_includes(&a, &aa);
            found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
            LOG("%d vs %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_INCLUDES_RANGE: {
            aa = arr20_double_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = pick_random(&a);
                bb[i] = value;
                aa.vector[i] = value;
            }
            arr20_double_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr20_double_includes_range(&range_a1, &range_a2);
            found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
            LOG("%d vs %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_IS_SORTED: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr20(&a);
            found_a = arr20_double_is_sorted(&range_a1);
            found_b = std::is_sorted(first_b1, last_b1);
            LOG("a_yes: %d b_yes %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_IS_SORTED_UNTIL: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr20_range(&range_a1);
            range_a2 = range_a1;
            range_a2.ref = range_a1.end;
            pos = arr20_double_is_sorted_until(&range_a1, &range_a2);
            iter = std::is_sorted_until(first_b1, last_b1);
            CHECK_ITER(*pos, b, iter);
            break;
        }
        case TEST_REVERSE: {
            print_arr20(&a);
            arr20_double_reverse(&a);
            std::reverse(b.begin(), b.end());
            print_arr20(&a);
            print_array(b);
            CHECK(a, b);
            break;
        }
        case TEST_REVERSE_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr20(&a);
            arr20_double_reverse_range(&range_a1);
            std::reverse(first_b1, last_b1);
            print_arr20(&a);
            CHECK(a, b);
            break;
        }
        case TEST_INTERSECTION_RANGE: {
            gen_arrays(&aa, bb);
            arr20_double_sort(&a);
            arr20_double_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_arr20_range(&range_a1);
            print_arr20_range(&range_a2);
            it = arr20_double_intersection_range(&range_a1, &range_a2);
            num_a = arr20_double_it_distance_range(&it);
            LOG("CTL => it (%zu)\n", num_a);
            print_arr20_range(&it);

            std::vector<double> bbb_;
            LOG("STL b + bb\n");
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb\n[");
            for (unsigned i = 0; i < bbb_.size(); i++)
            {
                bbb[i] = bbb_[i];
                LOG("%e ", bbb[i]);
            }
            LOG(")\n");
            assert(num_a == bbb_.size());
            CHECK_N(*it.container, bbb, num_a);
#endif
            arr20_double_free(it.container);
            free (it.container);
            arr20_double_free(&aa);
            break;
        }
        case TEST_DIFFERENCE_RANGE: {
            gen_arrays(&aa, bb);
            arr20_double_sort(&a);
            arr20_double_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            //LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
            print_arr20_range(&range_a1);
            print_arr20_range(&range_a2);
            it = arr20_double_difference_range(&range_a1, &range_a2);
            num_a = arr20_double_it_distance_range(&it);
            LOG("CTL => it (%zu)\n", num_a);
            print_arr20_range(&it);

            std::vector<double> bbb_;
            LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb (%zu)\n[", bbb.size());
            for (unsigned i = 0; i < bbb_.size(); i++)
            {
                bbb[i] = bbb_[i];
                LOG("%e ", bbb[i]);
            }
            LOG(")\n");
            assert(num_a == bbb_.size());
            CHECK_N(*it.container, bbb, num_a)
#endif
            arr20_double_free(it.container);
            free (it.container);
            arr20_double_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
            gen_arrays(&aa, bb);
            arr20_double_sort(&a);
            arr20_double_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_arr20_range(&range_a1);
            print_arr20_range(&range_a2);
            it = arr20_double_symmetric_difference_range(&range_a1, &range_a2);
            num_a = arr20_double_it_distance_range(&it);
            LOG("CTL => it (%zu)\n", num_a);
            print_arr20_range(&it);

            std::vector<double> bbb_;
            LOG("STL b + bb\n");
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb\n[");
            for (unsigned i = 0; i < bbb_.size(); i++)
            {
                bbb[i] = bbb_[i];
                LOG("%e ", bbb[i]);
            }
            LOG(")\n");
            assert(num_a == bbb_.size());
            CHECK_N(*it.container, bbb, num_a);
#endif
            arr20_double_free(it.container);
            free (it.container);
            arr20_double_free(&aa);
            break;
        }

#ifdef DEBUG
        case TEST_GENERATE_N_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t off = first_b1 - b.begin();
            size_t count = TEST_RAND(20 - off);
            double_generate_reset();
            arr20_double_generate_n_range(&range_a1, count, double_generate);
            double_generate_reset();
            std::generate_n(first_b1, count, double_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            // FIXME
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr20_double_init();
            range_a2 = arr20_double_begin(&aa);
            it = arr20_double_transform_range(&range_a1, range_a2, double_untrans);
            iter = std::transform(b.begin(), b.end(), b.begin() + 1, bb.begin(), DOUBLE_bintrans);
            CHECK_ITER(it, bb, iter);
            CHECK(aa, bb);
            CHECK(a, b);
            arr20_double_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            aa = arr20_double_copy_if(&a, double_is_odd);
            bb = b;
            size_t i = 0;
            for (auto &d : b)
            {
                if (double_is_odd(&d))
                    bb[i] = d;
                i++;
            }
            CHECK(aa, bb);
            arr20_double_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr20_double_copy_if_range(&range_a1, double_is_odd);
            size_t i = arr20_double_it_index(&range_a1);
            bb = b;
            for (auto &d : b)
            {
                if (double_is_odd(&d))
                    bb[i] = d;
                i++;
            }
            arr20_double_free(&aa);
            CHECK(a, b);
            break;
        }
#endif // DEBUG

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
    FINISH_TEST(__FILE__);
}

#endif // C++11
