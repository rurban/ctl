#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define N 100
#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#include <ctl/array.h>

#include <algorithm>
#include <numeric>
#include <array>
#include <vector>
#ifdef NEED_RANDOM_ENGINE
#include <random>
#endif

#define N 100

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
    TEST(FIND)                                                                                                         \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(MISMATCH)                                                                                                     \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_RANGE)                                                                                               \
    TEST(GENERATE_N)                                                                                                   \
    TEST(TRANSFORM)                                                                                                    \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
    TEST(SHUFFLE)                                                                                                      \
    TEST(SHUFFLE_RANGE)                                                                                                \
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
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(ASSIGN_RANGE)                                                                                                 \
    TEST(ASSIGN_GENERIC)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(GENERATE_N_RANGE) /* 58 */                                                                                    \
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
static const char *test_names[] = { FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif
// clang-format on

void print_arr100(arr100_digi *a)
{
    foreach (arr100_digi, a, it)
    {
        if (!it.ref->value)
            break;
        printf("%d ", *it.ref->value);
    }
    printf("\n");
}

void print_arr100_range(arr100_digi_it *it)
{
    digi* ref = &it->container->vector[0];
    digi* end = &it->container->vector[N];
    while (ref < it->ref && ref < end)
    {
        printf("%d ", ref->value ? *ref->value : -1);
        ref++;
    }
    printf("[");
    while (ref < it->end && ref < end)
    {
        printf("%d ", ref->value ? *ref->value : -1);
        ref++;
    }
    printf(") ");
    while (ref < end)
    {
        if (!ref->value)
            break;
        printf("%d ", *ref->value);
        ref++;
    }
    printf("\n");
}

void print_array(std::array<DIGI, 100> &b)
{
    for (auto &d : b)
    {
        if (!d.value)
            break;
        printf("%d ", *d.value);
    }
    printf("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 1000
#else
#define print_arr100(x)
#define print_arr100_range(x)
#define print_array(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int middle(arr100_digi *a)
{
    return (*arr100_digi_front(a)->value - *arr100_digi_back(a)->value) / 2;
}

int median(arr100_digi *a)
{
    arr100_digi_it it = arr100_digi_begin(a);
    arr100_digi_it_advance(&it, N / 2);
    return it.ref->value ? *it.ref->value : 0;
}

int random_element(arr100_digi *a)
{
    const size_t index = TEST_RAND(N);
    digi *vp = arr100_digi_at(a, index);
    return *vp->value;
}

int pick_random(arr100_digi *a)
{
    switch (TEST_RAND(4))
    {
    case 0:
        return middle(a);
    case 1:
        return median(a);
    case 2:
        return random_element(a);
    case 3:
        return TEST_RAND(TEST_MAX_VALUE);
    }
    assert(0);
}

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(arr100_digi_size(&(_x)) == _y.size());                                                                  \
        assert(arr100_digi_empty(&(_x)) == _y.empty());                                                                \
        assert(*_y.front().value == *arr100_digi_front(&(_x))->value);                                                 \
        /* assert(*_y.back().value == *arr100_digi_back(&(_x))->value); */                                             \
        std::array<DIGI, 100>::iterator _iter = _y.begin();                                                            \
        foreach (arr100_digi, &(_x), _it)                                                                              \
        {                                                                                                              \
            if (!(_it.ref->value))                                                                                     \
                break;                                                                                                 \
            assert(*_it.ref->value == *_iter->value);                                                                  \
            _iter++;                                                                                                   \
        }                                                                                                              \
        digi *_ref = arr100_digi_front(&(_x));                                                                         \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            if (!_ref || !_ref->value)                                                                                 \
                break;                                                                                                 \
            assert(*(_ref->value) == *_d.value);                                                                       \
            _ref++;                                                                                                    \
        }                                                                                                              \
        for (size_t _i = 0; _i < _y.size(); _i++)                                                                      \
        {                                                                                                              \
            if (!(_x).vector[_i].value)                                                                                \
                break;                                                                                                 \
            assert(*_y.at(_i).value == *arr100_digi_at(&(_x), _i)->value);                                             \
        }                                                                                                              \
    }

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if ((_it).ref && (_it).ref != &(_it).container->vector[N])                                                         \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*((_it).ref->value) == *(*_iter).value);                                                                \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!arr100_digi_it_done(&_it))                                                                                    \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

#define CHECK_REF(_ref, b, _iter)                                                                                      \
    if (_iter != b.end())                                                                                              \
    assert(*(_ref->value) == *(*_iter).value)

static void gen_arrays(arr100_digi *a, std::array<DIGI,100> &b)
{
    *a = arr100_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for (int i = 0; i < N; i++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        a->vector[i] = digi_init(vb);
        b[i] = DIGI{vb};
    }
}

static void get_random_iters(arr100_digi *a, arr100_digi_it *first_a, std::array<DIGI, 100> &b,
                             std::array<DIGI, 100>::iterator &first_b, std::array<DIGI, 100>::iterator &last_b)
{
    arr100_digi_it last_a;
    size_t r1 = TEST_RAND(N / 2);
    const size_t rnd = TEST_RAND(N / 2);
    size_t r2 = MIN(r1 + rnd, N);
    LOG("iters %zu, %zu of %d\n", r1, r2, N);
    if (N)
    {
        arr100_digi_it it1 = arr100_digi_begin(a);
        first_b = b.begin();
        arr100_digi_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == N)
        {
            last_a = arr100_digi_end(a);
            last_b = b.end();
        }
        else
        {
            arr100_digi_it it2 = arr100_digi_begin(a);
            arr100_digi_it_advance(&it2, r2);
            last_a = it2;
            last_b = b.begin();
            last_b += r2;
        }
    }
    else
    {
        arr100_digi_it end = arr100_digi_end(a);
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
    INIT_TEST_LOOPS(15,false);

    arr100_digi a, aa, aaa;
    std::array<DIGI, 100> b, bb, bbb;
    arr100_digi_it range_a1, range_a2, it;
    arr100_digi_it* pos;
    std::array<DIGI,100>::iterator first_b1, last_b1, first_b2, last_b2, iter;
    const int n = TEST_RAND(N);
    bool found_a, found_b;
    size_t num_a, num_b;
#ifdef NEED_RANDOM_ENGINE
    std::default_random_engine rng(seed);
#endif

    a = arr100_digi_init();
    a.compare = digi_compare;
    a.equal = digi_equal;

    for (int i = 0; i < N; i++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE);
        b[i] = DIGI{value};
        a.vector[i] = digi_init(value);
    }

    for (unsigned loop = 0; loop < loops; loop++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE);
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        }
        else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        RECORD_WHICH;
        LOG("TEST=%d %s\n", which, test_names[which]);
        switch (which)
        {
        case TEST_SELF: {
            for (int i = 0; i < N; i++)
            {
                value = TEST_RAND(TEST_MAX_VALUE);
                b[i] = DIGI{value};
                arr100_digi_set(&a, i, digi_init(value));
            }
            break;
        }
#if 0 // invalid for non-POD's
        case TEST_CLEAR:
        {
            b.fill(DIGI{0});
            arr100_digi_clear(&a);
            break;
        }
#endif
        case TEST_FILL: {
            b.fill(DIGI{value});
            arr100_digi_fill(&a, digi_init(value));
            break;
        }
        case TEST_FILL_N: {
            std::fill_n(b.begin(), n, DIGI{value});
            arr100_digi_fill_n(&a, n, digi_init(value));
            break;
        }
        case TEST_SORT: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            break;
        }
        case TEST_COPY: {
            aa = arr100_digi_copy(&a);
            bb = b;
            CHECK(aa, bb);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_ASSIGN: {
            size_t assign_size = TEST_RAND(N - 1);
            arr100_digi_assign(&a, assign_size, digi_init(value));
            for (size_t i = 0; i < assign_size; i++)
                b[i] = DIGI{value};
            break;
        }
        case TEST_SWAP: {
            aa = arr100_digi_copy(&a);
            aaa = arr100_digi_init_from(&a);
            bb = b;
            arr100_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            arr100_digi_free(&aaa);
            break;
        }
        case TEST_EQUAL: {
            aa = arr100_digi_copy(&a);
            bb = b;
            assert(arr100_digi_equal(&a, &aa));
            assert(b == bb);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = *a.vector[n].value;
            LOG("equal_value %d\n", value);
            print_arr100(&a);
            found_a = arr100_digi_equal_value(&range_a1, digi_init(value));
            found_b = first_b1 != last_b1;
            for (; first_b1 != last_b1; first_b1++)
            {
                if (value != *(*first_b1).value)
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
            aa = arr100_digi_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr100_digi_equal_range(&range_a1, &range_a2);
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
            arr100_digi_free(&aa);
            break;
        }
        case TEST_LEXICOGRAPHICAL_COMPARE: {
            aa = arr100_digi_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr100_digi_lexicographical_compare(&range_a1, &range_a2);
            found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
            LOG("same_a: %d same_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND: {
            value = TEST_RAND(2) ? value : *arr100_digi_at(&a, n)->value;
            digi key = digi_init(value);
            digi *ref = arr100_digi_find(&a, key);
            iter = std::find(b.begin(), b.end(), DIGI{value});
            found_a = ref != NULL;
            found_b = iter != b.end();
            assert(found_a == found_b);
            if (found_a && found_b)
                assert(*ref->value == *iter->value);
            digi_free(&key); // special
            break;
        }
        case TEST_FIND_RANGE: {
            value = pick_random(&a);
            digi key = digi_init(value);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr100_digi_find_range(&range_a1, key);
            iter = std::find(first_b1, last_b1, DIGI{value});
            LOG("%d at [%ld]\n", *range_a1.ref->value, range_a1.ref - a.vector);
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            CHECK_RANGE(range_a1, iter, last_b1);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = arr100_digi_find_if_range(&range_a1, digi_is_odd);
            iter = std::find_if(first_b1, last_b1, DIGI_is_odd);
            print_arr100(&a);
            print_array(b);
            LOG("%d at [%ld]\n", *it.ref->value, it.ref - a.vector);
            CHECK_RANGE(it, iter, last_b1);
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = arr100_digi_find_if_not_range(&range_a1, digi_is_odd);
            iter = std::find_if_not(first_b1, last_b1, DIGI_is_odd);
            LOG("%d at [%ld]\n", *it.ref->value, it.ref - a.vector);
            CHECK_RANGE(it, iter, last_b1);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr100_digi_all_of_range(&range_a1, digi_is_odd);
            found_b = std::all_of(first_b1, last_b1, DIGI_is_odd);
            /*if (found_a != found_b)
            {
                print_arr100(&a);
                print_array(b);
                printf ("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }*/
            assert(found_a == found_b);
            break;
        }
        case TEST_NONE_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr100_digi_none_of_range(&range_a1, digi_is_odd);
            found_b = std::none_of(first_b1, last_b1, DIGI_is_odd);
            if (found_a != found_b)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            num_a = arr100_digi_count_if_range(&range_a1, digi_is_odd);
            num_b = std::count_if(first_b1, last_b1, DIGI_is_odd);
            if (num_a != num_b)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                fail++;
            }
            assert(num_a == num_b); // fails. off by one, counts one too much
            break;
        }
        case TEST_COUNT_RANGE: {
            value = TEST_RAND(2) ? value : 0;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            // used to fail with 0,0 of 0
            num_a = arr100_digi_count_range(&range_a1, digi_init(value));
            num_b = std::count(first_b1, last_b1, DIGI{value});
            assert(num_a == num_b);
            break;
        }
        case TEST_ANY_OF: {
            found_a = arr100_digi_any_of(&a, digi_is_odd);
            found_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = arr100_digi_any_of_range(&range_a1, digi_is_odd);
            found_b = std::any_of(first_b1, last_b1, DIGI_is_odd);
            if (found_a != found_b)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        }
        case TEST_FIND_IF: {
            it = arr100_digi_find_if(&a, digi_is_odd);
            iter = std::find_if(b.begin(), b.end(), DIGI_is_odd);
            if (iter == b.end())
                assert(arr100_digi_it_done(&it));
            else
                assert(*(it.ref->value) == *iter->value);
            break;
        }
        case TEST_FIND_IF_NOT: {
            it = arr100_digi_find_if_not(&a, digi_is_odd);
            iter = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
            if (iter == b.end())
                assert(arr100_digi_it_done(&it));
            else
                assert(*(it.ref->value) == *iter->value);
            break;
        }
        case TEST_ALL_OF: {
            found_a = arr100_digi_all_of(&a, digi_is_odd);
            found_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_NONE_OF: {
            found_a = arr100_digi_none_of(&a, digi_is_odd);
            found_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
            assert(found_a == found_b);
            break;
        }
        case TEST_COUNT: {
            num_a = arr100_digi_count(&a, digi_init(value));
            num_b = std::count(b.begin(), b.end(), DIGI{value});
            assert(num_a == num_b);
            break;
        }
        case TEST_COUNT_IF: {
            num_a = arr100_digi_count_if(&a, digi_is_odd);
            num_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
            assert(num_a == num_b);
            break;
        }
        case TEST_GENERATE: {
            digi_generate_reset();
            arr100_digi_generate(&a, digi_generate);
            digi_generate_reset();
            std::generate(b.begin(), b.end(), DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_GENERATE_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            digi_generate_reset();
            arr100_digi_generate_range(&range_a1, digi_generate);
            digi_generate_reset();
            std::generate(first_b1, last_b1, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: {
            aa = arr100_digi_transform(&a, digi_untrans);
            std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
            CHECK(aa, bb);
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_IT: {
            print_arr100(&a);
            it = arr100_digi_begin(&a);
            arr100_digi_it_advance(&it, 1);
            aa = arr100_digi_transform_it(&a, &it, digi_bintrans);
            // the last one is uninitialized
            std::transform(b.begin(), b.end() - 1, b.begin() + 1, bb.begin(), DIGI_bintrans);
            LOG("STL => ");
            print_array(bb);
            arr100_digi_set(&aa, 99, digi_init(*bb[99].value));
            LOG("CTL => ");
            print_arr100(&aa);
            CHECK(aa, bb);
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_GENERATE_N: {
            size_t count = TEST_RAND(20);
            print_arr100(&a);
            LOG("generate_n %zu\n", count);
            digi_generate_reset();
            arr100_digi_generate_n(&a, count, digi_generate);
            print_arr100(&a);
            digi_generate_reset();
            std::generate_n(b.begin(), count, DIGI_generate);
            print_array(b);
            CHECK(a, b);
            break;
        }
        case TEST_ASSIGN_RANGE: {
            aa = arr100_digi_init_from(&a);
            digi_generate_reset();
            arr100_digi_generate(&a, digi_generate);
            print_arr100(&aa);
            digi_generate_reset();
            // STL has no assign method
            std::generate(b.begin(), b.end(), DIGI_generate);
            range_a2 = arr100_digi_begin(&aa);
            arr100_digi_assign_range(&a, &aa.vector[0], &aa.vector[N-1]);
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_ASSIGN_GENERIC: {
            aa = arr100_digi_init_from(&a);
            digi_generate_reset();
            arr100_digi_generate(&aa, digi_generate);
            print_arr100(&aa);
            digi_generate_reset();
            std::generate(b.begin(), b.end(), DIGI_generate);
            range_a2 = arr100_digi_begin(&aa);
            arr100_digi_assign_generic(&a, &range_a2);
            // STL has no assign method
            // b.assign(bb.begin(), bb.end());
            //LOG("CTL =>\n");
            print_arr100(&a);
            //LOG("STL =>\n");
            //print_array(b);
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_IOTA: {
            digi key = digi_init(0);
            arr100_digi_iota(&a, key);
            print_arr100(&a);
            std::iota(b.begin(), b.end(), DIGI{0});
            print_array(b);
            CHECK(a, b);
            digi_free(&key);
            break;
        }
        case TEST_IOTA_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            digi key = digi_init(0);
            arr100_digi_iota_range(&range_a1, key);
            print_arr100_range(&range_a1);
            std::iota(first_b1, last_b1, DIGI{0});
            print_array(b);
            CHECK(a, b);
            digi_free(&key);
            break;
        }
        case TEST_SHUFFLE: {
            print_arr100(&a);
            arr100_digi_shuffle(&a);
            print_arr100(&a);
#ifndef NEED_RANDOM_ENGINE
            std::random_shuffle(b.begin(), b.end());
#else
            std::shuffle(first_b1, last_b1, rng);
#endif
            print_array(b);
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            CHECK(a, b);
            break;
        }
        case TEST_SHUFFLE_RANGE: {
            print_arr100(&a);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            arr100_digi_shuffle_range(&range_a1);
            print_arr100_range(&range_a1);
#ifndef NEED_RANDOM_ENGINE
            std::random_shuffle(first_b1, last_b1);
#else
            std::shuffle(first_b1, last_b1, rng);
#endif
            // TODO check that the ranges before and after range are still
            // sorted, and untouched.
            print_array(b);
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            CHECK(a, b);
            break;
        }
#ifdef DEBUG
        case TEST_GENERATE_N_RANGE: // TEST=32
        {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t off = first_b1 - b.begin();
            size_t count = TEST_RAND(20 - off);
            digi_generate_reset();
            arr100_digi_generate_n_range(&range_a1, count, digi_generate);
            digi_generate_reset();
            std::generate_n(first_b1, count, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr100_digi_init_from(&a);
            range_a2 = arr100_digi_begin(&aa);
            it = arr100_digi_transform_range(&range_a1, range_a2, digi_untrans);
            iter = std::transform(first_b1, last_b1, b.begin() + 1, bb.begin(), DIGI_bintrans);
            CHECK_RANGE(it, iter, last_b1);
            // CHECK_ITER(it, bb, iter);
            CHECK(aa, bb);
            // heap use-after-free
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            aa = arr100_digi_copy_if(&a, digi_is_odd);
            bb = b;
            size_t i = 0;
            for (auto &d : b)
            {
                if (DIGI_is_odd(d))
                    bb[i] = d;
                i++;
            }
            CHECK(aa, bb);
            arr100_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY_IF_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr100_digi_copy_if_range(&range_a1, digi_is_odd);
            size_t i = arr100_digi_it_index(&range_a1);
            bb = b;
            for (auto &d : b)
            {
                if (DIGI_is_odd(d))
                    bb[i] = d;
                i++;
            }
            arr100_digi_free(&aa);
            CHECK(a, b);
            break;
        }
#endif // DEBUG
        case TEST_MISMATCH: {
            aa = arr100_digi_init_from(&a);
            gen_arrays(&aa, bb);
            arr100_digi_it b1, b2;
            b1 = arr100_digi_begin(&a);
            b2 = arr100_digi_begin(&aa);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            /* found_a = */ arr100_digi_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
            auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
            int d1a = arr100_digi_it_distance(&b1, &range_a1);
            int d2a = arr100_digi_it_distance(&b2, &range_a2);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == std::distance(b.begin(), pair.first));
            assert(d2a == std::distance(bb.begin(), pair.second));
            arr100_digi_free(&aa);
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_arr100(&a);
            it = arr100_digi_adjacent_find(&a);
            iter = std::adjacent_find(b.begin(), b.end());
            CHECK_ITER(it, b, iter);
            LOG("found %s\n", arr100_digi_it_done(&it) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr100(&a);
            pos = arr100_digi_adjacent_find_range(&range_a1);
            iter = std::adjacent_find(first_b1, last_b1);
            CHECK_RANGE(*pos, iter, last_b1);
            // CHECK_ITER(*aa, b, bb);
            LOG("found %s\n", arr100_digi_it_done(pos) ? "no" : "yes");
            break;
        }
        case TEST_SEARCH: // 42
        {
            print_arr100(&a);
            aa = arr100_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b2 - bb.begin();
                arr100_digi_set(&aa, i, digi_init(0));
                bb[i] = DIGI{0};
            }
            // print_arr100(aa);
            it = arr100_digi_search(&a, &range_a2);
            iter = std::search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", arr100_digi_it_done(&it) ? "no" : "yes");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            CHECK_RANGE(it, iter, b.end());
            arr100_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            aa = arr100_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b2 - bb.begin();
                arr100_digi_set(&aa, i, digi_init(0));
                bb[i] = DIGI{0};
            }
            print_arr100_range(&range_a2);
            range_a1 = arr100_digi_begin(&a);
            found_a = arr100_digi_search_range(&range_a1, &range_a2);
            iter = std::search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", found_a ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(found_a == !arr100_digi_it_done(&range_a1));
            if (found_a)
                assert(iter != b.end());
            else
                assert(iter == b.end());
            CHECK_ITER(range_a1, b, iter);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_arr100(&a);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            it = arr100_digi_search_n(&a, count, digi_init(value));
            iter = std::search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(it, b, iter);
            LOG("found %s at %zu\n", arr100_digi_it_done(&it) ? "no" : "yes", arr100_digi_it_index(&it));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            print_arr100_range(&range_a1);
            pos = arr100_digi_search_n_range(&range_a1, count, digi_init(value));
            iter = std::search_n(first_b1, last_b1, count, DIGI{value});
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s at %zu\n", arr100_digi_it_done(pos) ? "no" : "yes", arr100_digi_it_index(pos));
            break;
        }
        case TEST_FIND_FIRST_OF: {
            print_arr100(&a);
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = TEST_RAND(TEST_MAX_VALUE);
                bb[i] = DIGI{value};
                aa.vector[i] = digi_init(value);
            }
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            it = arr100_digi_find_first_of(&a, &range_a2);
            iter = std::find_first_of(b.begin(), b.end(), first_b2, last_b2);
            print_arr100(&aa);
            LOG("=> %zu vs %ld\n", arr100_digi_it_index(&it), iter - b.begin());
            CHECK_ITER(it, b, iter);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < N; i++)
            {
                value = TEST_RAND(TEST_MAX_VALUE);
                bb[i] = DIGI{value};
                aa.vector[i] = digi_init(value);
            }
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr100(&a);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            print_arr100(&aa);

            found_a = arr100_digi_find_first_of_range(&range_a1, &range_a2);
            iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                iter != last_b1 ? "yes" : "no", range_a1.ref - a.vector,
                iter - b.begin());
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            // CHECK_RANGE(range_a1, it, last_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < 4; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            range_a2 = arr100_digi_begin(&aa);
            print_arr100(&a);
            print_arr100(&aa);
            range_a2.end = range_a2.ref + 4;
            it = arr100_digi_find_end(&a, &range_a2);
            iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.begin() + 4);
            found_a = !arr100_digi_it_done(&it);
            found_b = iter != b.end();
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                iter - b.begin());
//#ifdef DEBUG
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
//#else
//            if (found_a != found_b)
//                printf("arr100_digi_find_end => %s/%s, %ld/%ld FAIL\n",
//                       found_a ? "yes" : "no",
//                       found_b ? "yes" : "no", it.ref - a.vector,
//                       iter - b.begin());
//#endif
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < 4; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            range_a2 = arr100_digi_begin(&aa);
            range_a2.end = range_a2.ref + 4;
#if __cpp_lib_erase_if >= 202002L
            it = arr100_digi_find_end_range(&range_a1, &range_a2);
            iter = std::find_end(first_b1, last_b1, bb.begin(), bb.begin() + 4);
            CHECK_ITER(it, b, iter);
#endif
            arr100_digi_free(&aa);
            break;
        }
        case TEST_LOWER_BOUND: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            it = arr100_digi_lower_bound(&a, digi_init(value));
            iter = std::lower_bound(b.begin(), b.end(), DIGI{value});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_UPPER_BOUND: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            it = arr100_digi_upper_bound(&a, digi_init(value));
            iter = std::upper_bound(b.begin(), b.end(), DIGI{value});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = arr100_digi_lower_bound_range(&range_a1, digi_init(value));
            iter = std::lower_bound(first_b1, last_b1, DIGI{value});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = arr100_digi_upper_bound_range(&range_a1, digi_init(value));
            iter = std::upper_bound(first_b1, last_b1, DIGI{value});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_BINARY_SEARCH: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            value = pick_random(&a);
            found_a = arr100_digi_binary_search(&a, digi_init(value));
            found_b = std::binary_search(b.begin(), b.end(), DIGI{value});
            LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            found_a = arr100_digi_binary_search_range(&range_a1, digi_init(value));
            found_b = std::binary_search(first_b1, last_b1, DIGI{value});
            LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_INCLUDES: {
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < 100; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            print_arr100(&a);
            print_arr100(&aa);
            //arr100_digi_it range_a2 = arr100_digi_begin(&aa);
            //range_a2.end = range_a2.ref + 4;
            found_a = arr100_digi_includes(&a, &aa);
            found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
            LOG("%d vs %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_INCLUDES_RANGE: {
            aa = arr100_digi_init_from(&a);
            for (int i = 0; i < 100; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = arr100_digi_includes_range(&range_a1, &range_a2);
            found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
            LOG("%d vs %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_IS_SORTED: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr100(&a);
            found_a = arr100_digi_is_sorted(&range_a1);
            found_b = std::is_sorted(first_b1, last_b1);
            LOG("a_yes: %d b_yes %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_IS_SORTED_UNTIL: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr100_range(&range_a1);
            range_a2 = range_a1;
            range_a2.ref = range_a1.end;
            pos = arr100_digi_is_sorted_until(&range_a1, &range_a2);
            iter = std::is_sorted_until(first_b1, last_b1);
            CHECK_ITER(*pos, b, iter);
            break;
        }
        case TEST_REVERSE: {
            print_arr100(&a);
            arr100_digi_reverse(&a);
            std::reverse(b.begin(), b.end());
            print_arr100(&a);
            print_array(b);
            CHECK(a, b);
            break;
        }
        case TEST_REVERSE_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_arr100(&a);
            arr100_digi_reverse_range(&range_a1);
            std::reverse(first_b1, last_b1);
            print_arr100(&a);
            CHECK(a, b);
            break;
        }
        case TEST_INTERSECTION_RANGE: {
            gen_arrays(&aa, bb);
            arr100_digi_sort(&a);
            arr100_digi_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_arr100_range(&range_a1);
            print_arr100_range(&range_a2);
            it = arr100_digi_intersection_range(&range_a1, &range_a2);
            LOG("CTL => it (%zu)\n", arr100_digi_it_distance_range(&it));
            print_arr100_range(&it);

            std::vector<DIGI> bbb_;
            LOG("STL b + bb\n");
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb\n");
            int i = 0;
            for (auto &d : bbb_) bbb[i++] = *d;
            print_array(bbb);
            if (!arr100_digi_it_done(&it))
                CHECK(*it.container, bbb);
#endif
            arr100_digi_free(it.container);
            free (it.container);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_DIFFERENCE_RANGE: {
            gen_arrays(&aa, bb);
            arr100_digi_sort(&a);
            arr100_digi_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            //LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
            print_arr100_range(&range_a1);
            print_arr100_range(&range_a2);
            it = arr100_digi_difference_range(&range_a1, &range_a2);
            LOG("CTL => it (%zu)\n", arr100_digi_it_distance_range(&it));
            print_arr100_range(&it);

            std::vector<DIGI> bbb_;
            LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb (%zu)\n", bbb.size());
            int i = 0;
            for (auto &d : bbb_) bbb[i++] = *d;
            print_array(bbb);
            if (!arr100_digi_it_done(&it))
                CHECK(*it.container, bbb);
#endif
            arr100_digi_free(it.container);
            free (it.container);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
            gen_arrays(&aa, bb);
            arr100_digi_sort(&a);
            arr100_digi_sort(&aa);
            std::sort(b.begin(), b.end());
            std::sort(bb.begin(), bb.end());
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_arr100_range(&range_a1);
            print_arr100_range(&range_a2);
            it = arr100_digi_symmetric_difference_range(&range_a1, &range_a2);
            LOG("CTL => it (%zu)\n", arr100_digi_it_distance_range(&it));
            print_arr100_range(&it);

            std::vector<DIGI> bbb_;
            LOG("STL b + bb\n");
            print_array(b);
            print_array(bb);
#ifndef _MSC_VER
            std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb_));
            LOG("STL => bbb\n");
            int i = 0;
            for (auto &d : bbb_) bbb[i++] = *d;
            print_array(bbb);
            if (!arr100_digi_it_done(&it))
                CHECK(*it.container, bbb);
#endif
            arr100_digi_free(it.container);
            free (it.container);
            arr100_digi_free(&aa);
            break;
        }

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
    FINISH_TEST(__FILE__);
}

#endif // C++11
