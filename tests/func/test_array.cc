#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define N 100
#include <ctl/array.h>

#include <algorithm>
#include <array>

#define N 100

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
        assert(arr100_digi_size(&_x) == _y.size());                                                                    \
        assert(arr100_digi_empty(&_x) == _y.empty());                                                                  \
        assert(*_y.front().value == *arr100_digi_front(&_x)->value);                                                   \
        assert(*_y.back().value == *arr100_digi_back(&_x)->value);                                                     \
        std::array<DIGI, 100>::iterator _iter = _y.begin();                                                            \
        foreach (arr100_digi, &_x, _it)                                                                                \
        {                                                                                                              \
            assert(*_it.ref->value == *_iter->value);                                                                  \
            _iter++;                                                                                                   \
        }                                                                                                              \
        digi *_ref = arr100_digi_front(&_x);                                                                           \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*(_ref->value) == *_d.value);                                                                       \
            _ref++;                                                                                                    \
        }                                                                                                              \
        for (size_t _i = 0; _i < _y.size(); _i++)                                                                      \
            assert(*_y.at(_i).value == *arr100_digi_at(&_x, _i)->value);                                               \
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
    INIT_TEST_LOOPS(15);

    arr100_digi a = arr100_digi_init();
    a.compare = digi_compare;
    a.equal = digi_equal;
    std::array<DIGI, 100> b;
    for (int i = 0; i < N; i++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE);
        b[i] = DIGI{value};
        a.vector[i] = digi_init(value);
    }

    for (size_t loop = 0; loop < loops; loop++)
    {

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
    TEST(BINARY_SEARCH_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(SYMMETRIC_DIFFERENCE) /* 49*/                                                                                 \
    TEST(INTERSECTION)                                                                                                 \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

        enum
        {
            FOREACH_METH(GENERATE_ENUM)
#ifdef DEBUG
                FOREACH_DEBUG(GENERATE_ENUM)
#endif
                    TEST_TOTAL
        };
#ifdef DEBUG
        static const char *test_names[] = {FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif
        int which = TEST_RAND(TEST_TOTAL);
        if (test >= 0 && test < (int)TEST_TOTAL)
            which = test;
        LOG("TEST=%d %s\n", which, test_names[which]);
        switch (which)
        {
        case TEST_SELF: {
            for (int i = 0; i < N; i++)
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
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
            const int value = TEST_RAND(TEST_MAX_VALUE);
            b.fill(DIGI{value});
            arr100_digi_fill(&a, digi_init(value));
            break;
        }
        case TEST_FILL_N: {
            const int n = TEST_RAND(N);
            const int value = TEST_RAND(TEST_MAX_VALUE);
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
            arr100_digi aa = arr100_digi_copy(&a);
            std::array<DIGI, 100> bb = b;
            CHECK(aa, bb);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_ASSIGN: {
            const int value = TEST_RAND(TEST_MAX_VALUE);
            size_t assign_size = TEST_RAND(N - 1);
            arr100_digi_assign(&a, assign_size, digi_init(value));
            for (size_t i = 0; i < assign_size; i++)
                b[i] = DIGI{value};
            break;
        }
        case TEST_SWAP: {
            arr100_digi aa = arr100_digi_copy(&a);
            arr100_digi aaa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb = b;
            std::array<DIGI, 100> bbb;
            arr100_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            arr100_digi_free(&aaa);
            break;
        }
        case TEST_EQUAL: {
            arr100_digi aa = arr100_digi_copy(&a);
            std::array<DIGI, 100> bb = b;
            assert(arr100_digi_equal(&a, &aa));
            assert(b == bb);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            arr100_digi_it r1a;
            std::array<DIGI, 100>::iterator r1b, last1_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            size_t index = TEST_RAND(N);
            int value = *a.vector[index].value;
            LOG("equal_value %d\n", value);
            print_arr100(&a);
            bool same_a = arr100_digi_equal_value(&r1a, digi_init(value));
            bool same_b = r1b != last1_b;
            for (; r1b != last1_b; r1b++)
            {
                if (value != *(*r1b).value)
                {
                    same_b = false;
                    break;
                }
            }
            LOG("same_a: %d same_b: %d\n", (int)same_a, (int)same_b);
            assert(same_a == same_b);
            break;
        }
        case TEST_EQUAL_RANGE: {
            arr100_digi aa = arr100_digi_copy(&a);
            std::array<DIGI, 100> bb = b;
            arr100_digi_it r1a, r2a;
            std::array<DIGI, 100>::iterator r1b, last1_b, r2b, last2_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            get_random_iters(&aa, &r2a, bb, r2b, last2_b);
            bool same_a = arr100_digi_equal_range(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            bool same_b = std::equal(r1b, last1_b, r2b, last2_b);
            LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
            assert(same_a == same_b);
#else
            bool same_b = std::equal(r1b, last1_b, r2b);
            LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
            if (same_a != same_b)
                printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND: {
            const size_t index = TEST_RAND(N);
            int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : *arr100_digi_at(&a, index)->value;
            digi key = digi_init(value);
            digi *aa = arr100_digi_find(&a, key);
            auto bb = std::find(b.begin(), b.end(), DIGI{value});
            bool found_a = aa != NULL;
            bool found_b = bb != b.end();
            assert(found_a == found_b);
            if (found_a && found_b)
                assert(*aa->value == *bb->value);
            digi_free(&key);
            break;
        }
        case TEST_FIND_RANGE: {
            int vb = pick_random(&a);
            digi key = digi_init(vb);
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool found_a = arr100_digi_find_range(&first_a, key);
            auto it = std::find(first_b, last_b, vb);
            LOG("%d at [%ld]\n", *first_a.ref->value, first_a.ref - a.vector);
            if (found_a)
                assert(it != last_b);
            else
                assert(it == last_b);
            CHECK_RANGE(first_a, it, last_b);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            arr100_digi_it i = arr100_digi_find_if_range(&first_a, digi_is_odd);
            auto it = std::find_if(first_b, last_b, DIGI_is_odd);
            print_arr100(&a);
            print_array(b);
            LOG("%d at [%ld]\n", *i.ref->value, i.ref - a.vector);
            CHECK_RANGE(i, it, last_b);
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            arr100_digi_it i = arr100_digi_find_if_not_range(&first_a, digi_is_odd);
            auto it = std::find_if_not(first_b, last_b, DIGI_is_odd);
            LOG("%d at [%ld]\n", *i.ref->value, i.ref - a.vector);
            CHECK_RANGE(i, it, last_b);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = arr100_digi_all_of_range(&first_a, digi_is_odd);
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
        case TEST_NONE_OF_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = arr100_digi_none_of_range(&first_a, digi_is_odd);
            bool bb = std::none_of(first_b, last_b, DIGI_is_odd);
            if (aa != bb)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t numa = arr100_digi_count_if_range(&first_a, digi_is_odd);
            size_t numb = std::count_if(first_b, last_b, DIGI_is_odd);
            if (numa != numb)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d FAIL\n", (int)numa, (int)numb);
                fail++;
            }
            assert(numa == numb); // fails. off by one, counts one too much
            break;
        }
        case TEST_COUNT_RANGE: {
            int test_value = 0;
            int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : test_value;
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            // used to fail with 0,0 of 0
            size_t numa = arr100_digi_count_range(&first_a, digi_init(v));
            size_t numb = std::count(first_b, last_b, DIGI{v});
            assert(numa == numb);
            break;
        }
        case TEST_ANY_OF: {
            bool is_a = arr100_digi_any_of(&a, digi_is_odd);
            bool is_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = arr100_digi_any_of_range(&first_a, digi_is_odd);
            bool bb = std::any_of(first_b, last_b, DIGI_is_odd);
            if (aa != bb)
            {
                print_arr100(&a);
                print_array(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_FIND_IF: {
            arr100_digi_it aa = arr100_digi_find_if(&a, digi_is_odd);
            auto bb = std::find_if(b.begin(), b.end(), DIGI_is_odd);
            if (bb == b.end())
                assert(arr100_digi_it_done(&aa));
            else
                assert(*(aa.ref->value) == *bb->value);
            break;
        }
        case TEST_FIND_IF_NOT: {
            arr100_digi_it aa = arr100_digi_find_if_not(&a, digi_is_odd);
            auto bb = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
            if (bb == b.end())
                assert(arr100_digi_it_done(&aa));
            else
                assert(*(aa.ref->value) == *bb->value);
            break;
        }
        case TEST_ALL_OF: {
            bool is_a = arr100_digi_all_of(&a, digi_is_odd);
            bool is_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF: {
            bool is_a = arr100_digi_none_of(&a, digi_is_odd);
            bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_COUNT: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            int aa = arr100_digi_count(&a, digi_init(key));
            int bb = std::count(b.begin(), b.end(), DIGI{key});
            assert(aa == bb);
            break;
        }
        case TEST_COUNT_IF: {
            size_t count_a = arr100_digi_count_if(&a, digi_is_odd);
            size_t count_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
            assert(count_a == count_b);
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
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            digi_generate_reset();
            arr100_digi_generate_range(&first_a, digi_generate);
            digi_generate_reset();
            std::generate(first_b, last_b, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: {
            arr100_digi aa = arr100_digi_transform(&a, digi_untrans);
            std::array<DIGI, 100> bb;
            std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
            CHECK(aa, bb);
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_IT: {
            print_arr100(&a);
            arr100_digi_it pos = arr100_digi_begin(&a);
            arr100_digi_it_advance(&pos, 1);
            arr100_digi aa = arr100_digi_transform_it(&a, &pos, digi_bintrans);
            // the last one is unitialized
            arr100_digi_set(&aa, 99, digi_init(0));
            print_arr100(&aa);
            std::array<DIGI, 100> bb;
            std::transform(b.begin(), b.end() - 1, b.begin() + 1, bb.begin(), DIGI_bintrans);
            print_array(bb);
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
#ifdef DEBUG
        case TEST_GENERATE_N_RANGE: // TEST=32
        {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t off = first_b - b.begin();
            size_t count = TEST_RAND(20 - off);
            digi_generate_reset();
            arr100_digi_generate_n_range(&first_a, count, digi_generate);
            digi_generate_reset();
            std::generate_n(first_b, count, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            arr100_digi aa = arr100_digi_init_from(&a);
            arr100_digi_it dest = arr100_digi_begin(&aa);
            arr100_digi_it it = arr100_digi_transform_range(&first_a, dest, digi_untrans);
            std::array<DIGI, 100> bb;
            auto iter = std::transform(first_b, last_b, b.begin() + 1, bb.begin(), DIGI_bintrans);
            CHECK_RANGE(it, iter, last_b);
            // CHECK_ITER(it, bb, iter);
            CHECK(aa, bb);
            // heap use-after-free
            CHECK(a, b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            arr100_digi aa = arr100_digi_copy_if(&a, digi_is_odd);
            std::array<DIGI, 100> bb = b;
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
            arr100_digi_it range;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            arr100_digi aa = arr100_digi_copy_if_range(&range, digi_is_odd);
            size_t i = arr100_digi_it_index(&range);
            std::array<DIGI, 100> bb = b;
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
            arr100_digi aa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb;
            for (int i = 0; i < N; i++)
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                bb[i] = DIGI{value};
                aa.vector[i] = digi_init(value);
            }
            arr100_digi_it b1, b2;
            b1 = arr100_digi_begin(&a);
            b2 = arr100_digi_begin(&aa);
            arr100_digi_it r1a, r2a;
            std::array<DIGI, 100>::iterator r1b, last1_b, r2b, last2_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            get_random_iters(&aa, &r2a, bb, r2b, last2_b);
            /*bool found_a = */ arr100_digi_mismatch(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
#else
            auto pair = std::mismatch(r1b, last1_b, r2b);
#endif
            int d1a = arr100_digi_it_distance(&b1, &r1a);
            int d2a = arr100_digi_it_distance(&b2, &r2a);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == std::distance(b.begin(), pair.first));
            assert(d2a == std::distance(bb.begin(), pair.second));
            arr100_digi_free(&aa);
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_arr100(&a);
            arr100_digi_it aa = arr100_digi_adjacent_find(&a);
            auto bb = std::adjacent_find(b.begin(), b.end());
            CHECK_ITER(aa, b, bb);
            LOG("found %s\n", arr100_digi_it_done(&aa) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            arr100_digi_it range;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            print_arr100(&a);
            arr100_digi_it *aa = arr100_digi_adjacent_find_range(&range);
            auto bb = std::adjacent_find(first_b, last_b);
            CHECK_RANGE(*aa, bb, last_b);
            // CHECK_ITER(*aa, b, bb);
            LOG("found %s\n", arr100_digi_it_done(aa) ? "no" : "yes");
            break;
        }
        case TEST_SEARCH: // 42
        {
            print_arr100(&a);
            arr100_digi aa = arr100_digi_copy(&a);
            std::array<DIGI, 100> bb = b;
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&aa, &first_a, bb, first_b, last_b);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b - bb.begin();
                arr100_digi_set(&aa, i, digi_init(0));
                bb[i] = DIGI{0};
            }
            // print_arr100(aa);
            arr100_digi_it found_a = arr100_digi_search(&a, &first_a);
            auto found_b = std::search(b.begin(), b.end(), first_b, last_b);
            LOG("found a: %s\n", arr100_digi_it_done(&found_a) ? "no" : "yes");
            LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
            CHECK_RANGE(found_a, found_b, b.end());
            arr100_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            arr100_digi aa = arr100_digi_copy(&a);
            std::array<DIGI, 100> bb = b;
            arr100_digi_it needle, range;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&aa, &needle, bb, first_b, last_b);
            if (TEST_RAND(2))
            { // 50% unsuccessful
                size_t i = first_b - bb.begin();
                arr100_digi_set(&aa, i, digi_init(0));
                bb[i] = DIGI{0};
            }
            // print_arr100_range(needle);
            range = arr100_digi_begin(&a);
            bool found = arr100_digi_search_range(&range, &needle);
            auto iter = std::search(b.begin(), b.end(), first_b, last_b);
            LOG("found a: %s\n", found ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(found == !arr100_digi_it_done(&range));
            if (found)
                assert(iter != b.end());
            else
                assert(iter == b.end());
            CHECK_ITER(range, b, iter);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_arr100(&a);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            arr100_digi_it aa = arr100_digi_search_n(&a, count, digi_init(value));
            auto bb = std::search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(aa, b, bb);
            LOG("found %s at %zu\n", arr100_digi_it_done(&aa) ? "no" : "yes", arr100_digi_it_index(&aa));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            arr100_digi_it range;
            std::array<DIGI,100>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            //print_arr100_range(&range);
            arr100_digi_it *aa = arr100_digi_search_n_range(&range, count, digi_init(value));
            auto bb = std::search_n(first_b, last_b, count, DIGI{value});
            CHECK_RANGE(*aa, bb, last_b);
            LOG("found %s at %zu\n", arr100_digi_it_done(aa) ? "no" : "yes", arr100_digi_it_index(aa));
            break;
        }
        case TEST_FIND_FIRST_OF: {
            print_arr100(&a);
            arr100_digi aa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb;
            for (int i = 0; i < N; i++)
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                bb[i] = DIGI{value};
                aa.vector[i] = digi_init(value);
            }
            arr100_digi_it s_first;
            std::array<DIGI, 100>::iterator s_first_b, s_last_b;
            get_random_iters(&aa, &s_first, bb, s_first_b, s_last_b);
            arr100_digi_it it = arr100_digi_find_first_of(&a, &s_first);
            auto iter = std::find_first_of(b.begin(), b.end(), s_first_b, s_last_b);
            print_arr100(&aa);
            LOG("=> %zu vs %ld\n", arr100_digi_it_index(&it), iter - b.begin());
            CHECK_ITER(it, b, iter);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            arr100_digi aa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb;
            for (int i = 0; i < N; i++)
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                bb[i] = DIGI{value};
                aa.vector[i] = digi_init(value);
            }
            arr100_digi_it first_a, s_first;
            std::array<DIGI, 100>::iterator first_b, last_b, s_first_b, s_last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            print_arr100(&a);
            get_random_iters(&aa, &s_first, bb, s_first_b, s_last_b);
            print_arr100(&aa);

            bool found_a = arr100_digi_find_first_of_range(&first_a, &s_first);
            auto it = std::find_first_of(first_b, last_b, s_first_b, s_last_b);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", it != last_b ? "yes" : "no", first_a.ref - a.vector,
                it - b.begin());
            if (found_a)
                assert(it != last_b);
            else
                assert(it == last_b);
            // CHECK_RANGE(first_a, it, last_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            arr100_digi aa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb;
            for (int i = 0; i < 4; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            arr100_digi_it s_first = arr100_digi_begin(&aa);
            print_arr100(&a);
            print_arr100(&aa);
            s_first.end = s_first.ref + 4;
            arr100_digi_it it = arr100_digi_find_end(&a, &s_first);
            auto iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.begin() + 34);
            bool found_a = !arr100_digi_it_done(&it);
            bool found_b = iter != b.end();
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                iter - b.begin());
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
            arr100_digi_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            arr100_digi_it first_a, s_first;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            arr100_digi aa = arr100_digi_init_from(&a);
            std::array<DIGI, 100> bb;
            for (int i = 0; i < 4; i++)
            {
                bb[i] = DIGI{i};
                aa.vector[i] = digi_init(i);
            }
            s_first = arr100_digi_begin(&aa);
            s_first.end = s_first.ref + 4;
#if __cpp_lib_erase_if >= 202002L
            first_a = arr100_digi_find_end_range(&first_a, &s_first);
            auto it = std::find_end(first_b, last_b, bb.begin(), bb.begin() + 4);
            CHECK_ITER(first_a, b, it);
#endif
            arr100_digi_free(&aa);
            break;
        }
        case TEST_LOWER_BOUND: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            int key = pick_random(&a);
            arr100_digi_it aa = arr100_digi_lower_bound(&a, digi_init(key));
            auto bb = std::lower_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_UPPER_BOUND: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            int key = pick_random(&a);
            arr100_digi_it aa = arr100_digi_upper_bound(&a, digi_init(key));
            auto bb = std::upper_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            arr100_digi_it *aa = arr100_digi_lower_bound_range(&first_a, digi_init(key));
            std::array<DIGI, 100>::iterator bb = std::lower_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            arr100_digi_it first_a;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            arr100_digi_it *aa = arr100_digi_upper_bound_range(&first_a, digi_init(key));
            std::array<DIGI, 100>::iterator bb = std::upper_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_BINARY_SEARCH: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            int key = pick_random(&a);
            bool found_a = arr100_digi_binary_search(&a, digi_init(key));
            bool found_b = std::binary_search(b.begin(), b.end(), DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            arr100_digi_sort(&a);
            std::sort(b.begin(), b.end());
            arr100_digi_it range;
            std::array<DIGI, 100>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            int key = pick_random(&a);
            bool found_a = arr100_digi_binary_search_range(&range, digi_init(key));
            bool found_b = std::binary_search(first_b, last_b, DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
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

    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
