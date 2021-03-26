#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#include <ctl/deque.h>

#include <deque>
#include <algorithm>
#include <numeric>
#include <vector>
#if __cplusplus >= 201703L
#include <random>
#endif

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH_BACK)                                                                                                    \
    TEST(POP_BACK)                                                                                                     \
    TEST(PUSH_FRONT)                                                                                                   \
    TEST(POP_FRONT)                                                                                                    \
    TEST(CLEAR)                                                                                                        \
    TEST(ERASE)                                                                                                        \
    TEST(ERASE_INDEX)                                                                                                  \
    TEST(ERASE_IF)                                                                                                     \
    TEST(ERASE_RANGE)                                                                                                  \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_INDEX)                                                                                                 \
    TEST(INSERT_COUNT)                                                                                                 \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(EMPLACE)                                                                                                      \
    TEST(EMPLACE_FRONT)                                                                                                \
    TEST(EMPLACE_BACK)                                                                                                 \
    TEST(RESIZE)                                                                                                       \
    TEST(SHRINK_TO_FIT)                                                                                                \
    TEST(SORT)                                                                                                         \
    TEST(RANGED_SORT)                                                                                                  \
    TEST(SORT_RANGE)                                                                                                   \
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
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(DIFFERENCE_RANGE)                                                                                             \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_RANGE)                                                                                               \
    TEST(GENERATE_N)                                                                                                   \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM)                                                                                                    \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(TRANSFORM_IT_RANGE)                                                                                           \
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
    TEST(SHUFFLE)                                                                                                      \
    TEST(SHUFFLE_RANGE)                                                                                                \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)                                                                                                \
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
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(REVERSE)                                                                                                      \
    TEST(REVERSE_RANGE)                                                                                                \
    TEST(ASSIGN_GENERIC)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(UNIQUE)                                                                                                       \
    TEST(UNIQUE_RANGE)                                                                                                 \
    TEST(INSERT_GENERIC)

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
#endif
// clang-format on


#define ADJUST_CAP(m, a, b)
void print_deq(deq_digi *a)
{
    for (size_t i = 0; i < a->size; i++)
        printf("%d ", *deq_digi_at(a, i)->value);
    printf("\n");
}

void print_deq_range(deq_digi_it it)
{
    deq_digi *a = it.container;
    size_t i;
    size_t i1 = it.index;
    size_t i2 = it.end;
    for (i = 0; i < i1; i++)
        printf("%d ", *deq_digi_at(a, i)->value);
    printf("[");
    for (i = i1; i < i2; i++)
        printf("%d ", *deq_digi_at(a, i)->value);
    printf(") ");
    for (i = i2; i < a->size; i++)
        printf("%d ", *deq_digi_at(a, i)->value);
    printf("\n");
}

void print_deque(std::deque<DIGI> &b)
{
    for (size_t i = 0; i < b.size(); i++)
    {
        DIGI val = b.at(i);
        // DIGI.hh is not as stable as the CTL
        if (val.value)
            printf("%d ", *val.value);
        else
            printf("NULL, ");
    }
    printf("\n");
}

#ifdef DEBUG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 15
#define TEST_MAX_VALUE 1000
#else
#define TEST_MAX_VALUE INT_MAX
#endif

#ifndef DEBUG
#define print_deq(x)
#define print_deq_range(x)
#define print_deque(x)

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        assert(deq_digi_empty(&_x) == _y.empty());                                                                     \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            if (_y.front().value)                                                                                      \
                assert(*_y.front().value == *deq_digi_front(&_x)->value);                                              \
            if (_y.back().value)                                                                                       \
                assert(*_y.back().value == *deq_digi_back(&_x)->value);                                                \
        }                                                                                                              \
        std::deque<DIGI>::iterator _iter = _y.begin();                                                                 \
        foreach (deq_digi, &_x, _it)                                                                                   \
        {                                                                                                              \
            /* libstdc++ may be corrupt. libc++ not */                                                                 \
            if (_iter->value)                                                                                          \
                assert(*_it.ref->value == *_iter->value);                                                              \
            _iter++;                                                                                                   \
        }                                                                                                              \
        size_t _i = 0;                                                                                                 \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            digi *_ref = deq_digi_at(&_x, _i++);                                                                       \
            if (_d.value)                                                                                              \
                assert(*_ref->value == *_d.value);                                                                     \
        }                                                                                                              \
        for (_i = 0; _i < _y.size(); _i++)                                                                             \
            assert(*_y.at(_i).value == *deq_digi_at(&_x, _i)->value);                                                  \
    }
#define CHECK_ITER(cit, _y, iter) assert((long)(cit).index == std::distance(_y.begin(), iter))

#else // DEBUG

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        assert(deq_digi_empty(&_x) == _y.empty());                                                                     \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            if (_y.front().value)                                                                                      \
                assert(*_y.front().value == *deq_digi_front(&_x)->value);                                              \
            else                                                                                                       \
                fprintf(stderr, "STL empty front value\n");                                                            \
            if (_y.back().value)                                                                                       \
                assert(*_y.back().value == *deq_digi_back(&_x)->value);                                                \
            else                                                                                                       \
                fprintf(stderr, "STL empty back value\n");                                                             \
        }                                                                                                              \
        std::deque<DIGI>::iterator _iter = _y.begin();                                                                 \
        foreach (deq_digi, &_x, _it)                                                                                   \
        {                                                                                                              \
            if (*_it.ref->value != *_iter->value)                                                                      \
                fprintf(stderr, "CTL %d at %zu vs STL %d\n", *_it.ref->value, _it.index, *_iter->value);               \
            assert(*_it.ref->value == *_iter->value);                                                                  \
            _iter++;                                                                                                   \
        }                                                                                                              \
        size_t _i = 0;                                                                                                 \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            digi *_ref = deq_digi_at(&_x, _i++);                                                                       \
            if (_d.value)                                                                                              \
                assert(*_ref->value == *_d.value);                                                                     \
        }                                                                                                              \
        for (_i = 0; _i < _y.size(); _i++)                                                                             \
            assert(*_y.at(_i).value == *deq_digi_at(&_x, _i)->value);                                                  \
    }
#define CHECK_ITER(cit, _y, iter)                                                                                      \
    {                                                                                                                  \
        long _dist = std::distance(_y.begin(), iter);                                                                  \
        if ((long)(cit).index != _dist)                                                                                \
            fprintf(stderr, "CTL index %zu vs STL %zu\n", (cit).index, _dist);                                         \
        assert((long)(cit).index == _dist);                                                                            \
    }
#endif

#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!deq_digi_it_done(&(_it)))                                                                                     \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*((_it).ref->value) == *(*_iter).value);                                                                \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

int middle(deq_digi *a)
{
    if (!a->size)
        return 0;
    return (*deq_digi_front(a)->value - *deq_digi_back(a)->value) / 2;
}

int median(deq_digi *a)
{
    deq_digi_it it = deq_digi_begin(a);
    deq_digi_it_advance(&it, a->size / 2);
    return a->size ? *it.ref->value : 0;
}

int random_element(deq_digi *a)
{
    const size_t index = TEST_RAND(a->size);
    if (!a->size)
        return 0;
    digi *vp = deq_digi_at(a, index);
    return *vp->value;
}

int pick_random(deq_digi *a)
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
    return 0;
}

static void get_random_iters(deq_digi *a, deq_digi_it *first_a, std::deque<DIGI> &b,
                             std::deque<DIGI>::iterator &first_b, std::deque<DIGI>::iterator &last_b)
{
    deq_digi_it last_a;
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        deq_digi_it it1 = deq_digi_begin(a);
        first_b = b.begin();
        deq_digi_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            last_a = deq_digi_end(a);
            last_b = b.end();
        }
        else
        {
            deq_digi_it it2 = deq_digi_begin(a);
            last_b = b.begin();
            deq_digi_it_advance(&it2, r2);
            last_b += r2;
            last_a = it2;
        }
    }
    else
    {
        deq_digi_it end = deq_digi_end(a);
        *first_a = end;
        last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.index;
}

// TESTS DEQ STABILITY WITH SELF CLEANUP.
// EDGE CASE:
//     MISC CALLS TO POP/PUSH FRONT/BACK WITH
//     DEQUE SIZE 1 CAUSED HEAP USE AFTER FREE ISSUES.

void test_capacity_edge_case(void)
{
    {
        deq_digi a = deq_digi_init();
        deq_digi_push_back(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_back(&a);
        assert(a.capacity == 1);
        deq_digi_push_back(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_back(&a);
        assert(a.capacity == 1);
        deq_digi_free(&a);
    }
    {
        deq_digi a = deq_digi_init();
        deq_digi_push_back(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_front(&a);
        assert(a.capacity == 1);
        deq_digi_push_back(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_front(&a);
        assert(a.capacity == 1);
        deq_digi_free(&a);
    }
    {
        deq_digi a = deq_digi_init();
        deq_digi_push_front(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_front(&a);
        assert(a.capacity == 1);
        deq_digi_push_front(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_front(&a);
        assert(a.capacity == 1);
        deq_digi_free(&a);
    }
    {
        deq_digi a = deq_digi_init();
        deq_digi_push_front(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_back(&a);
        assert(a.capacity == 1);
        deq_digi_push_front(&a, digi_init(1));
        assert(a.capacity == 1);
        deq_digi_pop_back(&a);
        assert(a.capacity == 1);
        deq_digi_free(&a);
    }
}
void test_random_work_load(void)
{
    deq_digi a = deq_digi_init();
    std::deque<DIGI> b;
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for (size_t i = 0; i < loops; i++)
        switch (TEST_RAND(5))
        {
        case 0: {
            assert(a.size == b.size());
            deq_digi_push_front(&a, digi_init(1));
            b.push_front(DIGI{1});
            assert(a.size == b.size());
            break;
        }
        case 1: {
            assert(a.size == b.size());
            deq_digi_push_back(&a, digi_init(1));
            b.push_back(DIGI{1});
            assert(a.size == b.size());
            break;
        }
        case 2: {
            assert(a.size == b.size());
            if (a.size)
                deq_digi_pop_front(&a);
            if (b.size())
                b.pop_front();
            assert(a.size == b.size());
            break;
        }
        case 3: {
            assert(a.size == b.size());
            if (a.size)
                deq_digi_pop_back(&a);
            if (b.size())
                b.pop_back();
            assert(a.size == b.size());
            break;
        }
        case 4: {
            assert(a.size == b.size());
            deq_digi_clear(&a);
            b.clear();
            assert(a.size == b.size());
            break;
        }
        }
    deq_digi_free(&a);
}

static void setup_deque(deq_digi *a, std::deque<DIGI> &b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = deq_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for (size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        deq_digi_push_back(a, digi_init(vb));
        b.push_back(DIGI{vb});
    }
}

int main(void)
{
    int fail = 0;
    test_capacity_edge_case();
    test_random_work_load();
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        LOG("loop %u, size %zu\n", loop, size);
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for (size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            deq_digi a, aa, aaa;
            std::deque<DIGI> b, bb, bbb;
            deq_digi_it range_a1, range_a2, it;
            deq_digi_it *pos;
            std::deque<DIGI>::iterator first_b1, last_b1, first_b2, last_b2, iter;
            bool found_a, found_b;
            size_t num_a, num_b;
            int value = TEST_RAND(TEST_MAX_VALUE);
            const size_t index = TEST_RAND(size);
#if __cplusplus >= 201703L
            std::default_random_engine rng {seed};
#endif

            a = deq_digi_init();
            a.compare = digi_compare;
            a.equal = digi_equal;

            if (mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                deq_digi_resize(&a, size, digi_init(0));
                b.resize(size);
                for (size_t i = 0; i < size; i++)
                {
                    value = TEST_RAND(TEST_MAX_VALUE);
                    deq_digi_set(&a, i, digi_init(value));
                    b[i] = DIGI{value};
                }
            }
            if (mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for (size_t pushes = 0; pushes < size; pushes++)
                {
                    value = TEST_RAND(TEST_MAX_VALUE);
                    deq_digi_push_back(&a, digi_init(value));
                    b.push_back(DIGI{value});
                }
            }
            int which;
            if (tests.size)
            {
                which = *queue_int_front(&tests);
                if (mode == MODE_TOTAL-1)
                    queue_int_pop(&tests);
            }
            else
                which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
            LOG("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
            RECORD_WHICH;
            switch (which)
            {
            case TEST_PUSH_BACK: {
                b.push_back(DIGI{value});
                deq_digi_push_back(&a, digi_init(value));
                CHECK(a, b);
                break;
            }
            case TEST_POP_BACK: {
                if (a.size > 0)
                {
                    b.pop_back();
                    deq_digi_pop_back(&a);
                }
                CHECK(a, b);
                break;
            }
            case TEST_PUSH_FRONT: {
                b.push_front(DIGI{value});
                deq_digi_push_front(&a, digi_init(value));
                CHECK(a, b);
                break;
            }
            case TEST_POP_FRONT: {
                if (a.size > 0)
                {
                    b.pop_front();
                    deq_digi_pop_front(&a);
                    CHECK(a, b);
                }
                break;
            }
            case TEST_CLEAR: {
                b.clear();
                deq_digi_clear(&a);
                CHECK(a, b);
                break;
            }
            case TEST_ERASE: {
                if (a.size > 0)
                {
                    it = deq_digi_begin(&a);
                    deq_digi_it_advance(&it, index);
                    b.erase(b.begin() + index);
                    deq_digi_erase(&it);
                }
                CHECK(a, b);
                break;
            }
            case TEST_RESIZE: {
                const size_t resize = 3 * index + 1;
                b.resize(resize);
                deq_digi_resize(&a, resize, digi_init(0));
                CHECK(a, b);
                break;
            }
            case TEST_SHRINK_TO_FIT: {
                deq_digi_shrink_to_fit(&a);
                b.shrink_to_fit();
                break;
            }
            case TEST_SORT: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                CHECK(a, b);
                break;
            }
            // internal method only
            case TEST_RANGED_SORT: {
                if (a.size < 4)
                    break; // even the STL crashes on wrong iters
                LOG("unsorted:\n");
                print_deq(&a);
                // including to
                size_t cto = a.size - 4;
                deq_digi__ranged_sort(&a, 1, cto, digi_compare);
                LOG("sorted 1 - %lu (size-4):\n", cto);
                print_deq(&a);

                auto from = b.begin();
                auto to = b.end();
                advance(from, 1);
                advance(to, -3);
                LOG("STL sort %ld - %ld:\n", std::distance(b.begin(), from), std::distance(b.begin(), to));
                std::sort(from, to);
                print_deque(b);
                CHECK(a, b);
                break;
            }
            case TEST_SORT_RANGE: {
                if (a.size < 4)
                    break;
                {
                    deq_digi_sort_range(&a, 1, a.size - 3);
                }
                {
                    auto from = b.begin();
                    auto to = b.end();
                    advance(from, 1);
                    advance(to, -3);
                    std::sort(from, to);
                }
                CHECK(a, b);
                break;
            }
            case TEST_COPY: {
                aa = deq_digi_copy(&a);
                bb = b;
                CHECK(aa, bb);
                deq_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_SWAP: {
                aa = deq_digi_copy(&a);
                aaa = deq_digi_init();
                bb = b;
                deq_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                deq_digi_free(&aaa);
                CHECK(a, b);
                break;
            }
            case TEST_INSERT: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    value = TEST_RAND(INT_MAX);
                    it = deq_digi_begin(&a);
                    deq_digi_it_advance(&it, index);
                    deq_digi_insert(&it, digi_init(value));
                    b.insert(b.begin() + index, DIGI{value});
                }
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_INDEX: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t idx = TEST_RAND(a.size);
                    deq_digi_insert_index(&a, idx, digi_init(value));
#ifdef DEBUG
                    iter =
#endif
                        b.insert(b.begin() + idx, DIGI{value});
                    LOG("STL insert %d at %ld:\n", value, std::distance(b.begin(), iter));
                }
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_COUNT: {
#ifdef LONG
                size_t amount = TEST_RAND(1024);
#else
                size_t amount = TEST_RAND(10);
#endif
                it = deq_digi_begin(&a);
                deq_digi_it_advance(&it, index);
                if (!deq_digi_insert_count(&it, amount, digi_init(value)))
                {
                    fprintf(stderr, "overflow size %zu + amount %zu\n", a.size, amount);
                    break;
                }
                LOG("CTL insert_count at %zu, %zux %d:\n", it.index, amount, value);
                print_deq(&a);

                if (amount)
                {
#ifdef DEBUG
                    iter =
#endif
                        b.insert(b.begin() + index, amount, DIGI{value});
                    LOG("STL insert %zux %d at %ld:\n", amount, value, std::distance(b.begin(), iter));
                    // CHECK_ITER (pos, b, iter);
                    print_deque(b); // may be corrupt
                    CHECK(a, b);    // may be NULL
                }
                break;
            }
            case TEST_ERASE_INDEX: // 25
                if (a.size > 0)
                {
                    LOG("erase_index %zu from %zu\n", index, a.size);
                    deq_digi_erase_index(&a, index);
                    b.erase(b.begin() + index);
                    // CHECK_ITER (pos, b, iter);
                }
                CHECK(a, b);
                break;
            case TEST_INSERT_RANGE: // 54
            {
                size_t size2 = TEST_RAND(TEST_MAX_SIZE);
                aa = deq_digi_init_from(&a);
                for (int i = 0; i < (int)size2; i++)
                {
                    deq_digi_push_back(&aa, digi_init(i));
                    bb.push_back(DIGI{i});
                }
                print_deq(&a);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                // libstdc++  fails on empty (uninitialized) front or back
                // values. It cannot deal with empty insert ranges,
                // i.e. first_b2 == last_b2. We can.
                if (first_b2 == last_b2)
                {
                    deq_digi_free(&aa);
                    break;
                }
                // print_deq(&aa);
                it = deq_digi_begin(&a);
                deq_digi_it_advance(&it, index);
                LOG("insert_range 0-%zu at %zu:\n", size2 - 1, index);
                deq_digi_insert_range(&it, &range_a2);
                b.insert(b.begin() + index, first_b2, last_b2);
#if 0
                std::vector<DIGI> cc;
                LOG("add vector (%zu)\n", size2);
                for(int i = 0; i < (int)size2; i++)
                    cc.push_back(DIGI{i});
                b.insert(b.begin() + index, cc.begin(), cc.end());
#endif

                LOG("CTL =>\n");
                print_deq(&a);
                LOG("STL =>\n");
                print_deque(b);
                if (a.size != b.size())
                    fail++;
                CHECK(a, b);

                // for coverage: the 2nd case
                LOG("insert_range at end:\n");
                it = deq_digi_end(&a);
                deq_digi_insert_range(&it, &range_a2);
                b.insert(b.end(), first_b2, last_b2);
                print_deq(&a);
                CHECK(a, b);

                deq_digi_free(&aa);
                break;
            }
            case TEST_ASSIGN_GENERIC:
            {
                print_deq(&a);
                aa = deq_digi_init_from(&a);
                setup_deque(&aa, bb);
                range_a2 = deq_digi_begin(&aa);
                deq_digi_assign_generic(&a, &range_a2);
                b.assign(bb.begin(), bb.end());
                print_deq(&a);
                if (a.size != b.size())
                    fail++;
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_INSERT_GENERIC:
            {
                aa = deq_digi_init_from(&a);
                setup_deque(&aa, bb);
                print_deq(&aa);
                it = deq_digi_begin(&a);
                range_a2 = deq_digi_begin(&aa);
                deq_digi_it_advance(&it, index);
                LOG("insert_range %zu at %zu:\n", aa.size, index);
                deq_digi_insert_generic(&it, &range_a2);
                b.insert(b.begin() + index, bb.begin(), bb.end());
                LOG("CTL =>\n");
                print_deq(&a);
                LOG("STL =>\n");
                print_deque(b);
                if (a.size != b.size())
                    fail++;
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
#endif
            case TEST_ERASE_RANGE: {
                if (a.size < 4)
                {
                    deq_digi_resize(&a, 10, digi_init(value));
                    b.resize(10, DIGI{value});
                }
                const size_t idx = TEST_RAND(a.size / 2);
                const size_t iend = idx + TEST_RAND(a.size - idx);
                range_a1 = deq_digi_begin(&a);
                deq_digi_it_advance(&range_a1, idx);
                range_a1.end = iend;
                print_deq_range(range_a1);
                LOG("erase_range %zu of %zu\n", idx, a.size);
                deq_digi_erase_range(&range_a1);
                LOG("CTL erase_range [%lu - %lu):\n", idx, iend);
                print_deq(&a);

                first_b1 = b.begin() + idx;
                last_b1 = b.begin() + iend;
                /*auto iter =*/
                b.erase(first_b1, last_b1);
                // LOG ("STL erase [%ld, %ld):\n", std::distance(b.begin(), iter), iend);
                print_deque(b);
                // CHECK_RANGE (range, iter, b_end);
                CHECK(a, b);
                break;
            }
            case TEST_EMPLACE: {
                digi key = digi_init(value);
                if (a.size < 1)
                {
                    int v = TEST_RAND(TEST_MAX_VALUE);
                    deq_digi_push_front(&a, digi_init(v));
                    b.push_front(DIGI{v});
                }
#if defined DEBUG && !defined LONG
                //if (a.size > 10)
                //{
                //    deq_digi_resize(&a, 10, digi_init(0));
                //    b.resize(10);
                //}
                LOG("before emplace\n");
                print_deq(&a);
#endif
                assert(a.size > 0);
                it = deq_digi_begin(&a);
                deq_digi_it_advance(&it, index);
                LOG("CTL emplace 1 %d\n", a.size > index ? *it.ref->value : -1);
                deq_digi_emplace(&it, &key);
                print_deq(&a);
                LOG("STL emplace begin++ %d\n", *DIGI{value});
                assert(b.size() > 0);
                b.emplace(b.begin() + index, DIGI{value});
                print_deque(b);
                if (!b.front().value)
                    fprintf(stderr, "!b.front().value size=%zu, index 1\n", b.size());
                if (!deq_digi_front(&a)->value)
                    fprintf(stderr, "!deq_digi_front(&a)->value size=%zu, index %zu\n", a.size, index);
                // b.front might fail with size=2, STL bug
                if (b.size() == 2 && !*b.front().value)
                {
                    fprintf(stderr, "Skip !*b.front().value size=2 STL bug\n");
                    deq_digi_clear(&a);
                    b.clear();
                }
                CHECK(a, b);
                // may not delete, as emplace does not copy
                // digi_free(&key);
                break;
            }
            case TEST_EMPLACE_FRONT: {
                digi key = digi_init(value);
                deq_digi_emplace_front(&a, &key);
                b.emplace_front(DIGI{value});
                CHECK(a, b);
                break;
            }
            case TEST_EMPLACE_BACK: {
                digi key = digi_init(value);
                deq_digi_emplace_back(&a, &key);
                b.emplace_back(DIGI{value});
                CHECK(a, b);
                break;
            }
            case TEST_ASSIGN: {
                size_t assign_size = TEST_RAND(a.size) + 1;
                deq_digi_assign(&a, assign_size, digi_init(value));
                b.assign(assign_size, DIGI{value});
                CHECK(a, b);
                break;
            }
            case TEST_REMOVE_IF: {
                deq_digi_remove_if(&a, digi_is_odd);
                print_deq(&a);
                b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                print_deque(b);
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_IF: {
#if __cpp_lib_erase_if >= 202002L
                num_a = deq_digi_erase_if(&a, digi_is_odd);
                num_b = std::erase_if(b, DIGI_is_odd);
                assert(num_a == num_b);
#else
                deq_digi_erase_if(&a, digi_is_odd);
                b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
#endif
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL: {
                aa = deq_digi_copy(&a);
                bb = b;
                assert(deq_digi_equal(&a, &aa));
                assert(b == bb);
                deq_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_FIND: {
                if (a.size > 0)
                {
                    value = TEST_RAND(2) ? value : *deq_digi_at(&a, index)->value;
                    digi key = digi_init(value);
                    it = deq_digi_find(&a, key);
                    iter = find(b.begin(), b.end(), DIGI{value});
                    found_a = !deq_digi_it_done(&it);
                    found_b = iter != b.end();
                    assert(found_a == found_b);
                    if (found_a && found_b)
                        assert(*it.ref->value == *iter->value);

                    a.equal = NULL;
                    it = deq_digi_find(&a, key);
                    found_a = !deq_digi_it_done(&it);
                    assert(found_a == found_b);
                    if (found_a && found_b)
                        assert(*it.ref->value == *iter->value);

                    digi_free(&key);
                    CHECK(a, b);
                }
                break;
            }
            case TEST_FIND_IF: {
                it = deq_digi_find_if(&a, digi_is_odd);
                iter = std::find_if(b.begin(), b.end(), DIGI_is_odd);
                if (iter == b.end())
                    assert(deq_digi_it_done(&it));
                else
                    assert(*(it.ref->value) == *iter->value);
                break;
            }
            case TEST_FIND_IF_NOT: {
                it = deq_digi_find_if_not(&a, digi_is_odd);
                iter = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
                print_deq(&a);
                print_deque(b);
                CHECK_ITER(it, b, iter);
                if (iter == b.end())
                    assert(deq_digi_it_done(&it));
                else
                    assert(*(it.ref->value) == *iter->value);
                break;
            }
            case TEST_ALL_OF: {
                found_a = deq_digi_all_of(&a, digi_is_odd);
                found_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF: {
                found_a = deq_digi_any_of(&a, digi_is_odd);
                found_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF: {
                found_a = deq_digi_none_of(&a, digi_is_odd);
                found_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT: {
                num_a = deq_digi_count(&a, digi_init((int)index));
                num_b = std::count(b.begin(), b.end(), DIGI{(int)index});
                assert(num_a == num_b);
                break;
            }
            case TEST_COUNT_IF: {
                num_a = deq_digi_count_if(&a, digi_is_odd);
                num_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
                assert(num_a == num_b);
                break;
            }
            case TEST_FIND_RANGE: {
                value = pick_random(&a);
                digi key = digi_init(value);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = deq_digi_find_range(&range_a1, key);
                iter = find(first_b1, last_b1, DIGI{value});
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
                it = deq_digi_find_if_range(&range_a1, digi_is_odd);
                iter = find_if(first_b1, last_b1, DIGI_is_odd);
                print_deq(&a);
                print_deque(b);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = deq_digi_find_if_not_range(&range_a1, digi_is_odd);
                iter = find_if_not(first_b1, last_b1, DIGI_is_odd);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_ALL_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = deq_digi_all_of_range(&range_a1, digi_is_odd);
                found_b = std::all_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_deq(&a);
                    print_deque(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = deq_digi_any_of_range(&range_a1, digi_is_odd);
                found_b = std::any_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_deq(&a);
                    print_deque(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = deq_digi_none_of_range(&range_a1, digi_is_odd);
                found_b = none_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_deq(&a);
                    print_deque(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                num_a = deq_digi_count_if_range(&range_a1, digi_is_odd);
                num_b = count_if(first_b1, last_b1, DIGI_is_odd);
                if (num_a != num_b)
                {
                    print_deq(&a);
                    print_deque(b);
                    printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                    fail++;
                }
                assert(num_a == num_b);
                break;
            }
            case TEST_COUNT_RANGE: {
                int v = TEST_RAND(2) ? value : 0;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                num_a = deq_digi_count_range(&range_a1, digi_init(v));
                num_b = count(first_b1, last_b1, DIGI{v});
                assert(num_a == num_b);
                break;
            }
            case TEST_INCLUDES: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                found_a = deq_digi_includes(&a, &aa);
                found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                assert(found_a == found_b);
                CHECK(aa, bb);
                deq_digi_free(&aa);
                break;
            }
            case TEST_INCLUDES_RANGE: // 51
            {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                print_deq(&a);
                print_deq(&aa);

                // deviates with aa: 0,0 of 1
                found_a = deq_digi_includes_range(&range_a1, &range_a2);
                found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
                assert(found_a == found_b);
                CHECK(aa, bb);
                deq_digi_free(&aa);
                break;
            }
            case TEST_UNION: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = deq_digi_union(&a, &aa);
#ifndef _MSC_VER
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                CHECK(aa, bb);
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = deq_digi_intersection(&a, &aa);
#ifndef _MSC_VER
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                CHECK(aa, bb);
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = deq_digi_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                CHECK(aa, bb);
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                print_deq(&a);
                aaa = deq_digi_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                CHECK(aa, bb);
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_UNION_RANGE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_deq_range(range_a1);
                print_deq_range(range_a2);
                aaa = deq_digi_union_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_deq(&aaa);

                LOG("STL b + bb\n");
                print_deque(b);
                print_deque(bb);
#ifndef _MSC_VER
                std::set_union(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_deque(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("union_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION_RANGE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_deq_range(range_a1);
                print_deq_range(range_a2);
                aaa = deq_digi_intersection_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_deq(&aaa);

                LOG("STL b + bb\n");
                print_deque(b);
                print_deque(bb);
#ifndef _MSC_VER
                std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_deque(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("intersection_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE_RANGE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                print_deq_range(range_a1);
                print_deq_range(range_a2);
                aaa = deq_digi_difference_range(&range_a1, &range_a2);
                LOG("CTL => aaa (%zu)\n", aa.size);
                print_deq(&aaa);

                LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
                print_deque(b);
                print_deque(bb);
#ifndef _MSC_VER
                std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb (%zu)\n", bbb.size());
                print_deque(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
                setup_deque(&aa, bb);
                deq_digi_sort(&a);
                deq_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_deq_range(range_a1);
                print_deq_range(range_a2);
                aaa = deq_digi_symmetric_difference_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_deq(&aaa);

                LOG("STL b + bb\n");
                print_deque(b);
                print_deque(bb);
#ifndef _MSC_VER
                std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_deque(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aaa);
                deq_digi_free(&aa);
                break;
            }
            case TEST_GENERATE: {
                digi_generate_reset();
                deq_digi_generate(&a, digi_generate);
                digi_generate_reset();
                std::generate(b.begin(), b.end(), DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                digi_generate_reset();
                deq_digi_generate_range(&range_a1, digi_generate);
                digi_generate_reset();
                std::generate(first_b1, last_b1, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM: {
                aa = deq_digi_transform(&a, digi_untrans);
                bb.resize(b.size());
                std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
            case TEST_GENERATE_N: // TEST=56
            {
                size_t count = TEST_RAND(20);
                LOG("generate_n %zu\n", count);
#ifndef _MSC_VER
                digi_generate_reset();
                deq_digi_generate_n(&a, count, digi_generate);
                print_deq(&a);
                digi_generate_reset();
                // FIXME The STL is arguably broken here.
                int n = MIN(count, b.size());
                b.erase(b.begin(), b.begin() + n);
                std::generate_n(std::inserter(b, b.begin()), n, DIGI_generate);
                print_deque(b);
                CHECK(a, b);
#endif
                break;
            }
            case TEST_GENERATE_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t off = first_b1 - b.begin();
                size_t len = last_b1 - first_b1;
                size_t count = TEST_RAND(20 - off);
                LOG("generate_n_range %zu\n", count);
#ifndef _MSC_VER
                digi_generate_reset();
                deq_digi_generate_n_range(&range_a1, count, digi_generate);
                print_deq(&a);
                digi_generate_reset();
                int n = MIN(MIN(count, b.size()), len);
                b.erase(first_b1, first_b1 + n);
                first_b1 = b.begin() + off;
                std::generate_n(std::inserter(b, first_b1), n, DIGI_generate);
                print_deque(b);
                CHECK(a, b);
#endif
                break;
            }
            case TEST_TRANSFORM_IT: {
                if (a.size < 2)
                    break;
                it = deq_digi_begin(&a);
                deq_digi_it_advance(&it, 1);
                print_deq(&a);
                aa = deq_digi_transform_it(&a, &it, digi_bintrans);
                print_deq(&aa);
#ifndef _MSC_VER
                std::transform(b.begin(), b.end() - 1, b.begin() + 1, std::back_inserter(bb), DIGI_bintrans);
                print_deque(bb);
                CHECK(aa, bb);
#endif
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_RANGE: {
                print_deq(&a);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = deq_digi_init_from(&a);
                deq_digi_resize(&aa, last_b1 - first_b1, digi_init(0));
                range_a2 = deq_digi_begin(&aa);
                deq_digi_transform_range(&range_a1, range_a2, digi_untrans);
                print_deq(&aa);
#ifndef _MSC_VER
                std::transform(first_b1, last_b1, std::back_inserter(bb), DIGI_untrans);
                print_deque(bb);
                CHECK(aa, bb);
#endif
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT_RANGE: {
                print_deq(&a);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = deq_digi_begin(&a);
                deq_digi_it_advance(&it, 1);
                aa = deq_digi_init_from(&a);
                deq_digi_resize(&aa, last_b1 - first_b1, digi_init(0));
                range_a2 = deq_digi_begin(&aa);
                deq_digi_transform_it_range(&range_a1, &it, range_a2, digi_bintrans);
                print_deq(&aa);
#ifndef _MSC_VER
                std::transform(first_b1, last_b1, b.begin() + 1, std::back_inserter(bb), DIGI_bintrans);
                print_deque(bb);
                CHECK(aa, bb);
#endif
                CHECK(a, b);
                deq_digi_free(&aa);
                break;
            }
            case TEST_IOTA:
            {
                digi key = digi_init(0);
                deq_digi_iota(&a, key);
                print_deq(&a);
                std::iota(b.begin(), b.end(), DIGI{0});
                print_deque(b);
                CHECK(a, b);
                digi_free(&key);
                break;
            }
            case TEST_IOTA_RANGE:
            {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                digi key = digi_init(0);
                deq_digi_iota_range(&range_a1, key);
                print_deq_range(range_a1);
                std::iota(first_b1, last_b1, DIGI{0});
                print_deque(b);
                CHECK(a, b);
                digi_free(&key);
                break;
            }
            case TEST_SHUFFLE: {
                print_deq(&a);
                deq_digi_shuffle(&a);
                print_deq(&a);
#if __cplusplus < 201703L
                std::random_shuffle(b.begin(), b.end());
#else
                std::shuffle(b.begin(), b.end(), rng);
#endif
                print_deque(b);
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                CHECK(a, b);
                break;
            }
            case TEST_SHUFFLE_RANGE: {
                print_deq(&a);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                deq_digi_shuffle_range(&range_a1);
                print_deq_range(range_a1);
#if __cplusplus < 201703L
                std::random_shuffle(first_b1, last_b1);
#else
                std::shuffle(first_b1, last_b1, rng);
#endif
                // TODO check that the ranges before and after range are still
                // sorted, and untouched.
                print_deque(b);
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                CHECK(a, b);
                break;
            }

            case TEST_COPY_IF: {
                aa = deq_digi_copy_if(&a, digi_is_odd);
/*
#if __cplusplus >= 202002L
                auto bb = a | std::ranges::views::filter(DIGI_is_odd);
                std::ranges::copy(bb, std::back_inserter(bb));
                ADJUST_CAP("filter_range", aa, bb);
                CHECK(aa, bb);
#endif
*/
#if __cplusplus >= 201103L && !defined(_MSC_VER)
                std::copy_if(b.begin(), b.end(), std::back_inserter(bb), DIGI_is_odd);
#else
                for (auto &d: b) {
                    if (DIGI_is_odd(d))
                        bb.push_back(d);
                }
#endif
                ADJUST_CAP("copy_if", aa, bb);
                CHECK(aa, bb);
                deq_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_COPY_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = deq_digi_copy_if_range(&range_a1, digi_is_odd);
#ifndef _MSC_VER
#if __cplusplus >= 201103L
                std::copy_if(first_b1, last_b1, std::back_inserter(bb), DIGI_is_odd);
                ADJUST_CAP("copy_if_range", aa, bb);
                CHECK(aa, bb);
#endif
#endif
                deq_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_MISMATCH: {
                if (a.size < 2)
                    break;
                setup_deque(&aa, bb);
                deq_digi_it b1, b2;
                b1 = deq_digi_begin(&a);
                b2 = deq_digi_begin(&aa);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                /*found_a = */ deq_digi_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
                if (!bb.size() || !distance(first_b2, last_b2))
                {
                    printf("skip std::mismatch with empty 2nd range. use C++14\n");
                    deq_digi_free(&aa);
                    break;
                }
                auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
                int d1a = deq_digi_it_distance(&b1, &range_a1);
                int d2a = deq_digi_it_distance(&b2, &range_a2);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                // TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                deq_digi_free(&aa);
                break;
            }
            case TEST_SEARCH: // 51
            {
                print_deq(&a);
                aa = deq_digi_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    long i = std::distance(bb.begin(), first_b2);
                    deq_digi_set(&aa, i, digi_init(0));
                    bb[i] = DIGI{0};
                }
                print_deq_range(range_a2);
                it = deq_digi_search(&a, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", deq_digi_it_done(&it) ? "no" : "yes");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                CHECK_ITER(it, b, iter);
                deq_digi_free(&aa);
                break;
            }
            case TEST_SEARCH_RANGE: {
                aa = deq_digi_copy(&a);
                bb = b;
                print_deq(&a);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    long i = std::distance(bb.begin(), first_b2);
                    deq_digi_set(&aa, i, digi_init(0));
                    bb[i] = DIGI{0};
                }
                print_deq_range(range_a2);
                range_a1 = deq_digi_begin(&a);
                found_a = deq_digi_search_range(&range_a1, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", found_a ? "yes" : "no");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                assert(found_a == !deq_digi_it_done(&range_a1));
                CHECK_ITER(range_a1, b, iter);
                deq_digi_free(&aa);
                break;
            }
            case TEST_SEARCH_N: {
                print_deq(&a);
                size_t count = TEST_RAND(4);
                value = pick_random(&a);
                LOG("search_n %zu %d\n", count, value);
                it = deq_digi_search_n(&a, count, digi_init(value));
                iter = search_n(b.begin(), b.end(), count, DIGI{value});
                CHECK_ITER(it, b, iter);
                LOG("found %s at %zu\n", deq_digi_it_done(&it) ? "no" : "yes",
                    deq_digi_it_index(&it));
                break;
            }
            case TEST_SEARCH_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t count = TEST_RAND(4);
                value = pick_random(&a);
                LOG("search_n_range %zu %d\n", count, value);
                print_deq_range(range_a1);
                pos = deq_digi_search_n_range(&range_a1, count, digi_init(value));
                iter = search_n(first_b1, last_b1, count, DIGI{value});
                CHECK_RANGE(*pos, iter, last_b1);
                LOG("found %s at %zu\n", deq_digi_it_done(pos) ? "no" : "yes",
                    deq_digi_it_index(pos));
                break;
            }
            case TEST_ADJACENT_FIND: {
                print_deq(&a);
                it = deq_digi_adjacent_find(&a);
                iter = adjacent_find(b.begin(), b.end());
                CHECK_ITER(it, b, iter);
                LOG("found %s\n", deq_digi_it_done(&it) ? "no" : "yes");
                break;
            }
            case TEST_ADJACENT_FIND_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_deq_range(range_a1);
                pos = deq_digi_adjacent_find_range(&range_a1);
                iter = adjacent_find(first_b1, last_b1);
                CHECK_ITER(*pos, b, iter);
                LOG("found %s\n", deq_digi_it_done(pos) ? "no" : "yes");
                break;
            }
            case TEST_FIND_FIRST_OF: {
                setup_deque(&aa, bb);
                last_b2 = bb.end();
                range_a2 = deq_digi_begin(&aa);
                if (range_a2.index + 5 < aa.size)
                {
                    range_a2.end = range_a2.index + 5;
                    last_b2 = bb.begin() + 5;
                }
                it = deq_digi_find_first_of(&a, &range_a2);
                iter = std::find_first_of(b.begin(), b.end(), bb.begin(), last_b2);
                print_deq(&a);
                print_deq(&aa);
                LOG("=> %zu vs %ld\n", deq_digi_it_index(&it), iter - b.begin());
                CHECK_ITER(it, b, iter);
                deq_digi_free(&aa);
                break;
            }
            case TEST_FIND_FIRST_OF_RANGE: {
                setup_deque(&aa, bb);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                found_a = deq_digi_find_first_of_range(&range_a1, &range_a2);
                iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", iter != last_b1 ? "yes" : "no",
                    deq_digi_it_index(&range_a1), iter - b.begin());
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                deq_digi_free(&aa);
                break;
            }
            case TEST_FIND_END: {
                setup_deque(&aa, bb);
                deq_digi_resize(&aa, 4, digi_init(0));
                bb.resize(4);
                range_a2 = deq_digi_begin(&aa);
                print_deq(&a);
                print_deq(&aa);
                it = deq_digi_find_end(&a, &range_a2);
                iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
                found_a = !deq_digi_it_done(&it);
                found_b = iter != b.end();
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                    found_b ? "yes" : "no", deq_digi_it_index(&it),
                    std::distance(b.begin(), iter));
                assert(found_a == found_b);
                CHECK_RANGE(it, iter, b.end());
                deq_digi_free(&aa);
                break;
            }
            case TEST_FIND_END_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                setup_deque(&aa, bb);
                deq_digi_resize(&aa, 4, digi_init(0));
                bb.resize(4);
                range_a2 = deq_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
                it = deq_digi_find_end_range(&range_a1, &range_a2);
                iter = find_end(first_b1, last_b1, bb.begin(), bb.end());
                found_a = !deq_digi_it_done(&it);
                found_b = iter != last_b1;
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                    found_b ? "yes" : "no", deq_digi_it_index(&it),
                    std::distance(b.begin(), iter));
                assert(found_a == found_b);
                CHECK_RANGE(it, iter, last_b1);
#endif
                deq_digi_free(&aa);
                break;
            }
            case TEST_EQUAL_VALUE: {
                size_t size1 = MIN(TEST_RAND(a.size), 5);
                deq_digi_resize(&a, size1, digi_init(0));
                b.resize(size1);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t idx = TEST_RAND(a.size - 1);
                value = a.size ? *deq_digi_at(&a, idx)->value : 0;
                LOG("equal_value %d\n", value);
                print_deq_range(range_a1);
                found_a = deq_digi_equal_value(&range_a1, digi_init(value));
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
                aa = deq_digi_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                found_a = deq_digi_equal_range(&range_a1, &range_a2);
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
                deq_digi_free(&aa);
                break;
            }
            case TEST_LEXICOGRAPHICAL_COMPARE: {
                aa = deq_digi_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                found_a = deq_digi_lexicographical_compare(&range_a1, &range_a2);
                found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
                LOG("same_a: %d same_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                deq_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_UNIQUE: {
                print_deq(&a);
                it = deq_digi_unique(&a);
                found_a = it.end < a.size;
                size_t idx = deq_digi_it_index(&it);
                print_deq(&a);
                // C++ is special here with its move hack
                iter = unique(b.begin(), b.end());
                found_b = iter != b.end();
                long dist = std::distance(b.begin(), iter);
                b.resize(dist);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", idx);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_deque(b);
                assert(found_a == found_b);
                assert((long)idx == dist);
                break;
            }
            case TEST_UNIQUE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_deq_range(range_a1);
                size_t orig_size = a.size;
                it = deq_digi_unique_range(&range_a1);
                found_a = a.size < orig_size;
                size_t idx = deq_digi_it_index(&it);
                iter = unique(first_b1, last_b1);
                found_b = iter != last_b1;
                long dist = std::distance(b.begin(), iter);
                if (found_b)
                    b.erase(iter, last_b1);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", idx);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_deq(&a);
                print_deque(b);
                assert(found_a == found_b);
                assert((long)idx == dist);
                break;
            }
#endif // DEBUG
            case TEST_LOWER_BOUND: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                it = deq_digi_lower_bound(&a, digi_init(value));
                iter = lower_bound(b.begin(), b.end(), DIGI{value});
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_UPPER_BOUND: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                it = deq_digi_upper_bound(&a, digi_init(value));
                iter = upper_bound(b.begin(), b.end(), DIGI{value});
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_LOWER_BOUND_RANGE: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                pos = deq_digi_lower_bound_range(&range_a1, digi_init(value));
                iter = lower_bound(first_b1, last_b1, DIGI{value});
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_UPPER_BOUND_RANGE: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                pos = deq_digi_upper_bound_range(&range_a1, digi_init(value));
                iter = upper_bound(first_b1, last_b1, DIGI{value});
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_BINARY_SEARCH: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                found_a = deq_digi_binary_search(&a, digi_init(value));
                found_b = binary_search(b.begin(), b.end(), DIGI{value});
                LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_BINARY_SEARCH_RANGE: {
                deq_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                found_a = deq_digi_binary_search_range(&range_a1, digi_init(value));
                found_b = binary_search(first_b1, last_b1, DIGI{value});
                LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_MERGE: {
                setup_deque(&aa, bb);
                aaa = deq_digi_merge(&a, &aa);
#ifndef _MSC_VER
                merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aa);
                deq_digi_free(&aaa);
                break;
            }
            case TEST_MERGE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                setup_deque(&aa, bb);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                aaa = deq_digi_merge_range(&range_a1, &range_a2);
#ifndef _MSC_VER
                merge(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                deq_digi_free(&aa);
                deq_digi_free(&aaa);
                break;
            }
            case TEST_IS_SORTED: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_deq_range(range_a1);
                found_a = deq_digi_is_sorted(&range_a1);
                found_b = std::is_sorted(first_b1, last_b1);
                LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_IS_SORTED_UNTIL: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_deq_range(range_a1);
                range_a2 = range_a1;
                range_a2.index = range_a1.end;
                pos = deq_digi_is_sorted_until(&range_a1, &range_a2);
                iter = std::is_sorted_until(first_b1, last_b1);
                LOG("=> %s/%s, %ld/%ld: %d/%d\n", !deq_digi_it_done(pos) ? "yes" : "no",
                    iter != last_b1 ? "yes" : "no",
                    deq_digi_it_index(pos), distance(b.begin(), first_b1),
                    !deq_digi_it_done(pos) ? *pos->ref->value : -1,
                    iter != last_b1 ? *iter->value : -1);
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_REVERSE: {
                print_deq(&a);
                deq_digi_reverse(&a);
                reverse(b.begin(), b.end());
                print_deq(&a);
                CHECK(a, b);
                break;
            }
            case TEST_REVERSE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_deq_range(range_a1);
                deq_digi_reverse_range(&range_a1);
                reverse(first_b1, last_b1);
                CHECK(a, b);
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
#ifdef DEBUG
            if (which < number_ok)
#endif
                CHECK(a, b);
            deq_digi_free(&a);
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
