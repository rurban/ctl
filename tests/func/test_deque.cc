#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/deque.h>

#include <deque>
#include <algorithm>

#define ADJUST_CAP(m,a,b)
void print_deq(deq_digi *a)
{
    for(size_t i = 0; i < a->size; i++)
        printf ("%zu: %d\n", i, *deq_digi_at(a, i)->value);
    printf ("\n");
}

void print_deque(std::deque<DIGI> &b)
{
    for(size_t i = 0; i < b.size(); i++)
    {
        DIGI val = b.at(i);
        // DIGI.hh is not as stable as the CTL
        if (val.value)
            printf ("%zu: %d\n", i, *val.value);
        else
            printf ("%zu: NULL\n", i);
    }
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_SIZE 15
#define TEST_MAX_VALUE 1000
#else
#define TEST_MAX_VALUE INT_MAX
#endif

#define print_deq_range(x) print_deq(x.container)
#ifndef DEBUG
#define print_deq(x)
#define print_deque(x)

#define CHECK(_x, _y) {                                           \
    assert(_x.size == _y.size());                                 \
    assert(deq_digi_empty(&_x) == _y.empty());                    \
    if(_x.size > 0) {                                             \
        if (_y.front().value)                                     \
            assert(*_y.front().value == *deq_digi_front(&_x)->value); \
        if (_y.back().value)                                      \
            assert(*_y.back().value == *deq_digi_back(&_x)->value);\
    }                                                             \
    std::deque<DIGI>::iterator _iter = _y.begin();                \
    foreach(deq_digi, &_x, _it) {                                 \
        /* libstdc++ may be corrupt. libc++ not */                \
        if (_iter->value)                                         \
            assert(*_it.ref->value == *_iter->value);             \
        _iter++;                                                  \
    }                                                             \
    size_t _i = 0;                                                \
    for(auto& _d : _y) {                                          \
        digi* _ref = deq_digi_at(&_x, _i++);                      \
        if (_d.value)                                             \
            assert(*_ref->value == *_d.value);                    \
    }                                                             \
    for(_i = 0; _i < _y.size(); _i++)                             \
        assert(*_y.at(_i).value == *deq_digi_at(&_x, _i)->value); \
}
#define CHECK_ITER(cit,_y,iter)                                   \
    assert((long)(cit).index == std::distance(_y.begin(), iter))

#else // DEBUG

#define CHECK(_x, _y) {                                           \
    assert(_x.size == _y.size());                                 \
    assert(deq_digi_empty(&_x) == _y.empty());                    \
    if(_x.size > 0) {                                             \
        if (_y.front().value)                                     \
            assert(*_y.front().value == *deq_digi_front(&_x)->value); \
        else                                                          \
            fprintf(stderr, "STL empty front value\n");               \
        if (_y.back().value)                                          \
            assert(*_y.back().value == *deq_digi_back(&_x)->value);   \
        else                                                          \
            fprintf(stderr, "STL empty back value\n");                \
    }                                                             \
    std::deque<DIGI>::iterator _iter = _y.begin();                \
    foreach(deq_digi, &_x, _it) {                                 \
        if (*_it.ref->value != *_iter->value)                     \
            fprintf(stderr, "CTL %d at %zu vs STL %d\n",          \
                    *_it.ref->value, _it.index,                   \
                    *_iter->value);                               \
        assert(*_it.ref->value == *_iter->value);                 \
        _iter++;                                                  \
    }                                                             \
    size_t _i = 0;                                                \
    for(auto& _d : _y) {                                          \
        digi* _ref = deq_digi_at(&_x, _i++);                      \
        if (_d.value)                                             \
            assert(*_ref->value == *_d.value);                    \
    }                                                             \
    for(_i = 0; _i < _y.size(); _i++)                             \
        assert(*_y.at(_i).value == *deq_digi_at(&_x, _i)->value); \
}
#define CHECK_ITER(cit,_y,iter) {                                 \
    long _dist = std::distance(_y.begin(), iter);                 \
    if ((long)(cit).index != _dist)                               \
        fprintf(stderr, "CTL index %zu vs STL %zu\n",             \
                (cit).index,_dist);                               \
    assert((long)(cit).index == _dist);                           \
}

#endif

int random_element(deq_digi* a)
{
    const size_t index = TEST_RAND(a->size);
    if (!a->size)
        return 0;
    digi *vp = deq_digi_at(a, index);
    return *vp->value;
}

static void
get_random_iters (deq_digi *a, deq_digi_it* first_a, deq_digi_it* last_a,
                  std::deque<DIGI>& b, std::deque<DIGI>::iterator &first_b,
                  std::deque<DIGI>::iterator &last_b)
{
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
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            *last_a = deq_digi_end(a);
            last_b = b.end();
        }
        else
        {
            deq_digi_it it2 = deq_digi_begin(a);
            last_b = b.begin();
            deq_digi_it_advance(&it2, r2);
            last_b += r2;
            *last_a = it2;
        }
    }
    else
    {
        deq_digi_it end = deq_digi_end(a);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a->index;
}

// TESTS DEQ STABILITY WITH SELF CLEANUP.
// EDGE CASE:
//     MISC CALLS TO POP/PUSH FRONT/BACK WITH
//     DEQUE SIZE 1 CAUSED HEAP USE AFTER FREE ISSUES.

void
test_capacity_edge_case(void)
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
    }{
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
    }{
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
    }{
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
void
test_random_work_load(void)
{
    deq_digi a = deq_digi_init();
    std::deque<DIGI> b;
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t i = 0; i < loops; i++)
        switch(TEST_RAND(5))
        {
            case 0:
            {
                assert(a.size == b.size());
                deq_digi_push_front(&a, digi_init(1));
                b.push_front(DIGI{1});
                assert(a.size == b.size());
                break;
            }
            case 1:
            {
                assert(a.size == b.size());
                deq_digi_push_back(&a, digi_init(1));
                b.push_back(DIGI{1});
                assert(a.size == b.size());
                break;
            }
            case 2:
            {
                assert(a.size == b.size());
                if(a.size)
                    deq_digi_pop_front(&a);
                if(b.size())
                    b.pop_front();
                assert(a.size == b.size());
                break;
            }
            case 3:
            {
                assert(a.size == b.size());
                if(a.size)
                    deq_digi_pop_back(&a);
                if(b.size())
                    b.pop_back();
                assert(a.size == b.size());
                break;
            }
            case 4:
            {
                assert(a.size == b.size());
                deq_digi_clear(&a);
                b.clear();
                assert(a.size == b.size());
                break;
            }
        }
    deq_digi_free(&a);
}

static void
setup_deque(deq_digi* a, std::deque<DIGI>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = deq_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for(size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        deq_digi_push_back(a, digi_init(vb));
        b.push_back(DIGI{vb});
    }
}

int
main(void)
{
    int fail = 0;
    test_capacity_edge_case();
    test_random_work_load();
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        LOG("loop %zu, size %zu\n", loop, size);
#if defined(DEBUG) && !defined(LONG)
        size = 10;
#endif
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            deq_digi a = deq_digi_init();
            a.compare = digi_compare;
            a.equal = digi_equal;
            std::deque<DIGI> b;
            if(mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                deq_digi_resize(&a, size, digi_init(0));
                b.resize(size);
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    deq_digi_push_back(&a, digi_init(value));
                    b.push_back(DIGI{value});
                }
            }
#define FOREACH_METH(TEST) \
            TEST(PUSH_BACK) \
            TEST(POP_BACK) \
            TEST(PUSH_FRONT) \
            TEST(POP_FRONT) \
            TEST(CLEAR) \
            TEST(ERASE) \
            TEST(ERASE_INDEX) \
            TEST(ERASE_IF) \
            TEST(REMOVE_IF) \
            TEST(INSERT) \
            TEST(INSERT_INDEX) \
            TEST(INSERT_COUNT) \
            TEST(EMPLACE) \
            TEST(EMPLACE_FRONT) \
            TEST(EMPLACE_BACK) \
            TEST(RESIZE) \
            TEST(SHRINK_TO_FIT) \
            TEST(SORT) \
            TEST(RANGED_SORT) \
            TEST(SORT_RANGE) \
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
            TEST(INCLUDES) \
            TEST(INCLUDES_RANGE) \
            TEST(UNION) \
            TEST(INTERSECTION) \
            TEST(DIFFERENCE) \
            TEST(SYMMETRIC_DIFFERENCE) \
            TEST(UNION_RANGE) \
            TEST(INTERSECTION_RANGE) \
            TEST(DIFFERENCE_RANGE) \
            TEST(SYMMETRIC_DIFFERENCE_RANGE) \
            TEST(GENERATE) \
            TEST(GENERATE_RANGE) \
            TEST(TRANSFORM) \

#define FOREACH_DEBUG(TEST) \
            TEST(ERASE_RANGE) \
            TEST(INSERT_RANGE) /* 54 */ \
            TEST(EQUAL_RANGE) \
            TEST(FIND_END) \
            TEST(FIND_END_IF) \
            TEST(FIND_END_RANGE) \
            TEST(FIND_END_IF_RANGE) \
            TEST(LOWER_BOUND) \
            TEST(UPPER_BOUND) \
            TEST(LOWER_BOUND_RANGE) \
            TEST(UPPER_BOUND_RANGE) \
            TEST(GENERATE_N) \
            TEST(GENERATE_N_RANGE) \
            TEST(TRANSFORM_IT) \
            TEST(TRANSFORM_RANGE) /* 61 */ \

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
            LOG ("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
            switch(which)
            {
                case TEST_PUSH_BACK:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    b.push_back(DIGI{value});
                    deq_digi_push_back(&a, digi_init(value));
                    CHECK(a, b);
                    break;
                }
                case TEST_POP_BACK:
                {
                    if(a.size > 0)
                    {
                        b.pop_back();
                        deq_digi_pop_back(&a);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_PUSH_FRONT:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    b.push_front(DIGI{value});
                    deq_digi_push_front(&a, digi_init(value));
                    CHECK(a, b);
                    break;
                }
                case TEST_POP_FRONT:
                {
                    if(a.size > 0)
                    {
                        b.pop_front();
                        deq_digi_pop_front(&a);
                        CHECK(a, b);
                    }
                    break;
                }
                case TEST_CLEAR:
                {
                    b.clear();
                    deq_digi_clear(&a);
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        deq_digi_it pos = deq_digi_begin(&a);
                        deq_digi_it_advance(&pos, index);
                        b.erase(b.begin() + index);
                        deq_digi_erase(&pos);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_RESIZE:
                {
                    const size_t resize = 3 * TEST_RAND(a.size) + 1;
                    b.resize(resize);
                    deq_digi_resize(&a, resize, digi_init(0));
                    CHECK(a, b);
                    break;
                }
                case TEST_SHRINK_TO_FIT:
                {
                    deq_digi_shrink_to_fit(&a);
                    b.shrink_to_fit();
                    break;
                }
                case TEST_SORT:
                {
                    deq_digi_sort(&a);
                    std::sort(b.begin(), b.end());
                    CHECK(a, b);
                    break;
                }
                // internal method only
                case TEST_RANGED_SORT:
                {
                    if (a.size < 4)
                        break; // even the STL crashes on wrong iters
                    LOG ("unsorted:\n");
                    print_deq (&a);
                    // including to
                    size_t cto = a.size - 4;
                    deq_digi__ranged_sort(&a, 1, cto, digi_compare);
                    LOG ("sorted 1 - %lu (size-4):\n", cto);
                    print_deq (&a);

                    auto from = b.begin();
                    auto to = b.end();
                    advance(from, 1);
                    advance(to, -3);
                    LOG ("STL sort %ld - %ld:\n", std::distance(b.begin(), from),
                            std::distance(b.begin(), to));
                    std::sort(from, to);
                    print_deque (b);
                    CHECK(a, b);
                    break;
                }
                case TEST_SORT_RANGE:
                {
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
                case TEST_COPY:
                {
                    deq_digi aa = deq_digi_copy(&a);
                    std::deque<DIGI> bb = b;
                    CHECK(aa, bb);
                    deq_digi_free(&aa);
                    CHECK(a, b);
                    break;
                }
                case TEST_SWAP:
                {
                    deq_digi aa = deq_digi_copy(&a);
                    deq_digi aaa = deq_digi_init();
                    std::deque<DIGI> bb = b;
                    std::deque<DIGI> bbb;
                    deq_digi_swap(&aaa, &aa);
                    std::swap(bb, bbb);
                    CHECK(aaa, bbb);
                    deq_digi_free(&aaa);
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(INT_MAX);
                        const size_t index = TEST_RAND(a.size);
                        deq_digi_it pos = deq_digi_begin(&a);
                        deq_digi_it_advance(&pos, index);
                        deq_digi_insert(&pos, digi_init(value));
                        b.insert(b.begin() + index, DIGI{value});
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT_INDEX:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        deq_digi_insert_index(&a, index, digi_init(value));
#ifdef DEBUG
                        std::deque<DIGI>::iterator iter =
#endif
                            b.insert(b.begin() + index, DIGI{value});
                        LOG ("STL insert %d at %ld:\n", value, std::distance(b.begin(),iter));
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT_COUNT:
                {
#ifdef LONG
                    size_t amount = TEST_RAND(1024);
#else
                    size_t amount = TEST_RAND(10);
#endif
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size); // allow end()
                    deq_digi_it pos = deq_digi_begin(&a);
                    deq_digi_it_advance(&pos, index);
                    if (!deq_digi_insert_count(&pos, amount, digi_init(value))) {
                        fprintf(stderr, "overflow size %zu + amount %zu\n", a.size, amount);
                        break;
                    }
                    LOG ("CTL insert_count at %zu, %zux %d:\n", pos.index, amount, value);
                    print_deq (&a);

                    if (amount)
                    {
#ifdef DEBUG
                        std::deque<DIGI>::iterator iter =
#endif
                            b.insert(b.begin() + index, amount, DIGI{value});
                        LOG ("STL insert %zux %d at %ld:\n", amount, value,
                             std::distance(b.begin(),iter));
                        //CHECK_ITER (pos, b, iter);
                        print_deque (b); // may be corrupt
                        CHECK(a, b);     // may be NULL
                    }
                    break;
                }
                case TEST_ERASE_INDEX: // 25
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        LOG ("erase_index %zu from %zu\n", index, a.size);
                        deq_digi_erase_index(&a, index);
                        b.erase(b.begin() + index);
                        //CHECK_ITER (pos, b, iter);
                    }
                    CHECK(a, b);
                    break;
#ifdef DEBUG
                case TEST_INSERT_RANGE: // 26
                {
                    size_t size2 = TEST_RAND(TEST_MAX_SIZE);
                    deq_digi aa = deq_digi_init_from(&a);
                    std::deque<DIGI> bb;
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    for(int i = 0; i < (int)size2; i++)
                    {
                        deq_digi_push_back(&aa, digi_init(i));
                        bb.push_back(DIGI{i});
                    }
                    print_deq(&a);
                    get_random_iters (&aa, &first_a, &last_a, bb, first_b, last_b);
                    print_deq(&aa);
                    const size_t index = TEST_RAND(a.size);
                    deq_digi_it pos = deq_digi_begin(&a);
                    deq_digi_it_advance(&pos, index);
                    LOG ("insert_range at %zu:\n", index);
                    // libstdc++  fails on empty (uninitialized) front or back values
                    b.insert(b.begin() + index, first_b, last_b);
                    deq_digi_insert_range(&pos, &first_a, &last_a);
                    print_deq(&a);
                    print_deque(b);
                    if (a.size != b.size())
                        fail++;
                    CHECK(a, b);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_ERASE_RANGE:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    if (a.size < 4)
                    {
                        deq_digi_resize(&a, 10, digi_init(value));
                        b.resize(10, DIGI{value});
                    }
                    deq_digi_it from, to;
                    const size_t index = TEST_RAND(a.size/2);
                    const size_t iend = index + TEST_RAND(a.size - index);
                    from = deq_digi_begin(&a);
                    deq_digi_it_advance(&from, index);
                    to = deq_digi_end(&a);
                    deq_digi_it_advance(&to, (long)iend - a.size);
                    LOG ("erase_range %zu of %zu\n", index, a.size);
                    deq_digi_it *pos = deq_digi_erase_range(&a, &from, &to);
                    LOG ("CTL erase_range [%lu - %lu):\n",
                         index, iend);
                    print_deq (&a);

                    std::deque<DIGI>::iterator iter =
                        b.erase(b.begin() + index, b.end() - iend);
                    LOG ("STL erase [%ld, %ld):\n", std::distance(b.begin(), iter), iend);
                    CHECK_ITER (*pos, b, iter);
                    print_deque (b);
                    if (a.size != b.size())
                        fail++;
                    CHECK(a, b);
                    break;
                }
#endif
                case TEST_EMPLACE:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    digi aa = digi_init(value);
                    if (a.size < 1)
                    {
                        deq_digi_push_front(&a, digi_init(value));
                        b.push_front(DIGI{value});
                    }
#ifdef DEBUG
                    if (a.size > 10)
                    {
                        deq_digi_resize(&a, 10, digi_init(0));
                        b.resize(10);
                    }
                    LOG("before emplace\n");
                    print_deq(&a);
#endif
                    assert(a.size > 0);
                    deq_digi_it pos = deq_digi_begin(&a);
                    deq_digi_it_advance(&pos, 1);
                    LOG("CTL emplace 1 %d\n", *aa.value);
                    deq_digi_emplace(&pos, &aa);
                    print_deq(&a);
                    LOG("STL emplace begin++ %d\n", *DIGI{value});
                    assert(b.size() > 0);
                    b.emplace(b.begin() + 1, DIGI{value});
                    print_deque(b);
                    if (!b.front().value)
                        fprintf(stderr, "!b.front().value size=%zu, index 1\n", b.size());
                    if (!deq_digi_front(&a)->value)
                        fprintf(stderr, "!deq_digi_front(&a)->value size=%zu, index %zu\n",
                                a.size, 1UL);
                    // b.front might fail with size=2, STL bug
                    if (b.size() == 2 && !*b.front().value)
                    {
                        fprintf(stderr, "Skip !*b.front().value size=2 STL bug\n");
                        deq_digi_clear(&a);
                        b.clear();
                    }
                    CHECK(a, b);
                    // may not delete, as emplace does not copy
                    //digi_free(&aa);
                    break;
                }
                case TEST_EMPLACE_FRONT:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    digi aa = digi_init(value);
                    deq_digi_emplace_front(&a, &aa);
                    b.emplace_front(DIGI{value});
                    CHECK(a, b);
                    break;
                }
                case TEST_EMPLACE_BACK:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    digi aa = digi_init(value);
                    deq_digi_emplace_back(&a, &aa);
                    b.emplace_back(DIGI{value});
                    CHECK(a, b);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    size_t assign_size = TEST_RAND(a.size) + 1;
                    deq_digi_assign(&a, assign_size, digi_init(value));
                    b.assign(assign_size, DIGI{value});
                    CHECK(a, b);
                    break;
                }
                case TEST_REMOVE_IF:
                {
                    deq_digi_remove_if(&a, digi_is_odd);
                    print_deq(&a);
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                    print_deque(b);
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE_IF:
                {
#if __cpp_lib_erase_if >= 202002L
                    size_t num_a = deq_digi_erase_if(&a, digi_is_odd);
                    size_t num_b = std::erase_if(b, DIGI_is_odd);
                    assert (num_a == num_b);
#else
                    deq_digi_erase_if(&a, digi_is_odd);
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
#endif
                    CHECK(a, b);
                    break;
                }
                case TEST_EQUAL:
                {
                    deq_digi aa = deq_digi_copy(&a);
                    std::deque<DIGI> bb = b;
                    assert(deq_digi_equal(&a, &aa));
                    assert(b == bb);
                    deq_digi_free(&aa);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                                 : *deq_digi_at(&a, index)->value;
                        digi key = digi_init(value);
                        deq_digi_it aa = deq_digi_find(&a, key);
                        auto bb = find(b.begin(), b.end(), DIGI{value});
                        bool found_a = !deq_digi_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa.ref->value == *bb->value);

                        a.equal = NULL;
                        aa = deq_digi_find(&a, key);
                        found_a = !deq_digi_it_done(&aa);
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa.ref->value == *bb->value);

                        digi_free(&key);
                        CHECK(a, b);
                    }
                    break;
                }
                case TEST_FIND_IF:
                {
                    deq_digi_it it = deq_digi_find_if(&a, digi_is_odd);
                    auto bb = std::find_if(b.begin(), b.end(), DIGI_is_odd);
                    if(bb == b.end())
                        assert(deq_digi_it_done(&it));
                    else
                        assert(*(it.ref->value) == *bb->value);
                    break;
                }
                case TEST_FIND_IF_NOT:
                {
                    deq_digi_it aa = deq_digi_find_if_not(&a, digi_is_odd);
                    auto bb = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
                    print_deq(&a);
                    print_deque(b);
                    CHECK_ITER(aa, b, bb);
                    if(bb == b.end())
                        assert(deq_digi_it_done(&aa));
                    else
                        assert(*(aa.ref->value) == *bb->value);
                    break;
                }
                case TEST_ALL_OF:
                {
                    bool is_a = deq_digi_all_of(&a, digi_is_odd);
                    bool is_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_ANY_OF:
                {
                    bool is_a = deq_digi_any_of(&a, digi_is_odd);
                    bool is_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_NONE_OF:
                {
                    bool is_a = deq_digi_none_of(&a, digi_is_odd);
                    bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_COUNT:
                {
                    int key = TEST_RAND(TEST_MAX_SIZE);
                    int aa = deq_digi_count(&a, digi_init(key));
                    int bb = std::count(b.begin(), b.end(), DIGI{key});
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF:
                {
                    size_t count_a = deq_digi_count_if(&a, digi_is_odd);
                    size_t count_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
                    assert(count_a == count_b);
                    break;
                }
                case TEST_FIND_RANGE:
                {
                    int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                        : random_element(&a);
                    digi key = digi_init(vb);
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = deq_digi_find_range(&first_a, &last_a, key);
                    auto it = find(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    digi_free (&key); // special
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_IF_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = deq_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                    auto it = find_if(first_b, last_b, DIGI_is_odd);
                    print_deq(&a);
                    print_deque(b);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_FIND_IF_NOT_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = deq_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                    auto it = find_if_not(first_b, last_b, DIGI_is_odd);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_ALL_OF_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = deq_digi_all_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = std::all_of(first_b, last_b, DIGI_is_odd);
                    if (aa != bb)
                    {
                        print_deq(&a);
                        print_deque(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_ANY_OF_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = deq_digi_any_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = std::any_of(first_b, last_b, DIGI_is_odd);
                    if (aa != bb)
                    {
                        print_deq(&a);
                        print_deque(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_NONE_OF_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = deq_digi_none_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = none_of(first_b, last_b, DIGI_is_odd);
                    if (aa != bb)
                    {
                        print_deq(&a);
                        print_deque(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t numa = deq_digi_count_if_range(&first_a, &last_a, digi_is_odd);
                    size_t numb = count_if(first_b, last_b, DIGI_is_odd);
                    if (numa != numb)
                    {
                        print_deq(&a);
                        print_deque(b);
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
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    // used to fail with 0,0 of 0
                    size_t numa = deq_digi_count_range(&first_a, &last_a, digi_init(v));
                    size_t numb = count(first_b, last_b, DIGI{v});
                    assert(numa == numb);
                    break;
                }
                case TEST_INCLUDES:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    bool a_found = deq_digi_includes(&a, &aa);
                    bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                    assert(a_found == b_found);
                    CHECK(aa, bb);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_INCLUDES_RANGE: // 51
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi_it first_a1, last_a1;
                    std::deque<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    deq_digi_it first_a2, last_a2;
                    std::deque<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);
                    print_deq(&a);
                    print_deq(&aa);

                    // deviates with aa: 0,0 of 1
                    bool a_found = deq_digi_includes_range(&first_a1, &first_a2);
                    bool b_found = std::includes(first_b1, last_b1, first_b2, last_b2);
                    assert(a_found == b_found);
                    CHECK(aa, bb);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_UNION:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi aaa = deq_digi_union(&a, &aa);
# ifndef _MSC_VER
                    std::deque<DIGI> bbb;
                    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                                   std::back_inserter(bbb));
                    CHECK(aaa, bbb);
# endif
                    CHECK(aa, bb);
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_INTERSECTION:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi aaa = deq_digi_intersection(&a, &aa);
#ifndef _MSC_VER
                    std::deque<DIGI> bbb;
                    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                          std::back_inserter(bbb));
                    CHECK(aaa, bbb);
# endif
                    CHECK(aa, bb);
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi aaa = deq_digi_symmetric_difference(&a, &aa);
# ifndef _MSC_VER
                    std::deque<DIGI> bbb;
                    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                                  std::back_inserter(bbb));
                    CHECK(aaa, bbb);
# endif
                    CHECK(aa, bb);
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    print_deq(&a);
                    deq_digi aaa = deq_digi_difference(&a, &aa);
#ifndef _MSC_VER
                    std::deque<DIGI> bbb;
                    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                        std::back_inserter(bbb));
                    CHECK(aaa, bbb);
# endif
                    CHECK(aa, bb);
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_UNION_RANGE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi_it first_a1, last_a1;
                    std::deque<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    deq_digi_it first_a2, last_a2;
                    std::deque<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_deq_range(first_a1);
                    print_deq_range(first_a2);
                    deq_digi aaa = deq_digi_union_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_deq(&aaa);

                    std::deque<DIGI> bbb;
                    LOG("STL b + bb\n");
                    print_deque(b);
                    print_deque(bb);
# ifndef _MSC_VER
                    std::set_union(first_b1, last_b1, first_b2, last_b2,
                                   std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_deque(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("union_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_INTERSECTION_RANGE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi_it first_a1, last_a1;
                    std::deque<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    deq_digi_it first_a2, last_a2;
                    std::deque<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_deq_range(first_a1);
                    print_deq_range(first_a2);
                    deq_digi aaa = deq_digi_intersection_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_deq(&aaa);

                    std::deque<DIGI> bbb;
                    LOG("STL b + bb\n");
                    print_deque(b);
                    print_deque(bb);
# ifndef _MSC_VER
                    std::set_intersection(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_deque(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE_RANGE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi_it first_a1, last_a1;
                    std::deque<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    deq_digi_it first_a2, last_a2;
                    std::deque<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                    print_deq_range(first_a1);
                    print_deq_range(first_a2);
                    deq_digi aaa = deq_digi_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa (%zu)\n", aa.size);
                    print_deq(&aaa);

                    std::deque<DIGI> bbb;
                    LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
                    print_deque(b);
                    print_deque(bb);
# ifndef _MSC_VER
                    std::set_difference(first_b1, last_b1, first_b2, last_b2,
                                        std::back_inserter(bbb));
                    LOG("STL => bbb (%zu)\n", bbb.size());
                    print_deque(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("difference_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE_RANGE:
                {
                    deq_digi aa;
                    std::deque<DIGI> bb;
                    setup_deque(&aa, bb);
                    deq_digi_sort(&a);
                    deq_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    deq_digi_it first_a1, last_a1;
                    std::deque<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    deq_digi_it first_a2, last_a2;
                    std::deque<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_deq_range(first_a1);
                    print_deq_range(first_a2);
                    deq_digi aaa = deq_digi_symmetric_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_deq(&aaa);

                    std::deque<DIGI> bbb;
                    LOG("STL b + bb\n");
                    print_deque(b);
                    print_deque(bb);
# ifndef _MSC_VER
                    std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_deque(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    deq_digi_free(&aaa);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_GENERATE:
                {
                    digi_generate_reset();
                    deq_digi_generate(&a, digi_generate);
                    digi_generate_reset();
                    std::generate(b.begin(), b.end(), DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    digi_generate_reset();
                    deq_digi_generate_range(&first_a, &last_a, digi_generate);
                    digi_generate_reset();
                    std::generate(first_b, last_b, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM:
                {
                    deq_digi aa = deq_digi_transform(&a, digi_untrans);
                    std::deque<DIGI> bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    deq_digi_free(&aa);
                    break;
                }
#ifdef DEBUG
                case TEST_GENERATE_N: // TEST=
                {
                    size_t count = TEST_RAND(20);
                    digi_generate_reset();
                    deq_digi_generate_n(&a, count, digi_generate);
                    digi_generate_reset();
                    std::generate_n(b.begin(), count, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_N_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t off = first_b - b.begin();
                    size_t count = TEST_RAND(20 - off);
                    digi_generate_reset();
                    deq_digi_generate_n_range(&first_a, count, digi_generate);
                    digi_generate_reset();
                    std::generate_n(first_b, count, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM_IT:
                {
                    deq_digi_it pos = deq_digi_begin(&a);
                    deq_digi_it_advance(&pos, 1);
                    deq_digi aa = deq_digi_transform_it(&a, &pos, digi_bintrans);
                    std::deque<DIGI> bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), DIGI_bintrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    deq_digi_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_RANGE:
                {
                    deq_digi_it first_a, last_a;
                    std::deque<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    deq_digi aa = deq_digi_init();
                    deq_digi_resize(&aa, last_b - first_b, digi_init(0));
                    deq_digi_it dest = deq_digi_begin(&aa);
                    deq_digi_it it = deq_digi_transform_range(&first_a, &last_a, dest, digi_untrans);
                    std::deque<DIGI> bb;
                    bb.resize(last_b - first_b);
                    auto iter = std::transform(first_b, last_b, b.begin()+1, bb.begin(), DIGI_bintrans);
                    CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
                    // heap use-after-free
                    CHECK(a, b);
                    deq_digi_free(&aa);
                    break;
                }
#if 0
                case TEST_FIND_END:
                {
                    if(a.size > 0)
                    {
                        deq_digi_it first_a, last_a;
                        deq_digi_it s_first, s_last;
                        deq_digi_it aa = deq_digi_find_end(&a, &s_first, &s_last);
                        auto bb = find_end(b.begin(), b.end(), ...);
                        bool found_a = !deq_digi_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*(aa->value) == *bb->value);
                    }
                    break;
                }
                case TEST_FIND_END_RANGE:
                {
                    deq_digi_it first_a, last_a, s_first_a, s_last_a;
                    std::deque<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = deq_digi_find_end_range(&first_a, &last_a, &s_first_a, &s_last_a);
                    auto it = find_end(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    CHECK(a, b);
# endif
                    break;
                }
                case TEST_FIND_END_IF_RANGE:
                {
                    deq_digi_it first_a, last_a, s_first, s_last;
                    std::deque<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = deq_digi_find_end_if_range(&first_a, &last_a, &s_first,
                                                         &s_last, digi_is_odd);
                    auto it = find_end(first_b, last_b, s_first_b, s_last_b, DIGI_is_odd);
                    CHECK_ITER(first_a, b, it);
                    digi_free (&key); // special
                    CHECK(a, b);
# endif
                    break;
                }
#endif // FIND_END 0

#endif // DEBUG

                default:
#ifdef DEBUG
                    printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
                    printf("unhandled testcase %d\n", which);
#endif
                    break;
            }
#ifdef DEBUG
            if (which < TEST_ERASE_RANGE)
#endif
                CHECK(a, b);
            deq_digi_free(&a);
        }
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
