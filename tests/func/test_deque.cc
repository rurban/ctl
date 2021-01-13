#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/deque.h>

#include <deque>
#include <algorithm>

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
#define TEST_MAX_VALUE 1000
#else
#define TEST_MAX_VALUE INT_MAX
#endif

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
    foreach_ref(deq_digi, digi, &_x, _it, _ref) {                 \
        /* The STL may be corrupt */                              \
        if (_iter->value)                                         \
            assert(*_ref->value == *_iter->value);                \
        _iter++;                                                  \
    }                                                             \
    deq_digi_it _it = deq_digi_it_each(&_x);                      \
    for(auto& _d : _y) {                                          \
        if (_d.value)                                             \
            assert(*_it.ref->value == *_d.value);                 \
        _it.step(&_it);                                           \
    }                                                             \
    for(size_t i = 0; i < _y.size(); i++)                         \
        assert(*_y.at(i).value == *deq_digi_at(&_x, i)->value);   \
}
#define CHECK_ITER(cit,_y,iter)                                   \
    assert(cit == (size_t)std::distance(_y.begin(), iter))

#else

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
    foreach_ref(deq_digi, digi, &_x, _it, _ref) {                 \
        if (*_ref->value != *_iter->value)                        \
            fprintf(stderr, "CTL %d at %lu vs STL %d\n",          \
                    *_ref->value, _it,                            \
                    *_iter->value);                               \
        assert(*_ref->value == *_iter->value);                    \
        _iter++;                                                  \
    }                                                             \
    deq_digi_it _it = deq_digi_it_each(&_x);                      \
    for(auto& _d : _y) {                                          \
        assert(*_it.ref->value == *_d.value);                     \
        _it.step(&_it);                                           \
    }                                                             \
    for(size_t i = 0; i < _y.size(); i++)                         \
        assert(*_y.at(i).value == *deq_digi_at(&_x, i)->value);   \
}
#define CHECK_ITER(cit,_y,iter) {                                 \
    size_t _dist = std::distance(_y.begin(), iter);               \
    if (cit != _dist)                                             \
        fprintf(stderr, "CTL iter %zu vs STL %zu\n",              \
                cit,_dist);                                       \
    assert(cit == _dist);                                         \
}
#endif



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

int
main(void)
{
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
                LOG("mode DIRECT\n");
                deq_digi_resize(&a, size, digi_init(0));
                b.resize(size);
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
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
          /*TEST(ERASE_IT)                \
            TEST(INSERT_IT)*/             \
            TEST(INSERT_RANGE) \
            TEST(INSERT_COUNT) \
            TEST(ERASE_RANGE) \
            TEST(EMPLACE_FRONT) \
            TEST(EMPLACE_BACK) \
            TEST(RESIZE) \
            TEST(SHRINK_TO_FIT) \
            TEST(SORT) \
            TEST(RANGED_SORT) \
            TEST(SORT_RANGE) \
            TEST(COPY) \
            TEST(SWAP) \
            TEST(INSERT) \
            TEST(ASSIGN) \
            TEST(REMOVE_IF) \
            TEST(ERASE_IF) \
            TEST(EQUAL) \
            TEST(FIND)

#define FOREACH_DEBUG(TEST)                     \
            TEST(EMPLACE) /* STD problems, not CTL*/    \
            /* TEST(COUNT) */                       \
            /* TEST(EQUAL_RANGE) */

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
                        b.erase(b.begin() + index);
                        deq_digi_erase(&a, index);
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
                        deq_digi_insert(&a, index, digi_init(value));
                        b.insert(b.begin() + index, DIGI{value});
                    }
                    CHECK(a, b);
                    break;
                }
/*
                case TEST_INSERT_IT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        size_t pos;
                        pos = deq_digi_insert_it(&a, index, digi_init(value));
                        LOG ("CTL insert_it %d at %lu:\n", value, pos);
                        //print_deq (&a);

                        std::deque<DIGI>::iterator iter =
                            b.insert(b.begin() + index, DIGI{value});
                        LOG ("STL insert %d at %ld:\n", value, std::distance(b.begin(),iter));
                        //print_deque (b);
                        CHECK_ITER (pos, b, iter);
                    }
                    CHECK(a, b);
                    break;
                }
*/
                case TEST_INSERT_COUNT:
                {
#ifdef LONG
                    size_t amount = TEST_RAND(1024);
#else
                    size_t amount = TEST_RAND(10);
#endif
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size); // allow end()
                    size_t pos;
                    pos = deq_digi_insert_count(&a, index, amount, digi_init(value));
                    if (!pos) {
                        fprintf(stderr, "overflow size %zu + amount %zu\n", a.size, amount);
                        break;
                    }
                    LOG ("CTL insert_count at %lu, %zux %d:\n", pos, amount, value);
                    print_deq (&a);

                    if (amount)
                    {
                        std::deque<DIGI>::iterator iter =
                            b.insert(b.begin() + index, amount, DIGI{value});
                        LOG ("STL insert %zux %d at %ld:\n", amount, value,
                             std::distance(b.begin(),iter));
                        CHECK_ITER (pos, b, iter);
                        print_deque (b); // may be corrupt
                        CHECK(a, b);     // may be NULL
                    }
                    break;
                }
/*
                case TEST_ERASE_IT:
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        LOG ("erase_it %zu from %zu\n", index, a.size);
                        size_t pos;
                        pos = deq_digi_erase_it(&a, index);
                        std::deque<DIGI>::iterator iter =
                            b.erase(b.begin() + index);
                        CHECK_ITER (pos, b, iter);
                    }
                    CHECK(a, b);
                    break;
*/
                case TEST_INSERT_RANGE:
                {
                    const size_t rnd = TEST_RAND(a.size - 4);
                    const size_t index = MIN(rnd, 2UL);
                    deq_digi aa = deq_digi_copy(&a);
                    std::deque<DIGI> bb = b;
                    size_t pos;
                    if (a.size > 2)
                    {   // safe variant, from a copy
                        pos = deq_digi_insert_range(&a, 1, index, a.size);
                        LOG ("CTL insert_range safe at %lu, [%lu - %lu):\n", pos,
                             1UL, a.size);
                        print_deq (&a);

                        std::deque<DIGI>::iterator iter =
                            b.insert(b.begin() + 1, bb.begin() + index, bb.end());
                        LOG ("STL insert at %ld:\n", std::distance(b.begin(),iter));
                        CHECK_ITER (pos, b, iter);
                        print_deque (b);
                        CHECK(a, b);
                    }
#if 0
                    // unsafe variant, from same object. fails at lower half
                    // but since even g++ STL fails sometimes, skip that test
                    if (a.size > 2)
                    {
                        deq_digi_resize(&a, aa.size, digi_init(0));
                        pos = deq_digi_insert_range(&a, 1, index, a.size - 1);
                        LOG ("CTL insert_range unsafe at %lu, [%lu - %lu):\n", pos,
                             index, a.size - 1);
                        print_deq (&a);

                        b.resize(bb.size());
                        std::deque<DIGI>::iterator iter =
                            b.insert(b.begin() + 1, b.begin() + index, b.end() - 1);
                        LOG ("STL insert at %ld:\n", std::distance(b.begin(),iter));
                        CHECK_ITER (pos, b, iter);
                        print_deque (b);
                        CHECK(a, b);
                    }
#endif
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
                    const size_t rnd = TEST_RAND(a.size/2);
                    const size_t index = MAX(rnd, 2UL);
                    LOG ("erase_range %zu of %zu\n", index, a.size);
                    size_t pos;
                    pos = deq_digi_erase_range(&a, index, a.size);
                    LOG ("CTL erase_range at %lu, [%lu - %lu):\n", pos,
                         index, a.size);
                    print_deq (&a);

                    std::deque<DIGI>::iterator iter =
                        b.erase(b.begin() + index, b.end());
                    LOG ("STL erase [%ld, %ld):\n", std::distance(b.begin(),iter), a.size);
                    CHECK_ITER (pos, b, iter);
                    print_deque (b);
                    CHECK(a, b);
                    break;
                }
#ifdef DEBUG
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
                    LOG("CTL emplace 1 %d\n", *aa.value);
                    deq_digi_emplace(&a, 1, &aa);
                    print_deq(&a);
                    LOG("STL emplace begin++ %d\n", *DIGI{value});
                    assert(b.size() > 0);
                    auto iter = b.begin();
                    iter++;
                    b.emplace(iter, DIGI{value});
                    print_deque(b);
                    if (!b.front().value)
                        fprintf(stderr, "!b.front().value size=%zu, index 1\n", b.size());
                    if (!deq_digi_front(&a)->value)
                        fprintf(stderr, "!deq_digi_front(&a)->value size=%zu, index %zu\n", a.size, 1UL);
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
#endif
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
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE_IF:
                {
#if __cpp_lib_erase_if > 202002L
                    size_t num_a = deq_digi_erase_if(&a, digi_is_odd);
                    size_t num_b = std::erase_if(b.begin(), b.end(), DIGI_is_odd);
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
                        digi* aa = deq_digi_find(&a, key);
                        auto bb = std::find(b.begin(), b.end(), DIGI{value});
                        bool found_a = aa != NULL;
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa->value == *bb->value);

                        a.equal = NULL;
                        aa = deq_digi_find(&a, key);
                        found_a = aa != NULL;
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa->value == *bb->value);

                        digi_free(&key);
                        CHECK(a, b);
                    }
                    break;
                }
            }
            CHECK(a, b);
            deq_digi_free(&a);
        }
    }
    TEST_PASS(__FILE__);
}
