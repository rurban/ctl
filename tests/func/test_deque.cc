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
        printf ("%zu: %d\n", i, b.at(i).value ? *b.at(i).value : -1);
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
        assert(*_y.front().value == *deq_digi_front(&_x)->value); \
        assert(*_y.back().value == *deq_digi_back(&_x)->value);   \
    }                                                             \
    std::deque<DIGI>::iterator _iter = _y.begin();                \
    foreach(deq_digi, &_x, _it) {                                 \
        assert(*_it.ref->value == *_iter->value);                 \
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
#define CHECK_ITER(cit,_y,iter)                                   \
    assert(cit->index == (size_t)std::distance(_y.begin(), iter))

#else

#define CHECK(_x, _y) {                                           \
    assert(_x.size == _y.size());                                 \
    assert(deq_digi_empty(&_x) == _y.empty());                    \
    if(_x.size > 0) {                                             \
        assert(*_y.front().value == *deq_digi_front(&_x)->value); \
        assert(*_y.back().value == *deq_digi_back(&_x)->value);   \
    }                                                             \
    std::deque<DIGI>::iterator _iter = _y.begin();                \
    foreach(deq_digi, &_x, _it) {                                 \
        if (*_it.ref->value != *_iter->value)                     \
            fprintf(stderr, "CTL %d at %lu vs STL %d\n",          \
                    *_it.ref->value, _it.index,                   \
                    *_iter->value);                               \
        assert(*_it.ref->value == *_iter->value);                 \
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
    if (cit->index != _dist)                                      \
        fprintf(stderr, "CTL iter %zu vs STL %zu\n",              \
                cit->index,_dist);                                \
    assert(cit->index == _dist);                                  \
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
    int test = -1;
    char *env = getenv ("TEST");
    if (env)
        sscanf(env, "%d", &test);
    size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    if (test >= 0)
        loops = 10;
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
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
            std::deque<DIGI> b;
            if(mode == MODE_DIRECT)
            {
                deq_digi_resize(&a, size, digi_init(0));
                b.resize(size);
            }
            if(mode == MODE_GROWTH)
            {
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    deq_digi_push_back(&a, digi_init(value));
                    b.push_back(DIGI{value});
                }
            }
            enum
            {
                TEST_PUSH_BACK,
                TEST_POP_BACK,
                TEST_PUSH_FRONT,
                TEST_POP_FRONT,
                TEST_CLEAR,
                TEST_ERASE,
                TEST_ERASE_IT, // 6
                TEST_INSERT_IT,
                TEST_INSERT_RANGE, // 8
#ifdef DEBUG
                TEST_INSERT_COUNT, // 9
                TEST_ERASE_RANGE,
#endif
                TEST_EMPLACE,
                TEST_EMPLACE_FRONT,
                TEST_EMPLACE_BACK,
                TEST_RESIZE,
                TEST_SHRINK_TO_FIT,
                TEST_SORT,
                TEST_RANGED_SORT,
                TEST_SORT_RANGE,
                TEST_COPY,
                TEST_SWAP,
                TEST_INSERT,
                TEST_ASSIGN,
                TEST_REMOVE_IF,
                TEST_EQUAL,
                TEST_FIND,
                TEST_TOTAL,
            };
            int which = TEST_RAND(TEST_TOTAL);
            if (test >= 0 && test < (int)TEST_TOTAL)
                which = test;
            LOG ("TEST %d\n", which);
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
                    deq_digi_sort(&a, digi_compare);
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
                        deq_digi_it cfrom = deq_digi_it_each(&a);
                        deq_digi_it cto = deq_digi_it_each(&a);
                        cfrom.index += 1;
                        // excluding to
                        cto.index = a.size - 3;
                        deq_digi_sort_range(&a, &cfrom, &cto, digi_compare);
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
                case TEST_INSERT_IT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        deq_digi_it *pos;
                        deq_digi_it it = deq_digi_it_each(&a);
                        deq_digi_it_advance(&it, index);
                        pos = deq_digi_insert_it(&a, &it, digi_init(value));
                        LOG ("CTL insert_it %d at %lu:\n", value, pos->index);
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
#ifdef DEBUG
                case TEST_INSERT_COUNT:
                {
#ifdef LONG
                    size_t amount = TEST_RAND(512);
#else
                    size_t amount = TEST_RAND(10);
#endif
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size - 1);
                    deq_digi_it *pos;
                    deq_digi_it it = deq_digi_it_each(&a);
                    deq_digi_it_advance(&it, index);
                    pos = deq_digi_insert_count(&a, &it, amount, digi_init(value));
                    LOG ("CTL insert_count at %lu, %zux %d:\n", pos->index, amount, value);
                    print_deq (&a);

                    std::deque<DIGI>::iterator iter =
                        b.insert(b.begin() + index, amount, DIGI{value});
                    LOG ("STL insert %zux %d at %ld:\n", amount, value,
                         std::distance(b.begin(),iter));
                    CHECK_ITER (pos, b, iter);
                    print_deque (b); // maybe corrupt
                    CHECK(a, b);
                    break;
                }
#endif
                case TEST_ERASE_IT:
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        LOG ("erase_it %zu from %zu\n", index, a.size);
                        deq_digi_it* pos;
                        deq_digi_it it = deq_digi_it_each(&a);
                        deq_digi_it_advance(&it, index);
                        pos = deq_digi_erase_it(&a, &it);
                        std::deque<DIGI>::iterator iter =
                            b.erase(b.begin() + index);
                        CHECK_ITER (pos, b, iter);
                    }
                    CHECK(a, b);
                    break;
                case TEST_INSERT_RANGE:
                {
                    const size_t index = std::min(TEST_RAND(a.size - 4), 2UL);
                    deq_digi aa = deq_digi_copy(&a);
                    std::deque<DIGI> bb = b;
                    deq_digi_it *pos;
                    if (a.size > 2)
                    {   // safe variant, from a copy
                        deq_digi_it it = deq_digi_it_each(&a);
                        deq_digi_it from = deq_digi_it_each(&aa);
                        deq_digi_it end = deq_digi_it_each(&aa);
                        deq_digi_it_advance(&it, 1);
                        deq_digi_it_advance(&from, index);
                        end.index = a.size;
                        end.done = 1;
                        pos = deq_digi_insert_range(&a, &it, &from, &end);
                        LOG ("CTL insert_range safe at %lu, [%lu - %lu):\n", pos->index,
                             from.index, end.index);
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
                        deq_digi_it it = deq_digi_it_each(&a);
                        deq_digi_it from = deq_digi_it_each(&a);
                        deq_digi_it end = deq_digi_it_each(&a);
                        deq_digi_it_advance(&it, 1);
                        deq_digi_it_advance(&from, index);
                        deq_digi_it_advance(&end, a.size - 1);
                        pos = deq_digi_insert_range(&a, &it, &from, &end);
                        LOG ("CTL insert_range unsafe at %lu, [%lu - %lu):\n", pos->index,
                             from.index, end.index);
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
#ifdef DEBUG
                case TEST_ERASE_RANGE:
                    LOG ("erase_range\n");
                    break;
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
                    deq_digi_resize(&a, 10, digi_init(0));
                    b.resize(10);
                    LOG("before emplace\n");
                    print_deq(&a);
#endif
                    deq_digi_it it = deq_digi_it_each(&a);
                    deq_digi_it_advance(&it, 1);
                    LOG("CTL emplace 1 %d\n", *aa.value);
                    deq_digi_emplace(&a, &it, &aa);
                    print_deq(&a);
                    LOG("STL emplace begin++ %d\n", *DIGI{value});
                    b.emplace(b.begin() + 1, DIGI{value});
                    print_deque(b);
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
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                    CHECK(a, b);
                    break;
                }
                case TEST_EQUAL:
                {
                    deq_digi aa = deq_digi_copy(&a);
                    std::deque<DIGI> bb = b;
                    assert(deq_digi_equal(&a, &aa, digi_equal));
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
                        digi* aa = deq_digi_find(&a, key, digi_equal);
                        auto bb = std::find(b.begin(), b.end(), DIGI{value});
                        bool found_a = aa != NULL;
                        bool found_b = bb != b.end();
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
