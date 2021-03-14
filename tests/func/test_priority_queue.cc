#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/priority_queue.h>

#include <queue>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(TOP)                                                                                                          \
    TEST(PUSH)                                                                                                         \
    TEST(POP)                                                                                                          \
    TEST(EMPLACE)                                                                                                      \
    TEST(SWAP)
#define FOREACH_DEBUG(TEST)

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
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
#ifdef DEBUG
static const char *test_names[] = {FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        while (_x.size > 0)                                                                                            \
        {                                                                                                              \
            assert(_x.size == _y.size());                                                                              \
            assert(pqu_digi_empty(&_x) == _y.empty());                                                                 \
            assert(*_y.top().value == *pqu_digi_top(&_x)->value);                                                      \
            _y.pop();                                                                                                  \
            pqu_digi_pop(&_x);                                                                                         \
        }                                                                                                              \
    }

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for (size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        pqu_digi a = pqu_digi_init(digi_compare);
        std::priority_queue<DIGI> b;
        for (size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            pqu_digi_push(&a, digi_init(value));
            b.push(DIGI{value});
        }
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        } else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        LOG("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
        RECORD_WHICH;
        switch (which)
        {
        case TEST_TOP: {
            if (a.size > 0)
            {
                DIGI bb = b.top();
                digi *aa = pqu_digi_top(&a);
                assert(*bb.value == *aa->value);
            }
            break;
        }
        case TEST_PUSH: {
            const int value = TEST_RAND(INT_MAX);
            b.push(DIGI{value});
            pqu_digi_push(&a, digi_init(value));
            break;
        }
        case TEST_POP: {
            if (a.size > 0)
            {
                b.pop();
                pqu_digi_pop(&a);
            }
            break;
        }
        case TEST_SWAP: {
            pqu_digi aa = pqu_digi_copy(&a);
            pqu_digi aaa = pqu_digi_init(digi_compare);
            std::priority_queue<DIGI> bb = b;
            std::priority_queue<DIGI> bbb;
            pqu_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            pqu_digi_free(&aaa);
            break;
        }
        case TEST_EMPLACE: {
            const int value = TEST_RAND(INT_MAX);
            digi bb = digi_init(value);
#if __cpp_lib_erase_if >= 202002L
            b.emplace(DIGI{value});
#else
            b.push(DIGI{value});
#endif
            pqu_digi_emplace(&a, &bb);
            break;
        }
        }
        CHECK(a, b);
        pqu_digi_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
