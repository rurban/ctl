#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/queue.h>

#include <queue>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH)                                                                                                         \
    TEST(POP)                                                                                                          \
    TEST(SWAP)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

enum
{
    FOREACH_METH(GENERATE_ENUM)
    TEST_TOTAL
};
static const int number_ok = (int)TEST_TOTAL;
#ifdef DEBUG
static const char *test_names[] = {FOREACH_METH(GENERATE_NAME)
    ""};
#endif


#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        while (_x.size > 0)                                                                                            \
        {                                                                                                              \
            assert(_x.size == _y.size());                                                                              \
            assert(queue_digi_empty(&_x) == _y.empty());                                                               \
            assert(*_y.front().value == *queue_digi_front(&_x)->value);                                                \
            assert(*_y.back().value == *queue_digi_back(&_x)->value);                                                  \
            _y.pop();                                                                                                  \
            queue_digi_pop(&_x);                                                                                       \
        }                                                                                                              \
    }

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        queue_digi a = queue_digi_init();
        std::queue<DIGI> b;
        for (size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            queue_digi_push(&a, digi_init(value));
            b.push(DIGI{value});
        }
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        }
        else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        LOG("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
        RECORD_WHICH;
        switch (which)
        {
        case TEST_PUSH: {
            const int value = TEST_RAND(INT_MAX);
            b.push(DIGI{value});
            queue_digi_push(&a, digi_init(value));
            break;
        }
        case TEST_POP: {
            if (a.size > 0)
            {
                b.pop();
                queue_digi_pop(&a);
            }
            break;
        }
        case TEST_SWAP: {
            queue_digi aa = queue_digi_copy(&a);
            queue_digi aaa = queue_digi_init();
            std::queue<DIGI> bb = b;
            std::queue<DIGI> bbb;
            queue_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            queue_digi_free(&aaa);
            break;
        }
        }
        CHECK(a, b);
        queue_digi_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
