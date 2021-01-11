#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/queue.h>

#include <queue>
#include <algorithm>

#define CHECK(_x, _y) {                                           \
    while(_x.size > 0) {                                          \
        assert(_x.size == _y.size());                             \
        assert(queue_digi_empty(&_x) == _y.empty());                \
        assert(*_y.front().value == *queue_digi_front(&_x)->value); \
        assert(*_y.back().value == *queue_digi_back(&_x)->value);   \
        _y.pop();                                                 \
        queue_digi_pop(&_x);                                        \
    }                                                             \
}

int
main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        queue_digi a = queue_digi_init();
        std::queue<DIGI> b;
        for(size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            queue_digi_push(&a, digi_init(value));
            b.push(DIGI{value});
        }
#define FOREACH_METH(TEST) \
        TEST(PUSH) \
        TEST(POP) \
        TEST(SWAP)
#define FOREACH_DEBUG(TEST) \
        TEST(EQUAL_RANGE) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
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
        TEST(COUNT_RANGE)
        
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
            case TEST_PUSH:
            {
                const int value = TEST_RAND(INT_MAX);
                b.push(DIGI{value});
                queue_digi_push(&a, digi_init(value));
                break;
            }
            case TEST_POP:
            {
                if(a.size > 0)
                {
                    b.pop();
                    queue_digi_pop(&a);
                }
                break;
            }
            case TEST_SWAP:
            {
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
#ifdef DEBUG // algorithm
            case TEST_EQUAL_RANGE:
            case TEST_FIND_RANGE:
            case TEST_FIND_IF:
            case TEST_FIND_IF_NOT:
            case TEST_FIND_IF_RANGE:
            case TEST_FIND_IF_NOT_RANGE:
            case TEST_ALL_OF:
            case TEST_ANY_OF:
            case TEST_NONE_OF:
            case TEST_ALL_OF_RANGE:
            case TEST_ANY_OF_RANGE:
            case TEST_NONE_OF_RANGE:
            case TEST_COUNT:
            case TEST_COUNT_IF:
            case TEST_COUNT_IF_RANGE:
            case TEST_COUNT_RANGE:
                break;
#endif
        }
        CHECK(a, b);
        queue_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
