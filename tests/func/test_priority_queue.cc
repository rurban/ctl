#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/priority_queue.h>

#include <queue>

#define CHECK(_x, _y) {                                       \
    while(_x.size > 0) {                                      \
        assert(_x.size == _y.size());                         \
        assert(pqu_digi_empty(&_x) == _y.empty());            \
        assert(*_y.top().value == *pqu_digi_top(&_x)->value); \
        _y.pop();                                             \
        pqu_digi_pop(&_x);                                    \
    }                                                         \
}

int
main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        pqu_digi a = pqu_digi_init(digi_compare);
        std::priority_queue<DIGI> b;
        for(size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            pqu_digi_push(&a, digi_init(value));
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
                pqu_digi_push(&a, digi_init(value));
                break;
            }
            case TEST_POP:
            {
                if(a.size > 0)
                {
                    b.pop();
                    pqu_digi_pop(&a);
                }
                break;
            }
            case TEST_SWAP:
            {
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
        }
        CHECK(a, b);
        pqu_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
