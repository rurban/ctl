#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/stack.h>

#include <stack>
#include <algorithm>

#define CHECK(_x, _y) {                                        \
    while(_x.size > 0) {                                       \
        assert(_x.size == _y.size());                          \
        assert(stack_digi_empty(&_x) == _y.empty());           \
        assert(*_y.top().value == *stack_digi_top(&_x)->value);\
        _y.pop();                                              \
       stack_digi_pop(&_x);                                    \
    }                                                          \
}

int
main(void)
{
    INIT_SRAND;
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        stack_digi a = stack_digi_init();
        std::stack<DIGI> b;
        for(size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            stack_digi_push(&a, digi_init(value));
            b.push(DIGI{value});
        }
        enum
        {
            TEST_EMPTY,
            TEST_SIZE,
            TEST_TOP,
            TEST_PUSH,
            TEST_POP,
            TEST_SWAP,
            TEST_TOTAL,
        };
        int which = TEST_RAND(TEST_TOTAL);
        switch(which)
        {
            case TEST_PUSH:
            {
                const int value = TEST_RAND(INT_MAX);
                b.push(DIGI{value});
                stack_digi_push(&a, digi_init(value));
                CHECK(a, b);
                break;
            }
            case TEST_POP:
            {
                if(a.size > 0)
                {
                    b.pop();
                    stack_digi_pop(&a);
                    CHECK(a, b);
                }
                break;
            }
            case TEST_SWAP:
            {
                stack_digi aa = stack_digi_copy(&a);
                stack_digi aaa = stack_digi_init();
                std::stack<DIGI> bb = b;
                std::stack<DIGI> bbb;
                stack_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                stack_digi_free(&aaa);
                CHECK(a, b);
                break;
            }
        }
        CHECK(a, b);
        stack_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
