#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/stack.h>

#include <stack>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(EMPTY)                                                                                                        \
    TEST(SIZE)                                                                                                         \
    TEST(TOP)                                                                                                          \
    TEST(PUSH)                                                                                                         \
    TEST(POP)                                                                                                          \
    TEST(SWAP)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

// clang-format off
enum
{
    FOREACH_METH(GENERATE_ENUM)
    TEST_TOTAL
};
static const int number_ok = (int)TEST_TOTAL;
#ifdef DEBUG
static const char *test_names[] = {FOREACH_METH(GENERATE_NAME) ""};
#endif
// clang-format on

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        while (_x.size > 0)                                                                                            \
        {                                                                                                              \
            assert(_x.size == _y.size());                                                                              \
            assert(stack_digi_empty(&_x) == _y.empty());                                                               \
            assert(*_y.top().value == *stack_digi_top(&_x)->value);                                                    \
            _y.pop();                                                                                                  \
            stack_digi_pop(&_x);                                                                                       \
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
        stack_digi a = stack_digi_init();
        std::stack<DIGI> b;
        for (size_t pushes = 0; pushes < size; pushes++)
        {
            const int value = TEST_RAND(INT_MAX);
            stack_digi_push(&a, digi_init(value));
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
            stack_digi_push(&a, digi_init(value));
            break;
        }
        case TEST_POP: {
            if (a.size > 0)
            {
                b.pop();
                stack_digi_pop(&a);
            }
            break;
        }
        case TEST_SWAP: {
            stack_digi aa = stack_digi_copy(&a);
            stack_digi aaa = stack_digi_init();
            std::stack<DIGI> bb = b;
            std::stack<DIGI> bbb;
            stack_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            stack_digi_free(&aaa);
            break;
        }
        }
        CHECK(a, b);
        stack_digi_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
