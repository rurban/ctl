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

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EMPTY)

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
static const int number_ok = (int)TEST_TOTAL;
#ifdef DEBUG
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""
};
// clang-format on

#define TEST_MAX_VALUE 100
#else
#define TEST_MAX_VALUE INT_MAX
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
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        digi v1, *v1p;
        DIGI v2;
        pqu_digi a, aa, aaa;
        std::priority_queue<DIGI> b, bb, bbb;
        const int value = TEST_RAND(TEST_MAX_VALUE);

        a = pqu_digi_init(digi_compare);

        for (size_t pushes = 0; pushes < size; pushes++)
        {
            const int v = TEST_RAND(TEST_MAX_VALUE);
            pqu_digi_push(&a, digi_init(v));
            b.push(DIGI{v});
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
                v1p = pqu_digi_top(&a);
                v2 = b.top();
                assert(*v1p->value == *v2.value);
            }
            break;
        }
        case TEST_PUSH: {
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
            aa = pqu_digi_copy(&a);
            aaa = pqu_digi_init(digi_compare);
            bb = b;
            pqu_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            pqu_digi_free(&aaa);
            break;
        }
        case TEST_EMPLACE: {
            v1 = digi_init(value);
#if __cpp_lib_erase_if >= 202002L
            b.emplace(DIGI{value});
#else
            b.push(DIGI{value});
#endif
            pqu_digi_emplace(&a, &v1);
            break;
        }
#ifdef DEBUG
        case TEST_EMPTY: {
            aa = pqu_digi_copy(&a);
            while (aa.size > 0)
            {
                pqu_digi_pop(&aa);
            }
            bb = b;
            while (bb.size() > 0)
            {
                bb.pop();
            }
            assert(!pqu_digi_empty(&a));
            assert(pqu_digi_empty(&aa));
            assert(b.empty());
            pqu_digi_free(&aa);
        }
#endif
        }
        CHECK(a, b);
        pqu_digi_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
