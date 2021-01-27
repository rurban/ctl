#include "../test.h"
#include "digi.hh"

static inline int
digi_key_compare(digi* a, digi* b)
{
    return (*a->value == *b->value) ? 0 : (*a->value < *b->value) ? -1 : 1;
}

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/set.h>

#include <set>
#include <algorithm>
#include <iterator>

#define CHECK(_x, _y) {                           \
    assert(_x.size == _y.size());                 \
    std::set<DIGI>::iterator _iter = _y.begin();  \
    foreach(set_digi, &_x, _it) {                 \
        assert(*_it.ref->value == *_iter->value); \
        _iter++;                                  \
    }                                             \
    set_digi_it _it = set_digi_it_each(&_x);      \
    for(auto& _d : _y) {                          \
        assert(*_it.ref->value == *_d.value);     \
        _it.step(&_it);                           \
    }                                             \
}

static void
setup_sets(set_digi* a, std::set<DIGI>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = set_digi_init(digi_key_compare);
    for(size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        set_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
}

int
main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        set_digi a;
        std::set<DIGI> b;
        setup_sets(&a, b);
#define FOREACH_METH(TEST) \
        TEST(SELF) \
        TEST(INSERT) \
        TEST(ERASE) \
        TEST(REMOVE_IF) \
        TEST(CLEAR) \
        TEST(SWAP) \
        TEST(COUNT) \
        TEST(CONTAINS) \
        TEST(FIND) \
        TEST(COPY) \
        TEST(EQUAL) \
        TEST(UNION) \
        TEST(INTERSECTION) \
        TEST(SYMMETRIC_DIFFERENCE) \
        TEST(DIFFERENCE)
#define FOREACH_DEBUG(TEST) \
        /* TEST(EMPLACE) */ \
        /* TEST(EXTRACT) */ \
        /* TEST(MERGE) */ \
        /* TEST(ERASE_IF) */ \
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
            case TEST_SELF:
            {
                set_digi aa = set_digi_copy(&a);
                foreach(set_digi, &aa, it)
                    assert(set_digi_find(&a, *it.ref));
                foreach(set_digi, &a, it)
                    set_digi_erase(&aa, *it.ref);
                assert(set_digi_empty(&aa));
                set_digi_free(&aa);
                break;
            }
            case TEST_INSERT:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                set_digi_insert(&a, digi_init(vb));
                b.insert(DIGI{vb});
                break;
            }
            case TEST_ERASE:
            {
                const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
                for(size_t i = 0; i < erases; i++)
                    if(a.size > 0)
                    {
                        const int key = TEST_RAND(TEST_MAX_SIZE);
                        digi kd = digi_init(key);
                        set_digi_erase(&a, kd);
                        b.erase(DIGI{key});
                        CHECK(a, b);
                        digi_free(&kd);
                    }
                break;
            }
            case TEST_REMOVE_IF:
            {
                size_t b_erases = 0;
                {   // C++20 STD::ERASE_IF
                    auto iter = b.begin();
                    auto end = b.end();
                    while(iter != end)
                    {
                        if(*iter->value % 2)
                        {
                            iter = b.erase(iter);
                            b_erases++;
                        }
                        else
                            iter++;
                    }
                }
                size_t a_erases = set_digi_remove_if(&a, digi_is_odd);
                assert(a_erases == b_erases);
                break;
            }
            case TEST_CLEAR:
            {
                b.clear();
                set_digi_clear(&a);
                break;
            }
            case TEST_SWAP:
            {
                set_digi aa = set_digi_copy(&a);
                set_digi aaa = set_digi_init(digi_key_compare);
                std::set<DIGI> bb = b;
                std::set<DIGI> bbb;
                set_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
                break;
            }
            case TEST_COUNT:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = set_digi_count(&a, digi_init(key));
                int bb = b.count(DIGI{key});
                assert(aa == bb);
                CHECK(a, b);
                break;
            }
            case TEST_CONTAINS: // C++20
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = set_digi_contains(&a, digi_init(key));
#if defined(__cpp_lib_erase_if) && __cpp_lib_erase_if > 202002L
                int bb = b.contains(DIGI{key});
#else
                int bb = b.count(DIGI{key}) == 1;
#endif
                assert(aa == bb);
                break;
            }
            case TEST_FIND:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                digi kd = digi_init(key);
                set_digi_node* aa = set_digi_find(&a, kd);
                auto bb = b.find(DIGI{key});
                if(bb == b.end())
                    assert(set_digi_end(&a) == aa);
                else
                    assert(*bb->value == *aa->key.value);
                CHECK(a, b);
                digi_free(&kd);
                break;
            }
            case TEST_COPY:
            {
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                CHECK(aa, bb);
                set_digi_free(&aa);
                break;
            }
            case TEST_EQUAL:
            {
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                assert(set_digi_equal(&a, &aa));
                assert(b == bb);
                set_digi_free(&aa);
                break;
            }
            case TEST_UNION:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_union(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_intersection(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_symmetric_difference(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_difference(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
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
            case TEST_COUNT_IF:
            case TEST_COUNT_IF_RANGE:
            case TEST_COUNT_RANGE:
                printf("nyi\n");
                break;
#endif
        }
        CHECK(a, b);
        set_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
