#include "../test.h"
#include "digi.hh"

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/unordered_set.h>

#include <unordered_set>
#include <algorithm>

#define CHECK(_x, _y) {                                                \
    assert(_x.size == _y.size());                                      \
    if(_x.size > 0)                                                    \
    {                                                                  \
        size_t a_found = 0;                                            \
        size_t b_found = 0;                                            \
        foreach(uset_digi, &_x, it)                                    \
        {                                                              \
            auto found = _y.find(DIGI(*it.ref->value));                \
            assert(found != _y.end());                                 \
            a_found++;                                                 \
        }                                                              \
        for(auto x : _y)                                               \
        {                                                              \
            digi d = digi_init(*x.value);                              \
            uset_digi_node* found = uset_digi_find(&_x, d);            \
            assert(found != NULL);                                     \
            digi_free(&d);                                             \
            b_found++;                                                 \
        }                                                              \
        assert(a_found == b_found);                                    \
        /* only if we use the very same policies                      \
        assert(_x.bucket_count == _y.bucket_count());                  \
        for(size_t _i = 0; _i < _x.bucket_count; _i++)                 \
            assert(uset_digi_bucket_size(&_x, _i) == _y.bucket_size(_i));\
        */                                                              \
    }                                                                  \
}

#ifdef DEBUG
void print_uset(uset_digi* a)
{
    int i = 0;
    foreach(uset_digi, a, it)
        printf("%d: %d [%zu]\n", i++, *it.ref->value, it.bucket_index);
    printf("--\n");
}
void print_unordered_set(std::unordered_set<DIGI,DIGI_hash> b)
{
    int i = 0;
    for(auto& x : b)
        printf("%d: %d\n", i++, *x.value);
    printf("--\n");
}
#else
#define print_uset(aa)
#define print_unordered_set(bb)
#endif

static void
setup_sets(uset_digi* a, std::unordered_set<DIGI,DIGI_hash>& b)
{
    size_t size = TEST_RAND(TEST_MAX_SIZE);
#ifdef DEBUG
    size = 10;
#endif
    LOG ("\nSETUP_SETS %lu\n", size);
    *a = uset_digi_init(digi_hash, digi_equal);
    // TODO a->equal = digi_equal
#ifdef DEBUG
    //uset_digi_rehash(a, size * 2);
#endif
    for(size_t inserts = 0; inserts < size; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        uset_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
}

static void
test_small_size(void)
{
    uset_digi a = uset_digi_init(digi_hash, digi_equal);
    // TODO a.equal = digi_equal
    uset_digi_insert(&a, digi_init(1));
    uset_digi_insert(&a, digi_init(2));
    print_uset(&a);
    uset_digi_free(&a);
}

int
main(void)
{
    INIT_SRAND;
    test_small_size();
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        uset_digi a;
        std::unordered_set<DIGI,DIGI_hash> b;
        setup_sets(&a, b);

#define FOREACH_METH(TEST) \
        TEST(INSERT) \
        TEST(ERASE_IF) \
        TEST(CONTAINS) \
        TEST(ERASE) \
        TEST(CLEAR) \
        TEST(SWAP) \
        TEST(COUNT) \
        TEST(FIND) \
        TEST(COPY) \
        TEST(EQUAL) \
        TEST(REHASH) \
        TEST(RESERVE) \
        TEST(UNION)

#define FOREACH_DEBUG(TEST) \
        /* TEST(EMPLACE) */ \
        /* TEST(EXTRACT) */ \
        /* TEST(MERGE) */ \
        /* TEST(REMOVE_IF) */ \
        /* TEST(SYMMETRIC_DIFFERENCE) */    \
        /* TEST(INTERSECTION)  */ \
        /* TEST(DIFFERENCE)  */ \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(COUNT_IF)

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
        LOG ("TEST=%d %s (%zu, %zu)\n", which, test_names[which], a.size, a.bucket_count);
        switch(which)
        {
            case TEST_INSERT:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                uset_digi_insert(&a, digi_init(vb));
                b.insert(DIGI{vb});
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_IF:
            {
                size_t a_erases = uset_digi_erase_if(&a, digi_is_odd);
#if defined(__cpp_lib_erase_if) && __cpp_lib_erase_if > 202002L
                size_t b_erases = std::erase_if(b, DIGI_is_odd); //C++20
#else
                size_t b_erases = 0;
                {
                    auto iter = b.begin();
                    auto end = b.end();
                    while(iter != end)
                    {
                        if((int) *iter->value % 2)
                        {
                            iter = b.erase(iter);
                            b_erases += 1;
                        }
                        else
                            iter++;
                    }
                }
#endif
                assert(a_erases == b_erases);
                CHECK(a, b);
                break;
            }
            case TEST_CONTAINS:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                bool a_has = uset_digi_contains(&a, digi_init(vb));
#ifdef __cpp_lib_erase_if
                bool b_has = b.contains(DIGI{vb}); //C++20
#else
                bool b_has = b.count(DIGI{vb}) == 1;
#endif
                assert(a_has == b_has);
                CHECK(a, b);
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
                        uset_digi_erase(&a, kd);
                        b.erase(DIGI{key});
                        CHECK(a, b);
                        digi_free(&kd);
                    }
                CHECK(a, b);
                break;
            }
            case TEST_REHASH:
            {
                size_t size = uset_digi_size(&a);
                LOG (" -> %lu\n", size);
                b.rehash(size * 2);
                uset_digi_rehash(&a, size * 2);
                CHECK(a, b);
                break;
            }
            case TEST_RESERVE:
            {
                size_t size = uset_digi_size(&a);
                float load = uset_digi_load_factor(&a);
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                const size_t reserve = size * 2 / load;
                LOG ("load %f\n", load);
                bb.reserve(reserve);
                LOG ("STL reserve by %zu %zu\n", reserve, bb.bucket_count());
                LOG ("before\n");
                print_uset(&a);
                uset_digi aa = uset_digi_copy(&a);
                LOG ("copy\n");
                print_uset(&aa);
                uset_digi_reserve(&aa, reserve);
                LOG ("CTL reserve by %zu %zu\n", reserve, aa.bucket_count);
                print_uset(&aa);
                CHECK(aa, bb);
                uset_digi_free(&aa);
                break;
            }
            case TEST_SWAP:
            {
                uset_digi aa = uset_digi_copy(&a);
                uset_digi aaa = uset_digi_init(digi_hash, digi_equal);
                // TODO a.equal = digi_equal
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                std::unordered_set<DIGI,DIGI_hash> bbb;
                uset_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                CHECK(a, b);
                break;
            }
            case TEST_COUNT:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = uset_digi_count(&a, digi_init(key));
                int bb = b.count(DIGI{key});
                assert(aa == bb);
                CHECK(a, b);
                break;
            }
            case TEST_FIND:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                uset_digi_node* aa = uset_digi_find(&a, digi_init(key));
                auto bb = b.find(DIGI{key});
                if(bb == b.end())
                    assert(uset_digi_end(&a) == aa);
                else
                    assert(*bb->value == *aa->value.value);
                CHECK(a, b);
                break;
            }
            case TEST_CLEAR:
            {
                b.clear();
                uset_digi_clear(&a);
                CHECK(a, b);
                break;
            }
            case TEST_COPY:
              { // C++20
                uset_digi aa = uset_digi_copy(&a);
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                CHECK(aa, bb);
                uset_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL:
            {
                uset_digi aa = uset_digi_copy(&a);
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                print_uset(&aa);
                print_unordered_set(bb);
                assert(uset_digi_equal(&a, &aa));
                assert(b == bb);
                uset_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_UNION:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                uset_digi aaa = uset_digi_union(&a, &aa);
                std::unordered_set<DIGI,DIGI_hash> bbb;
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
#if 0
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                uset_digi aaa = uset_digi_symmetric_difference(&a, &aa);
                std::unordered_set<DIGI,DIGI_hash> bbb;
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
            case TEST_INTERSECTION:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                uset_digi aaa = uset_digi_intersection(&a, &aa);
                std::unordered_set<DIGI,DIGI_hash> bbb;
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb); // TODO size error
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                uset_digi aaa = uset_digi_difference(&a, &aa);
                print_uset(&aaa);
                std::unordered_set<DIGI,DIGI_hash> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                print_unordered_set(bbb);
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
#endif
#if 0
            case TEST_EMPLACE:
            case TEST_EXTRACT:
            case TEST_MERGE:
            case TEST_CONTAINS:
            case TEST_EQUAL_RANGE:
                break;
#endif
#ifdef DEBUG // algorithm
            case TEST_FIND_IF:
            case TEST_FIND_IF_NOT:
            case TEST_ALL_OF:
            case TEST_ANY_OF:
            case TEST_NONE_OF:
            case TEST_COUNT_IF:
                break;
#endif
        }
        CHECK(a, b);
        uset_digi_free(&a);
    }
#ifdef CTL_USET_GROWTH_POWER2
    TEST_PASS("tests/func/test_unordered_set_power2");
#else
    TEST_PASS(__FILE__);
#endif
}
