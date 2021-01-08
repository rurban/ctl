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
        /*                                                             \
        assert(_x.bucket_count == _y.bucket_count());                  \
        for(size_t _i = 0; _i < _x.bucket_count; _i++)                 \
            assert(uset_digi_bucket_size(&_x, _i) == _y.bucket_size(_i));\
        */                                                              \
    }                                                                  \
}

#ifdef DEBUG
void print_uset(uset_digi* a)
{
    foreach(uset_digi, a, it)
        printf("%d\n", *it.ref->value);
    printf("--\n");
}
void print_unordered_set(std::unordered_set<DIGI,DIGI_hash> b)
{
    for(auto& x : b)
        printf("%d\n", *x.value);
    printf("--\n");
}
#else
#define print_uset(aa)
#define print_unordered_set(bb)
#endif

static void
setup_sets(uset_digi* a, std::unordered_set<DIGI,DIGI_hash>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
#ifdef DEBUG
    iters = 5; //TMP
#endif
    LOG ("\nSETUP_SETS %lu\n", iters);
    *a = uset_digi_init(digi_hash, digi_equal);
    // TODO a->equal = digi_equal
    for(size_t inserts = 0; inserts < iters; inserts++)
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
    uset_digi_free(&a);
}

int
main(void)
{
    INIT_SRAND;
    test_small_size();
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t loop = 0; loop < loops; loop++)
    {
        uset_digi a;
        std::unordered_set<DIGI,DIGI_hash> b;
        setup_sets(&a, b);
        enum
        {
            TEST_INSERT,
            //TEST_EMPLACE,
            //TEST_EXTRACT,
            //TEST_MERGE,
            //TEST_EQUAL_RANGE,
            //TEST_REMOVE_IF,
            TEST_ERASE_IF,
            TEST_CONTAINS,
            TEST_ERASE,
            TEST_CLEAR,
            TEST_SWAP,
            TEST_COUNT,
            TEST_FIND,
            TEST_COPY,
            TEST_EQUAL,
            TEST_REHASH,
            TEST_RESERVE,
            TEST_UNION,
#ifdef DEBUG
            TEST_SYMMETRIC_DIFFERENCE,
            TEST_INTERSECTION,
            TEST_DIFFERENCE,
#endif
            TEST_TOTAL,
        };
        int which = TEST_RAND(TEST_TOTAL);
        switch(which)
        {
            case TEST_INSERT:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                LOG ("\nTEST INSERT %d\n", vb);
                uset_digi_insert(&a, digi_init(vb));
                b.insert(DIGI{vb});
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_IF:
            {
                LOG ("\nTEST ERASE_IF %lu\n", a.size);
                size_t a_erases = uset_digi_erase_if(&a, digi_is_odd);
#ifdef __cpp_lib_erase_if
                size_t b_erases = b.erase_if(DIGI_is_odd); //C++20
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
                LOG ("\nTEST CONTAINS %lu\n", a.size);
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                bool a_has = uset_digi_contains(&a, digi_init(vb));
#ifdef __cpp_lib_erase_if
                bool a_has = b.contains(DIGI{vb}); //C++20
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
                LOG ("\nTEST ERASE %lu\n", erases);
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
                LOG ("\nTEST REHASH -> %lu\n", size);
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
                bb.reserve(size * 2 / load);
                LOG ("\nTEST RESERVE %lu, %f\n", size, load);
                uset_digi aa = uset_digi_copy(&a);
                uset_digi_reserve(&aa, size * 2 / load);
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
                LOG ("\nTEST SWAP\n");
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
                LOG ("\nTEST COUNT\n");
                int aa = uset_digi_count(&a, digi_init(key));
                int bb = b.count(DIGI{key});
                assert(aa == bb);
                CHECK(a, b);
                break;
            }
            case TEST_FIND:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                LOG ("\nTEST FIND %d\n", key);
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
                LOG ("\nTEST CLEAR\n");
                uset_digi_clear(&a);
                CHECK(a, b);
                break;
            }
#if 0
            case TEST_EMPLACE:
            case TEST_EXTRACT:
            case TEST_MERGE:
            case TEST_CONTAINS:
            case TEST_EQUAL_RANGE:
                break;
#endif
            case TEST_COPY:
              { // C++20
                LOG ("\nTEST COPY %lu\n", a.size);
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
                LOG ("\nTEST EQUAL %lu\n", aa.size);
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
                LOG ("\nTEST UNION %lu, %lu\n", a.size, aa.size);
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
#ifdef DEBUG
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                LOG ("\nTEST SYMMETRIC_DIFFERENCE %lu, %lu\n", a.size, aa.size);
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
                LOG ("\nTEST INTERSECTION %lu, %lu\n", a.size, aa.size);
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
                LOG ("\nTEST DIFFERENCE %lu, %lu\n", a.size, aa.size);
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
        }
        CHECK(a, b);
        uset_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
