#include "../test.h"
#include "digi.hh"

static inline size_t
digi_hash(digi* a)
{
  return (size_t)(*a->value % 0xffffffff);
}

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/unordered_set.h>

#include <unordered_set>
#include <algorithm>

#define CHECK(_x, _y) {                           \
    assert(_x.size == _y.size());                 \
    std::unordered_set<DIGI>::iterator _iter = _y.begin(); \
    foreach(uset_digi, &_x, _it) {                 \
        assert(*_it.ref->value == *_iter->value); \
        _iter++;                                  \
    }                                             \
    uset_digi_it _it = uset_digi_it_each(&_x);    \
    for(auto& _d : _y) {                          \
        assert(*_it.ref->value == *_d.value);     \
        _it.step(&_it);                           \
    }                                             \
}

static void
setup_sets(uset_digi* a, std::unordered_set<DIGI,DIGI_hash>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = uset_digi_init(5, digi_hash, digi_match);
    for(size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        uset_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
}

int
main(void)
{
    INIT_SRAND;
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
            //TEST_CONTAINS,
            //TEST_ERASE_IF,
            //TEST_EQUAL_RANGE,
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
            TEST_INTERSECTION,
            TEST_SYMMETRIC_DIFFERENCE,
            TEST_DIFFERENCE,
            TEST_TOTAL,
        };
        int which = TEST_RAND(TEST_TOTAL);
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
                b.rehash(size * 2);
                uset_digi_rehash(&a, size * 2);
                CHECK(a, b);
                break;
            }
            case TEST_RESERVE:
            {
                size_t size = uset_digi_size(&a);
                size_t load = uset_digi_load_factor(&a);
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                bb.reserve(size * 2 / load);
#if 0
                uset_digi aa = uset_digi_copy(&a);
                uset_digi_reserve(&aa, size * 2 / load);
                CHECK(aa, bb);
#endif
                break;
            }
            case TEST_SWAP:
            {
                uset_digi aa = uset_digi_copy(&a);
                uset_digi aaa = uset_digi_init(1, digi_hash, digi_match);
                std::unordered_set<DIGI,DIGI_hash> bb = b;
                std::unordered_set<DIGI,DIGI_hash> bbb;
                uset_digi_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                uset_digi_free(&aaa);
                CHECK(a, b);
                break;
            }
            case TEST_COUNT:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                digi kd = digi_init(key);
                int aa = uset_digi_count(&a, kd);
                int bb = b.count(DIGI{key});
                assert(aa == bb);
                CHECK(a, b);
                digi_free(&kd);
                break;
            }
            case TEST_FIND:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                digi kd = digi_init(key);
                uset_digi_node* aa = uset_digi_find(&a, kd);
                auto bb = b.find(DIGI{key});
                if(bb == b.end())
                    assert(uset_digi_end(&a) == aa);
                else
                    assert(*bb->value == *aa->value.value);
                CHECK(a, b);
                digi_free(&kd);
                break;
            }
            case TEST_CLEAR:
            {
                b.clear();
                uset_digi_clear(&a);
                CHECK(a, b);
                break;
            }
#if 0
            case TEST_CONTAINS: // C++20.
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = uset_digi_contains(&a, key);
                int bb = b.contains(key);
                assert(aa == bb);
                CHECK(a, b);
                break;
            }
            case TEST_EMPLACE:
            case TEST_EXTRACT:
            case TEST_MERGE:
            case TEST_CONTAINS:
            case TEST_ERASE_IF:
            {
                size_t a_erases = uset_digi_erase_if(&a, digi_is_odd);
                size_t b_erases = b.erase_if(DIGI_is_odd);
                assert(a_erases == b_erases);
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL_RANGE:
                break;
#endif
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
                assert(uset_digi_equal(&a, &aa, digi_match));
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
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
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
            case TEST_DIFFERENCE:
            {
                uset_digi aa;
                std::unordered_set<DIGI,DIGI_hash> bb;
                setup_sets(&aa, bb);
                uset_digi aaa = uset_digi_difference(&a, &aa);
                std::unordered_set<DIGI,DIGI_hash> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                uset_digi_free(&aa);
                uset_digi_free(&aaa);
                break;
            }
        }
        CHECK(a, b);
        uset_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
