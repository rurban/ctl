#include "../test.h"
#include "strint.hh"

#define USE_INTERNAL_VERIFY
#define T strint
#include <ctl/unordered_map.h>

#include <inttypes.h>
#include <string>
#include <unordered_map>
#include <algorithm>
#include <iterator>

#define CHECK(_x, _y) {                                                \
    assert(_x.size == _y.size());                                      \
    if(_x.size > 0)                                                    \
    {                                                                  \
        size_t a_found = 0;                                            \
        size_t b_found = 0;                                            \
        foreach(umap_strint, &_x, it)                                  \
        {                                                              \
            str *_key = &it.ref->key;                                  \
            auto found = _y.find(_key->value);                         \
            assert(found != _y.end());                                 \
            a_found++;                                                 \
        }                                                              \
        for(auto x : _y)                                               \
        {                                                              \
            const char *_key = x.first.c_str();                        \
            strint d = strint_init(str_init(_key), x.second);          \
            umap_strint_node* found = umap_strint_find(&_x, d);        \
            assert(found != NULL);                                     \
            strint_free(&d);                                           \
            b_found++;                                                 \
        }                                                              \
        assert(a_found == b_found);                                    \
        /*                                                             \
        assert(_x.bucket_count == _y.bucket_count());                  \
        for(size_t _i = 0; _i < _x.bucket_count; _i++)                 \
            assert(umap_strint_bucket_size(&_x, _i) == _y.bucket_size(_i));\
        */                                                              \
    }                                                                  \
}

static char *
new_rand_str() {
    char *c_char = (char *)calloc(36, 1);
    snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
    return c_char;
}

static void
setup_sets(umap_strint* a, std::unordered_map<std::string,int>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = umap_strint_init(strint_hash, strint_equal);
    for(size_t inserts = 0; inserts < iters; inserts++)
    {
        char *key = new_rand_str();
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        STRINT bb = STRINT{key,vb};
        umap_strint_insert(a, strint_init(str_init(key),vb));
        b.insert(bb);
    }
}

int
main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        umap_strint a;
        std::unordered_map<std::string,int> b;
        setup_sets(&a, b);
#define FOREACH_METH(TEST) \
        TEST(INSERT) \
        TEST(INSERT_OR_ASSIGN) \
        TEST(ERASE) \
        TEST(CLEAR) \
        TEST(COUNT) \
        TEST(FIND) \
        TEST(EQUAL) \
        TEST(REHASH) \
        TEST(RESERVE) \
        TEST(UNION) \
        TEST(INTERSECTION) \
        TEST(SYMMETRIC_DIFFERENCE) \
        TEST(DIFFERENCE)

#define FOREACH_DEBUG(TEST) \
        /* TEST(EMPLACE) */ \
        /* TEST(EXTRACT) */ \
        /* TEST(MERGE) */ \
        /* TEST(CONTAINS) */ \
        /* TEST(EQUAL_RANGE) */ \
        /* TEST(ERASE_IF) */ \
        TEST(SWAP) \
        TEST(COPY)

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
            case TEST_INSERT:
            {
                char *key = new_rand_str();
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                umap_strint_insert(&a, strint_init(str_init(key),vb));
                b.insert(STRINT{key,vb});
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_OR_ASSIGN:
            {
                char *key = new_rand_str();
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                umap_strint_insert_or_assign(&a, strint_init(str_init(key),vb));
                b.insert_or_assign(key, vb);
                CHECK(a, b);
                break;
            }
            case TEST_ERASE:
            {
                const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
                for(size_t i = 0; i < erases; i++)
                    if(a.size > 0)
                    {
                        char *key = new_rand_str();
                        const int value = TEST_RAND(TEST_MAX_SIZE);
                        strint kd = strint_init(str_init(key),value);
                        umap_strint_erase(&a, kd);
                        b.erase(key);
                        CHECK(a, b);
                        strint_free(&kd);
                    }
                CHECK(a, b);
                break;
            }
            case TEST_REHASH:
            {
                size_t size = umap_strint_size(&a);
                b.rehash(size * 2);
                umap_strint_rehash(&a, size * 2);
                CHECK(a, b);
                break;
            }
            case TEST_RESERVE:
            {
                size_t size = umap_strint_size(&a);
                float load = umap_strint_load_factor(&a);
                std::unordered_map<std::string,int> bb = b;
                const int32_t reserve = size * 2 / load;
                LOG ("load %f\n", load);
                if (reserve > 0) // avoid std::bad_alloc
                {
                    bb.reserve(reserve);
                    umap_strint aa = umap_strint_copy(&a);
                    umap_strint_reserve(&aa, reserve);
                    CHECK(aa, bb);
                    umap_strint_free(&aa);
                }
                break;
            }
#ifdef DEBUG
            case TEST_SWAP:
            {
                umap_strint aa = umap_strint_copy(&a);
                umap_strint aaa = umap_strint_init(strint_hash, strint_equal);
                umap_strint_reserve(&aaa, a.size);
                std::unordered_map<std::string,int> bb = b;
                std::unordered_map<std::string,int> bbb;
                umap_strint_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                umap_strint_free(&aaa);
                CHECK(a, b);
                break;
            }
            case TEST_COPY:
              { // C++20
                umap_strint aa = umap_strint_copy(&a);
                std::unordered_map<std::string,int> bb = b;
                CHECK(aa, bb);
                umap_strint_free(&aa);
                CHECK(a, b);
                break;
            }
#endif
            case TEST_COUNT:
            {
                char *key = new_rand_str();
                int value = TEST_RAND(TEST_MAX_SIZE);
                strint kd = strint_init(str_init(key), value);
                int aa = umap_strint_count(&a, kd);
                int bb = b.count(key);
                assert(aa == bb);
                CHECK(a, b);
                strint_free(&kd);
                break;
            }
            case TEST_FIND:
            {
                char *key = new_rand_str();
                const int value = TEST_RAND(TEST_MAX_SIZE);
                strint kd = strint_init(str_init(key), value);
                umap_strint_node* aa = umap_strint_find(&a, kd);
                auto bb = b.find(key);
                if(bb == b.end())
                    assert(umap_strint_end(&a) == aa);
                else
                    assert(bb->second == aa->value.value);
                CHECK(a, b);
                strint_free(&kd);
                break;
            }
            case TEST_CLEAR:
            {
                b.clear();
                umap_strint_clear(&a);
                CHECK(a, b);
                break;
            }
#if 0
            case TEST_CONTAINS: // C++20.
            {
                char *key = new_rand_str();
                const int value = TEST_RAND(TEST_MAX_SIZE);
                strint kd = strint_init(str_init(key), value);
                int aa = umap_strint_contains(&a, kd);
                int bb = b.contains(STRINT{key,value});
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
                size_t a_erases = umap_strint_erase_if(&a, strint_is_odd);
                size_t b_erases = b.erase_if(STRINT_is_odd);
                assert(a_erases == b_erases);
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL_RANGE:
                break;
#endif
            case TEST_EQUAL:
            {
                umap_strint aa = umap_strint_copy(&a);
                std::unordered_map<std::string,int> bb = b;
                assert(umap_strint_equal(&a, &aa));
                assert(b == bb);
                umap_strint_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_UNION:
            {
                umap_strint aa;
                std::unordered_map<std::string,int> bb;
                setup_sets(&aa, bb);
                umap_strint aaa = umap_strint_union(&a, &aa);
                std::unordered_map<std::string,int> bbb;
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                umap_strint_free(&aa);
                umap_strint_free(&aaa);
                break;
            }
            case TEST_INTERSECTION:
            {
                umap_strint aa;
                std::unordered_map<std::string,int> bb;
                setup_sets(&aa, bb);
                umap_strint aaa = umap_strint_intersection(&a, &aa);
                std::unordered_map<std::string,int> bbb;
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                umap_strint_free(&aa);
                umap_strint_free(&aaa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                umap_strint aa;
                std::unordered_map<std::string,int> bb;
                setup_sets(&aa, bb);
                umap_strint aaa = umap_strint_symmetric_difference(&a, &aa);
                std::unordered_map<std::string,int> bbb;
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                umap_strint_free(&aa);
                umap_strint_free(&aaa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                umap_strint aa;
                std::unordered_map<std::string,int> bb;
                setup_sets(&aa, bb);
                umap_strint aaa = umap_strint_difference(&a, &aa);
                std::unordered_map<std::string,int> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::inserter(bbb, bbb.begin()));
                CHECK(a, b);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                umap_strint_free(&aa);
                umap_strint_free(&aaa);
                break;
            }
        }
        CHECK(a, b);
        umap_strint_free(&a);
    }
    TEST_PASS(__FILE__);
}
