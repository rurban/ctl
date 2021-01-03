#include "../test.h"
// FIXME
#include "strint.hh"

#define USE_INTERNAL_VERIFY
#define T strint
#include <ctl/unordered_map.h>

#include <string>
#include <unordered_map>
#include <algorithm>

#define CHECK(_x, _y) {                                      \
    assert(_x.size == _y.size());                            \
    std::unordered_map<std::string,int>::iterator _iter = _y.begin(); \
    foreach(umap_strint, &_x, _it) {                         \
        assert(_it.ref->value == _iter->second);             \
        _iter++;                                             \
    }                                                        \
    umap_strint_it _it = umap_strint_it_each(&_x);           \
    for(auto& _d : _y) {                                     \
        assert(_it.ref->value == _d.second);                 \
        _it.step(&_it);                                      \
    }                                                        \
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
    *a = umap_strint_init(5, strint_hash, strint_match);
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
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t loop = 0; loop < loops; loop++)
    {
        umap_strint a;
        std::unordered_map<std::string,int> b;
        setup_sets(&a, b);
        enum
        {
            TEST_INSERT,
            TEST_INSERT_OR_ASSIGN,
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
                auto p = STRINT{key,vb};
                umap_strint_insert_or_assign(&a, strint_init(str_init(key),vb));
                b.insert_or_assign(key, std::move(p));
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
                size_t load = umap_strint_load_factor(&a);
                std::unordered_map<std::string,int> bb = b;
                bb.reserve(size * 2 / load);
                umap_strint aa = umap_strint_copy(&a);
                umap_strint_reserve(&aa, size * 2 / load);
                CHECK(aa, bb);
                break;
            }
            case TEST_SWAP:
            {
                umap_strint aa = umap_strint_copy(&a);
                umap_strint aaa = umap_strint_init(aa.size, strint_hash, strint_match);
                std::unordered_map<std::string,int> bb = b;
                std::unordered_map<std::string,int> bbb;
                umap_strint_swap(&aaa, &aa);
                std::swap(bb, bbb);
                CHECK(aaa, bbb);
                umap_strint_free(&aaa);
                CHECK(a, b);
                break;
            }
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
            case TEST_COPY:
              { // C++20
                umap_strint aa = umap_strint_copy(&a);
                std::unordered_map<std::string,int> bb = b;
                CHECK(aa, bb);
                umap_strint_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL:
            {
                umap_strint aa = umap_strint_copy(&a);
                std::unordered_map<std::string,int> bb = b;
                assert(umap_strint_equal(&a, &aa, strint_match));
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
