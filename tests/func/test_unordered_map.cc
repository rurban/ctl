#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "strint.hh"

#define USE_INTERNAL_VERIFY
#define T strint
#define INCLUDE_ALGORITHM
#include <ctl/unordered_map.h>

#include <algorithm>
#include <inttypes.h>
#include <iterator>
#include <string>
#include <unordered_map>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_FOUND)                                                                                                 \
    TEST(INSERT_OR_ASSIGN)                                                                                             \
    TEST(INSERT_OR_ASSIGN_FOUND)                                                                                       \
    TEST(ERASE)                                                                                                        \
    TEST(ERASE_IF)                                                                                                     \
    TEST(CLEAR)                                                                                                        \
    TEST(COUNT)                                                                                                        \
    TEST(CONTAINS)                                                                                                     \
    TEST(FIND)                                                                                                         \
    TEST(EQUAL)                                                                                                        \
    TEST(REHASH)                                                                                                       \
    TEST(RESERVE)                                                                                                      \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(DIFFERENCE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    /* TEST(EMPLACE) */                                                                                                \
    /* TEST(EXTRACT) */                                                                                                \
    /* TEST(MERGE) */                                                                                                  \
    /* TEST(EQUAL_RANGE) */                                                                                            \
    TEST(SWAP)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(COUNT_IF)                                                                                                     \
    TEST(EMPLACE)                                                                                                      \
    TEST(EMPLACE_FOUND)                                                                                                \
    TEST(EMPLACE_HINT)                                                                                                 \
    TEST(MERGE)                                                                                                        \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(GENERATE)                                                                                                     \
    TEST(TRANSFORM)

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
// clang-format on
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
#ifdef DEBUG
static const char *test_names[] = {FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            size_t a_found = 0;                                                                                        \
            size_t b_found = 0;                                                                                        \
            foreach (umap_strint, &_x, _it)                                                                            \
            {                                                                                                          \
                str *_key = &_it.ref->key;                                                                             \
                auto _found = _y.find(str_c_str(_key));                                                                \
                assert(_found != _y.end());                                                                            \
                a_found++;                                                                                             \
            }                                                                                                          \
            for (auto x : _y)                                                                                          \
            {                                                                                                          \
                const char *_key = x.first.c_str();                                                                    \
                strint d = strint_init(str_init(_key), x.second);                                                      \
                umap_strint_it _found = umap_strint_find(&_x, d);                                                      \
                assert(!umap_strint_it_done(&_found));                                                                 \
                strint_free(&d);                                                                                       \
                b_found++;                                                                                             \
            }                                                                                                          \
            assert(a_found == b_found);                                                                                \
            /*                                                                                                         \
            assert(_x.bucket_count == _y.bucket_count());                                                              \
            for(size_t _i = 0; _i < _x.bucket_count; _i++)                                                             \
                assert(umap_strint_bucket_size(&_x, _i) == _y.bucket_size(_i));                                        \
            */                                                                                                         \
        }                                                                                                              \
    }

#define CHECK_ITER(_it, b, _iter)

static char *new_rand_str()
{
    char *c_char = (char *)calloc(36, 1);
    snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
    return c_char;
}

static void setup_sets(umap_strint *a, std::unordered_map<std::string, int> &b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = umap_strint_init(strint_hash, strint_equal);
    for (size_t inserts = 0; inserts < iters; inserts++)
    {
        char *key = new_rand_str();
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        STRINT bb = STRINT{key, vb};
        umap_strint_insert_or_assign(a, strint_init(str_init(key), vb));
        b.insert(bb);
        free(key);
    }
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        umap_strint a;
        std::unordered_map<std::string, int> b;
        setup_sets(&a, b);
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
        case TEST_INSERT: {
            char *key = new_rand_str();
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            umap_strint_insert(&a, strint_init(str_init(key), vb));
            free(key);
            b.insert(STRINT{key, vb});
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_FOUND: {
            char *key = new_rand_str();
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            int found;
            umap_strint_it it = umap_strint_insert_found(&a, strint_init(str_init(key), vb), &found);
            free(key);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_map<std::string, int>::iterator, bool> pair;
            pair = b.insert(STRINT{key, vb});
            // STL returns true if not found, and freshly inserted
            assert((!found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            auto iter = b.insert(STRINT{key, vb});
            CHECK_ITER(it, b, iter);
#endif
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_OR_ASSIGN: {
            char *key = new_rand_str();
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            umap_strint_insert_or_assign(&a, strint_init(str_init(key), vb));
            free(key);
            b.insert_or_assign(key, vb);
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_OR_ASSIGN_FOUND: {
            char *key = new_rand_str();
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            int found;
            umap_strint_it it = umap_strint_insert_or_assign_found(&a, strint_init(str_init(key), vb), &found);
            free(key);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_map<std::string, int>::iterator, bool> pair;
            pair = b.insert_or_assign(key, vb);
            // STL returns true if not found, and freshly inserted
            assert((!found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            auto iter = b.insert_or_assign(key, vb);
            CHECK_ITER(it, b, iter);
#endif
            CHECK(a, b);
            break;
        }
        case TEST_ERASE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 0)
                {
                    char *key = new_rand_str();
                    const int value = TEST_RAND(TEST_MAX_SIZE);
                    strint kd = strint_init(str_init(key), value);
                    free(key);
                    umap_strint_erase(&a, kd);
                    b.erase(key);
                    CHECK(a, b);
                    strint_free(&kd);
                }
            CHECK(a, b);
            break;
        }
        case TEST_REHASH: {
            size_t size = umap_strint_size(&a);
            b.rehash(size * 2);
            umap_strint_rehash(&a, size * 2);
            CHECK(a, b);
            break;
        }
        case TEST_RESERVE: {
            size_t size = umap_strint_size(&a);
            float load = umap_strint_load_factor(&a);
            std::unordered_map<std::string, int> bb = b;
            const int32_t reserve = size * 2 / load;
            LOG("load %f\n", load);
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
        case TEST_SWAP: {
            umap_strint aa = umap_strint_copy(&a);
            umap_strint aaa = umap_strint_init(strint_hash, strint_equal);
            umap_strint_reserve(&aaa, a.size);
            std::unordered_map<std::string, int> bb = b;
            std::unordered_map<std::string, int> bbb;
            umap_strint_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            umap_strint_free(&aaa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY: { // C++20
            umap_strint aa = umap_strint_copy(&a);
            std::unordered_map<std::string, int> bb = b;
            CHECK(aa, bb);
            umap_strint_free(&aa);
            CHECK(a, b);
            break;
        }
#endif
        case TEST_COUNT: {
            char *key = new_rand_str();
            int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            free(key);
            int aa = umap_strint_count(&a, kd);
            int bb = b.count(key);
            assert(aa == bb);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_FIND: {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            free(key);
            umap_strint_it aa = umap_strint_find(&a, kd);
            auto bb = b.find(key);
            if (bb == b.end())
                assert(umap_strint_it_done(&aa));
            else
                assert(bb->second == aa.ref->value);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_CLEAR: {
            b.clear();
            umap_strint_clear(&a);
            CHECK(a, b);
            break;
        }
        case TEST_ERASE_IF: {
            size_t a_erases = umap_strint_erase_if(&a, strint_isupper);
#if __cpp_lib_erase_if >= 202002L
            // C++20
            size_t b_erases = std::erase_if(b, STRINT_isupper);
            assert(a_erases == b_erases);
            CHECK(a, b);
#endif
            break;
        }
        case TEST_EQUAL: {
            umap_strint aa = umap_strint_copy(&a);
            std::unordered_map<std::string, int> bb = b;
            assert(umap_strint_equal(&a, &aa));
            assert(b == bb);
            umap_strint_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_UNION: {
            umap_strint aa;
            std::unordered_map<std::string, int> bb;
            setup_sets(&aa, bb);
            umap_strint aaa = umap_strint_union(&a, &aa);
            std::unordered_map<std::string, int> bbb;
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            umap_strint_free(&aa);
            umap_strint_free(&aaa);
            break;
        }
        case TEST_INTERSECTION: {
            umap_strint aa;
            std::unordered_map<std::string, int> bb;
            setup_sets(&aa, bb);
            umap_strint aaa = umap_strint_intersection(&a, &aa);
            std::unordered_map<std::string, int> bbb;
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            umap_strint_free(&aa);
            umap_strint_free(&aaa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            umap_strint aa;
            std::unordered_map<std::string, int> bb;
            setup_sets(&aa, bb);
            umap_strint aaa = umap_strint_symmetric_difference(&a, &aa);
            std::unordered_map<std::string, int> bbb;
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            umap_strint_free(&aa);
            umap_strint_free(&aaa);
            break;
        }
        case TEST_DIFFERENCE: {
            umap_strint aa;
            std::unordered_map<std::string, int> bb;
            setup_sets(&aa, bb);
            umap_strint aaa = umap_strint_difference(&a, &aa);
            std::unordered_map<std::string, int> bbb;
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            umap_strint_free(&aa);
            umap_strint_free(&aaa);
            break;
        }
        case TEST_CONTAINS: // C++20.
        {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            free(key);
            int aa = umap_strint_contains(&a, kd);
#if __cpp_lib_erase_if >= 202002L
            int bb = b.contains(key);
#else
            int bb = b.count(key) == 1 ? 1 : 0;
#endif
            assert(aa == bb);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
#ifdef DEBUG
        // case TEST_EMPLACE:
        // case TEST_EXTRACT:
        // case TEST_MERGE:
        // case TEST_EQUAL_RANGE:
        // case TEST_FIND_IF:
        // case TEST_FIND_IF_NOT:
        // case TEST_ALL_OF:
        // case TEST_ANY_OF:
        // case TEST_NONE_OF:
        // case TEST_COUNT_IF:
        // case TEST_EMPLACE:
        // case TEST_EMPLACE_FOUND:
        // case TEST_EMPLACE_HINT:
        // case TEST_MERGE:
        // case TEST_REMOVE_IF:
        // case TEST_GENERATE:
        // case TEST_TRANSFORM:
#endif
        default:
#ifdef DEBUG
            printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
        CHECK(a, b);
        umap_strint_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
