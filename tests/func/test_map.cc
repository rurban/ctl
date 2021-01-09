#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "strint.hh"

#define USE_INTERNAL_VERIFY
#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#define T charp
#include <ctl/map.h>

#include <algorithm>
#include <iterator>
#include <map>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_OR_ASSIGN)                                                                                             \
    TEST(ERASE)                                                                                                        \
    TEST(CLEAR)                                                                                                        \
    TEST(SWAP)                                                                                                         \
    TEST(COUNT)                                                                                                        \
    TEST(FIND_NODE)                                                                                                    \
    TEST(FIND)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(EQUAL)                                                                                                        \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(DIFFERENCE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    /* TEST(EMPLACE) */                                                                                                \
    /* TEST(EXTRACT) */                                                                                                \
    /* TEST(MERGE) */                                                                                                  \
    TEST(CONTAINS)                                                                                                     \
    TEST(ERASE_IF)                                                                                                     \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(COUNT_RANGE)

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
CLANG_DIAG_IGNORE(-Wunneeded-internal-declaration)
// only needed for the size
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
CLANG_DIAG_RESTORE
#ifdef DEBUG
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""};
#endif
// clang-format on

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        std::map<std::string, int>::iterator _iter = _y.begin();                                                       \
        foreach (map_strint, &_x, _it)                                                                                 \
        {                                                                                                              \
            assert(_it.ref->value == _iter->second);                                                                   \
            _iter++;                                                                                                   \
        }                                                                                                              \
        map_strint_it _it = map_strint_begin(&_x);                                                                     \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(_it.ref->value == _d.second);                                                                       \
            map_strint_it_next(&_it);                                                                                  \
        }                                                                                                              \
    }

static char *new_rand_str()
{
    char *c_char = (char *)calloc(36, 1);
    snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
    return c_char;
}

static void setup_sets(map_strint *a, std::map<std::string, int> &b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = map_strint_init(strint_compare);
    a->equal = strint_equal;
    for (size_t inserts = 0; inserts < iters; inserts++)
    {
        char *key = new_rand_str();
        const int vb = TEST_RAND(TEST_MAX_SIZE);
        map_strint_insert(a, strint_init(str_init(key), vb));
        b.insert(STRINT{key, vb}); // or std::pair<std::string,int>(key,vb));
    }
}

int main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        map_strint a;
        std::map<std::string, int> b;
        setup_sets(&a, b);
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
        case TEST_INSERT: {
            char *key = new_rand_str();
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            map_charp_insert(&a, strint_init(str_init(key), vb));
            b.insert(STRINT{key, vb});
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_OR_ASSIGN: {
            char *key = new_rand_str();
            int vb = TEST_RAND(TEST_MAX_SIZE);
            map_charp_insert_or_assign(&a, strint_init(str_init(key), vb));
            b.insert_or_assign(key, vb);
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
                    map_charp_erase(&a, kd);
                    b.erase(key);
                    CHECK(a, b);
                    strint_free(&kd);
                }
            CHECK(a, b);
            break;
        }
        case TEST_SWAP: {
            map_charp aa = map_charp_copy(&a);
            map_charp aaa = map_charp_init(strint_compare);
            std::map<std::string, int> bb = b;
            std::map<std::string, int> bbb;
            map_charp_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            map_charp_free(&aaa);
            CHECK(a, b);
            break;
        }
        case TEST_COUNT: {
            char *key = new_rand_str();
            int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            int aa = map_charp_count(&a, kd);
            int bb = b.count(key);
            assert(aa == bb);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_FIND_NODE: {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            map_strint_node *aa = map_strint_find_node(&a, kd);
            auto bb = b.find(key);
            if (bb == b.end())
            {
                char *key = new_rand_str();
                const int value = TEST_RAND(TEST_MAX_SIZE);
                strint kd = strint_init(str_init(key), value);
                map_strint_erase(&a, kd);
                b.erase(key);
                CHECK(a, b);
                strint_free(&kd);
            }
            CHECK(a, b);
            break;
        }
        case TEST_SWAP: {
            map_strint aa = map_strint_copy(&a);
            map_strint aaa = map_strint_init(strint_compare);
            std::map<std::string, int> bb = b;
            std::map<std::string, int> bbb;
            map_strint_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            map_strint_free(&aaa);
            CHECK(a, b);
            break;
        }
        case TEST_COUNT: {
            char *key = new_rand_str();
            int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            int aa = map_strint_count(&a, kd);
            int bb = b.count(key);
            assert(aa == bb);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_FIND_NODE: {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            map_strint_node *aa = map_strint_find_node(&a, kd);
            auto bb = b.find(key);
            if (bb == b.end())
            {
                b.clear();
                map_charp_clear(&a);
                CHECK(a, b);
                break;
            }
            else
                assert(bb->second == aa->value.value);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_FIND: {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            map_strint_it it = map_strint_find(&a, kd);
            auto bb = b.find(key);
            if (bb == b.end())
                assert(map_strint_it_done(&it));
            else
                assert(bb->second == it.ref->value);
            CHECK(a, b);
            strint_free(&kd);
            break;
        }
        case TEST_CLEAR: {
            b.clear();
            map_strint_clear(&a);
            CHECK(a, b);
            break;
        }
#ifdef DEBUG
        case TEST_CONTAINS: // C++20
        {
            char *key = new_rand_str();
            const int value = TEST_RAND(TEST_MAX_SIZE);
            strint kd = strint_init(str_init(key), value);
            int aa = map_strint_contains(&a, kd);
#if __cpp_lib_erase_if >= 202002L
            int bb = b.contains(key);
#else
                int bb = b.count(key
        }) == 1;
#endif
            assert(aa == bb);
            CHECK(a, b);
            break;
        }
        case TEST_ERASE_IF: {
#if __cpp_lib_erase_if >= 202002L
            size_t a_erases = map_strint_erase_if(&a, strint_isupper);
            size_t b_erases = std::erase_if(b, STRINT_isupper);
            assert(a_erases == b_erases);
            CHECK(a, b);
#endif
            break;
        }
#endif
#if 0
            case TEST_EMPLACE:
            case TEST_EXTRACT:
            case TEST_MERGE:
            case TEST_CONTAINS:
#endif
        case TEST_COPY: { // C++20
            map_charp aa = map_charp_copy(&a);
            std::map<std::string, int> bb = b;
            CHECK(aa, bb);
            map_charp_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_EQUAL: {
            map_charp aa = map_charp_copy(&a);
            std::map<std::string, int> bb = b;
            assert(map_charp_equal(&a, &aa));
            assert(b == bb);
            map_charp_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_UNION: {
            map_charp aa;
            std::map<std::string, int> bb;
            setup_sets(&aa, bb);
            map_charp aaa = map_charp_union(&a, &aa);
            std::map<std::string, int> bbb;
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            map_charp_free(&aa);
            map_charp_free(&aaa);
            break;
        }
        case TEST_INTERSECTION: {
            map_charp aa;
            std::map<std::string, int> bb;
            setup_sets(&aa, bb);
            map_charp aaa = map_charp_intersection(&a, &aa);
            std::map<std::string, int> bbb;
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            map_charp_free(&aa);
            map_charp_free(&aaa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            map_charp aa;
            std::map<std::string, int> bb;
            setup_sets(&aa, bb);
            map_charp aaa = map_charp_symmetric_difference(&a, &aa);
            std::map<std::string, int> bbb;
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            map_charp_free(&aa);
            map_charp_free(&aaa);
            break;
        }
        case TEST_DIFFERENCE: {
            map_charp aa;
            std::map<std::string, int> bb;
            setup_sets(&aa, bb);
            map_charp aaa = map_charp_difference(&a, &aa);
            std::map<std::string, int> bbb;
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(a, b);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            map_charp_free(&aa);
            map_charp_free(&aaa);
            break;
        }
        }
        CHECK(a, b);
        map_charp_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
