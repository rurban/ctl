#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "charpint.hh"

#define USE_INTERNAL_VERIFY
typedef char* charp;
#undef PODK
#define TK charp
#define POD
#define T int
//#define INCLUDE_ALGORITHM
#include <ctl/swisstable.h>

#include <inttypes.h>
#include <algorithm>
#include <iterator>
#include <unordered_set>
#include <unordered_map>

#define FOREACH_METH(TEST)                                                      \
    TEST(SELF)                                                                  \
    TEST(INSERT)                                                                \
    TEST(INSERT_FOUND)                                                          \
    TEST(CONTAINS)                                                              \
    TEST(CLEAR)                                                                 \
    TEST(SWAP)                                                                  \
    TEST(COUNT)                                                                 \
    TEST(FIND)                                                                  \
    TEST(COPY)                                                                  \
    TEST(EQUAL)                                                                 \
    TEST(REHASH)                                                                \
    TEST(RESERVE)                                                               \
    TEST(FIND_IF)                                                               \
    TEST(FIND_IF_NOT)

#define FOREACH_DEBUG(TEST)                                                     \
    TEST(ERASE)                                                                 \
    TEST(ERASE_IF)                                                              \
    TEST(ALL_OF)                                                                \
    TEST(ANY_OF)                                                                \
    TEST(NONE_OF)                                                               \
    TEST(COUNT_IF)                                                              \
    TEST(UNION) /* 20 */                                                        \
    TEST(INTERSECTION)                                                          \
    TEST(DIFFERENCE)                                                            \
    TEST(SYMMETRIC_DIFFERENCE)                                                  \
    TEST(GENERATE)                                                              \
    TEST(GENERATE_N)                                                            \
    TEST(TRANSFORM)                                                             \
    TEST(COPY_IF)                                                               \
    TEST(EMPLACE)                                                               \
    TEST(EMPLACE_FOUND)                                                         \
    TEST(EMPLACE_HINT) /* 30 */                                                 \
    TEST(MERGE)                                                                 \
    TEST(MERGE_RANGE)                                                           \
    TEST(EXTRACT) /* 33 */                                                      \
    TEST(INSERT_GENERIC)                                                        \
    TEST(REMOVE_IF)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

// clang-format off
enum {
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
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""};
#endif

#define CHECK(_x, _y)                                                           \
    {                                                                           \
        assert(_x.size == _y.size());                                           \
        if (_x.size > 0)                                                        \
        {                                                                       \
            size_t a_found = 0;                                                 \
            size_t b_found = 0;                                                 \
            foreach (hmap_charp, &_x, _it)                                      \
            {                                                                   \
                str *_key = &_it.ref->key;                                      \
                auto _found = _y.find(str_c_str(_key));                         \
                assert(_found != _y.end());                                     \
                a_found++;                                                      \
            }                                                                   \
            for (auto x : _y)                                                   \
            {                                                                   \
                const char *_key = x.first.c_str();                             \
                hmap_charp_it _found = hmap_charp_find(&_x, key);               \
                assert(!hmap_charp_it_done(&_found));                           \
                strint_free(&d);                                                \
                b_found++;                                                      \
            }                                                                   \
            assert(a_found == b_found);                                         \
        }                                                                       \
    }

#define CHECK_ITER(_it, b, _iter)                                               \
    if (!hmap_charp_it_done(&_it))                                              \
    {                                                                           \
        assert(_iter != b.end());                                               \
        assert(*_it.ref->value == *(*_iter).value);                             \
    }                                                                           \
    else                                                                        \
        assert(_iter == b.end())

#ifdef DEBUG
void print_hmap(hmap_charp *a)
{
    int i = 0;
    foreach (hmap_charp, a, it)
        printf("%d: %d [%ld]\n", i++, *it.ref->value, it.buckets - a->buckets);
    printf("--\n");
}
void print_unordered_map(std::unordered_map<char*, int> &b)
{
    int i = 0;
    for (auto &x : b)
        printf("%d: %d\n", i++, *x.value);
    printf("--\n");
}
#else
#define print_hmap(aa)
#define print_unordered_map(bb)
#endif

#ifdef DEBUG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 15
#define TEST_MAX_VALUE TEST_MAX_SIZE
#else
#define TEST_MAX_VALUE INT_MAX
#endif

static char *new_rand_str()
{
    char *c_char = (char *)calloc(36, 1);
    snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
    return c_char;
}

static void setup_hmaps(hmap_charp *a, std::unordered_map<char*,int> &b)
{
    size_t size = TEST_RAND(TEST_MAX_SIZE);
    LOG("\nsetup_hmap %lu\n", size);
    *a = hmap_charp_init(charp_hash, charp_equal);
    hmap_charp_rehash(a, size);
    for (size_t inserts = 0; inserts < size; inserts++)
    {
        char *key = new_rand_str();
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        hmap_charp_insert(a, key, vb);
        b.insert(CHARPINT{key, vb});
        free (key);
    }
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    //test_small_size();
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        hmap_charp a, aa, aaa;
        std::unordered_map<char*, int> b, bb, bbb;
        hmap_charp_it first, found, it;
        std::unordered_map<char*, int>::iterator iter;
        size_t num_a, num_b;
        bool is_a, is_b;
        char *key = new_rand_str();
        int value = TEST_RAND(TEST_MAX_VALUE);
        setup_hmaps(&a, b);
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        } else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        LOG("TEST=%d %s (%zu, %zu)\n", which, test_names[which], a.size, a.bucket_max);
        RECORD_WHICH;
        switch (which)
        {
        case TEST_SELF: {
            aa = hmap_charp_copy(&a);
            LOG("before\n");
            print_hmap(&a);
            foreach(hmap_charp, &aa, it1)
            {
                // LOG("find %d [%zu]\n", *ref->value, it.bucket_index);
                size_t index = it1.ref - aa.values;
                hmap_charp_node *node = &aa.groups[index];
                found = hmap_charp_find(&a, node->key[index]);
                assert(!hmap_charp_it_done(&found));
            }
            LOG("all found\n");
#if 0
            foreach(hmap_charp, &a, it2)
            {
                size_t index = it2.ref - a.values;
                hmap_charp_node *node = &aa.groups[index];
                hmap_charp_erase(&aa, node);
            }
            LOG("all erased\n");
            assert(hmap_charp_empty(&aa));
#endif
            print_hmap(&a);
            hmap_charp_free(&aa);
            break;
        }
        case TEST_INSERT: {
            hmap_charp_insert(&a, key, value);
            b.insert(CHARPINT{key, value});
            break;
        }
#if 0
        case TEST_INSERT_FOUND: {
            first = hmap_charp_begin(&a);
            //const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            int a_found;
            it = hmap_charp_insert_found(&a, key, value, &a_found);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_map<char*, int>::iterator, bool> pair;
            pair = b.insert(CHARPINT{key, value});
            // STL returns true if not found, and freshly inserted
            assert((!a_found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            auto iter = b.insert(CHARPINT{key, vb});
            CHECK_ITER(it, b, iter);
#endif
            break;
        }
#if 0
        case TEST_ERASE_IF: {
            num_a = hmap_charp_erase_if(&a, strint_is_odd);
#if __cpp_lib_erase_if >= 202002L
            num_b = std::erase_if(b, CHARPINTc_is_odd); // C++20
#else
            num_b = 0;
            {
                iter = b.begin();
                auto end = b.end();
                while (iter != end)
                {
                    if ((int)*iter->value % 2)
                    {
                        iter = b.erase(iter);
                        num_b += 1;
                    }
                    else
                        iter++;
                }
            }
#endif
            assert(num_a == num_b);
            break;
        }
#endif
        case TEST_CONTAINS: {
            is_a = hmap_charp_contains(&a, strint_init(value));
#if __cpp_lib_erase_if >= 202002L
            is_b = b.contains(CHARPINT{key, value}); // C++20
#else
            is_b = b.count(CHARPINT{key, value}) == 1;
#endif
            assert(is_a == is_b);
            break;
        }
#if 0
        case TEST_ERASE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 0)
                {
                    const int key = TEST_RAND(TEST_MAX_SIZE);
                    strint kd = strint_init(key);
                    hmap_charp_erase(&a, kd);
                    b.erase(CHARPINT{key});
                    strint_free(&kd);
                }
            break;
        }
#endif
        case TEST_REHASH: {
            size_t size = hmap_charp_size(&a);
            LOG("size %lu -> %lu, cap: %lu\n", size, size * 2, a.bucket_max + 1);
            print_hmap(&a);
            print_unordered_map(b);
            b.rehash(size * 2);
            LOG("STL size: %lu, cap: %lu\n", b.size(), b.bucket_count());
            hmap_charp_rehash(&a, size * 2);
            print_hmap(&a);
            break;
        }
        case TEST_RESERVE: {
            size_t size = hmap_charp_size(&a);
            float load = hmap_charp_load_factor(&a);
            bb = b;
            const int32_t reserve = size * 2 / load;
            LOG("load %f\n", load);
            if (reserve > 0) // avoid std::bad_alloc
            {
                bb.reserve(reserve);
                LOG("STL reserve by %" PRId32 " %zu\n", reserve, bb.bucket_count());
                LOG("before\n");
                print_hmap(&a);
                aa = hmap_charp_copy(&a);
                LOG("copy\n");
                print_hmap(&aa);
                hmap_charp_reserve(&aa, reserve);
                LOG("CTL reserve by %" PRId32 " %zu\n", reserve, aa.bucket_max + 1);
                print_hmap(&aa);
                CHECK(aa, bb);
                hmap_charp_free(&aa);
            }
            break;
        }
        case TEST_SWAP: {
            aa = hmap_charp_copy(&a);
            aaa = hmap_charp_init(NULL, NULL);
            bb = b;
            hmap_charp_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            hmap_charp_free(&aa);
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_COUNT: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            num_a = hmap_charp_count(&a, strint_init(key));
            num_b = b.count(CHARPINT{key});
            assert(num_a == num_b);
            break;
        }
        case TEST_FIND: {
            first = hmap_charp_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            strint key = strint_init(vb);
            // find is special, it doesnt free the key
            it = hmap_charp_find(&a, key);
            iter= b.find(CHARPINT{vb});
            if (iter == b.end())
                assert(hmap_charp_it_done(&it));
            else
                assert(*iter->value == *it.ref->value);
            strint_free(&key);
            break;
        }
        case TEST_CLEAR: {
            b.clear();
            hmap_charp_clear(&a);
            break;
        }
        case TEST_COPY: { // C++20
            aa = hmap_charp_copy(&a);
            bb = b;
            CHECK(aa, bb);
            hmap_charp_free(&aa);
            break;
        }
        case TEST_EQUAL: {
            aa = hmap_charp_copy(&a);
            bb = b;
            print_hmap(&aa);
            print_unordered_map(bb);
            assert(hmap_charp_equal(&a, &aa));
            assert(b == bb);
            hmap_charp_free(&aa);
            break;
        }
#ifdef DEBUG
        case TEST_INSERT_GENERIC: {
            setup_hmaps(&aa, bb);
            first = hmap_charp_begin(&a);
            //hmap_charp_insert_generic(&a, &first);
            b.insert(bb.begin(), bb.end());
            print_hmap(&a);
            print_unordered_map(b);
            CHECK(a, b);
            hmap_charp_free(&aa);
            break;
        }
#endif
        case TEST_UNION: {
            setup_hmaps(&aa, bb);
            aaa = hmap_charp_union(&a, &aa);
#if 0 // If the STL would be actually usable
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::inserter(bbb, std::next(bbb.begin())));
#else
            std::copy(b.begin(), b.end(), std::inserter(bbb, bbb.end()));
            for (const auto &elem : bb)
            {
                bbb.insert(elem);
            }
#endif
            print_hmap(&aa);
            print_unordered_map(bb);
            CHECK(aa, bb);
            print_hmap(&aaa);
            print_unordered_map(bbb);
            CHECK(aaa, bbb);
            hmap_charp_free(&aa);
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_INTERSECTION: {
            setup_hmaps(&aa, bb);
            aaa = hmap_charp_intersection(&a, &aa);
#if 0 // If the STL would be actually usable
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, std::next(bbb.begin())));
#else
            for (const auto &elem : b)
            {
                if (bb.find(CHARPINT(*elem.value)) != bb.end())
                    bbb.insert(elem);
            }
#endif
            CHECK(aa, bb);
            hmap_charp_free(&aa);
            CHECK(aaa, bbb);
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_DIFFERENCE: {
            setup_hmaps(&aa, bb);
            LOG("uset a\n");
            print_hmap(&a);
            aaa = hmap_charp_difference(&a, &aa);
#if 0
            // Note: the STL cannot do this simple task, because it requires
            // both sets to be ordered.
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                std::inserter(bbb, std::next(bbb.begin())));
#else
            std::copy(b.begin(), b.end(), std::inserter(bbb, bbb.end()));
            for (const auto &elem : bb)
            {
                bbb.erase(elem);
            }
#endif
            LOG("uset b\n");
            print_hmap(&aa);
            print_unordered_map(bb);
            CHECK(aa, bb);
            hmap_charp_free(&aa);
            LOG("uset difference (a-b)\n");
            print_hmap(&aaa);
            print_unordered_map(bbb);
            CHECK(aaa, bbb);
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            setup_hmaps(&aa, bb);
            aaa = hmap_charp_symmetric_difference(&a, &aa);
            print_hmap(&aaa);
#if 0 // If the STL would be actually usable
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                          std::inserter(bbb, std::next(bbb.begin())));
#else
            // union: b + bb
            std::copy(b.begin(), b.end(), std::inserter(bbb, bbb.end()));
            for (const auto &elem : bb)
            {
                bbb.insert(elem);
            }
            print_unordered_map(bbb);
            // intersection: b - bb
            for (const auto &elem : b)
            {
                if (bb.find(CHARPINT(*elem.value)) != bb.end())
                    bbb.erase(elem);
            }
            print_unordered_map(bbb);
#endif
            CHECK(aa, bb);
            hmap_charp_free(&aa);
            CHECK(aaa, bbb); // fails
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_EMPLACE: // 24
        {
            first = hmap_charp_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            strint key = strint_init(vb);
            hmap_charp_emplace(&a, &key);
            b.emplace(CHARPINT{vb});
            break;
        }
        case TEST_EMPLACE_FOUND: {
            first = hmap_charp_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            strint key = strint_init(vb);
            int a_found;
            it = hmap_charp_emplace_found(&a, &key, &a_found);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_map<char*, int>::iterator, bool> pair;
            pair = b.emplace(CHARPINT{vb});
            // STL returns true if not found, and freshly inserted
            assert((!a_found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            iter = b.insert(CHARPINT{vb});
            CHECK_ITER(it, b, iter);
#endif
            break;
        }
        case TEST_EMPLACE_HINT: {
            // makes not much sense for uset, only set
            first = hmap_charp_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            strint key = strint_init(vb);
            found = hmap_charp_find(&a, key);
            it = hmap_charp_emplace_hint(&found, &key);
#if __cplusplus >= 201103L
            // C++11
            auto hint = b.find(CHARPINT{vb});
            iter = b.emplace_hint(hint, CHARPINT{vb});
            CHECK_ITER(it, b, iter);
#else
            iter = b.insert(CHARPINT{vb});
            CHECK_ITER(it, b, iter.first);
#endif
            break;
        }
        // algorithm
        case TEST_FIND_IF: {
            it = hmap_charp_find_if(&a, strint_is_odd);
            iter = std::find_if(b.begin(), b.end(), CHARPINTc_is_odd);
            if (iter == b.end())
                assert(!it.node);
            else
                assert(*iter->value % 2);
            break;
        }
        case TEST_FIND_IF_NOT: {
            it = hmap_charp_find_if_not(&a, strint_is_odd);
            iter = std::find_if_not(b.begin(), b.end(), CHARPINTc_is_odd);
            if (iter == b.end())
                assert(!it.node);
            else
                assert(!(*iter->value % 2));
            break;
        }
        case TEST_ALL_OF: {
            is_a = hmap_charp_all_of(&a, strint_is_odd);
            is_b = std::all_of(b.begin(), b.end(), CHARPINTc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF: {
            is_a = hmap_charp_any_of(&a, strint_is_odd);
            is_b = std::any_of(b.begin(), b.end(), CHARPINTc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF: {
            is_a = hmap_charp_none_of(&a, strint_is_odd);
            is_b = std::none_of(b.begin(), b.end(), CHARPINTc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_COUNT_IF: {
            num_a = hmap_charp_count_if(&a, strint_is_odd);
            num_b = std::count_if(b.begin(), b.end(), CHARPINTc_is_odd);
            assert(num_a == num_b);
            break;
        }
        /* Need some C++ help here.
           I don't think std::generate can be made usable for set, we dont care
           for the insert hint, and we have no operator!= for the STL inserter.
           However our CTL generate for set works fine, just a bit expensive. */
        case TEST_GENERATE: {
            print_hmap(&a);
            strint_generate_reset();
            hmap_charp_generate(&a, strint_generate);
            LOG("=>\n");
            print_hmap(&a);
            strint_generate_reset();
            // std::generate(b.begin(), b.end(), CHARPINTc_generate);
            // FIXME: need operator!= for insert_operator<set<CHARPINT>>
            // std::generate(std::inserter(b, b.begin()), std::inserter(bb, bb.begin()),
            //              CHARPINT_generate);
            // LOG("b\n");
            // print_unordered_map(b);
            size_t n = b.size();
            b.clear();
            for (size_t i = 0; i < n; i++)
                b.insert(CHARPINT_generate());
            LOG("=>\n");
            print_unordered_map(b);
            CHECK(a, b);
            break;
        }
        case TEST_GENERATE_N: {
            print_hmap(&a);
            print_unordered_map(b);
            size_t count = TEST_RAND(20);
            LOG("=> %zu\n", count);
            strint_generate_reset();
            hmap_charp_generate_n(&a, count, strint_generate);
            print_hmap(&a);
            strint_generate_reset();
            // This is a joke
            // std::generate_n(std::inserter(b, b.begin()), count, CHARPINT_generate);
            b.clear();
            for (size_t i = 0; i < count; i++)
                b.insert(CHARPINT_generate());
            print_unordered_map(b);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: {
            print_hmap(&a);
            aa = hmap_charp_transform(&a, strint_untrans);
            std::transform(b.begin(), b.end(), std::inserter(bb, bb.end()), CHARPINT_untrans);
            print_hmap(&aa);
            print_unordered_map(bb);
            CHECK(aa, bb);
            CHECK(a, b);
            hmap_charp_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            print_hmap(&a);
            aa = hmap_charp_copy_if(&a, strint_is_odd);
#if __cplusplus >= 201103L
            std::copy_if(b.begin(), b.end(), std::inserter(bb, bb.begin()), CHARPINTc_is_odd);
#else
            for (auto &d : b)
                if (CHARPINT_is_odd(d))
                    bb.insert(d);
#endif
            CHECK(aa, bb);
            hmap_charp_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_MERGE: {
            aa = hmap_charp_init_from(&a);
            setup_hmaps(&aa, bb);
            print_hmap(&a);
            print_hmap(&aa);
            aaa = hmap_charp_merge(&a, &aa);
#if __cpp_lib_node_extract >= 201606L
            b.merge(bb); // C++17
            print_hmap(&aaa);
            print_unordered_map(b);
            CHECK(aaa, b);
            b.clear();
            hmap_charp_clear(&a);
#else
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            hmap_charp_free(&aa);
            hmap_charp_free(&aaa);
            break;
        }
        case TEST_MERGE_RANGE: {
            hmap_charp_it range_a1, range_a2;
            //std::unordered_map<CHARPINT>::iterator first_b1, last_b1, first_b2, last_b2;
            //get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = hmap_charp_init_from(&a);
            setup_hmaps(&aa, bb);
            range_a1 = hmap_charp_begin(&a);
            range_a2 = hmap_charp_begin(&aa);
            //get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            aaa = hmap_charp_merge_range(&range_a1, &range_a2);
#if !defined(_MSC_VER)
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            hmap_charp_free(&aa);
            hmap_charp_free(&aaa);
            break;
        }

#if 0
        case TEST_EXTRACT:
        case TEST_REMOVE_IF:
        case TEST_EQUAL_RANGE:
            printf("nyi\n");
            break;
#endif
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
        free (key);
        hmap_charp_free(&a);
    }

    FINISH_TEST(__FILE__);
}

#endif // C++11
