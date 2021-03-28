#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define USE_INTERNAL_VERIFY
#define INCLUDE_ALGORITHM
#include <ctl/unordered_set.h>

#include <algorithm>
#include <inttypes.h>
#include <iterator>
#include <unordered_set>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(SELF)                                                                                                         \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_FOUND)                                                                                                 \
    TEST(ERASE_IF)                                                                                                     \
    TEST(CONTAINS)                                                                                                     \
    TEST(ERASE)                                                                                                        \
    TEST(CLEAR)                                                                                                        \
    TEST(SWAP)                                                                                                         \
    TEST(COUNT)                                                                                                        \
    TEST(FIND)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(EQUAL)                                                                                                        \
    TEST(REHASH)                                                                                                       \
    TEST(RESERVE)                                                                                                      \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(COUNT_IF)                                                                                                     \
    TEST(UNION) /* 20 */                                                                                               \
    TEST(INTERSECTION)                                                                                                 \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_N)                                                                                                   \
    TEST(TRANSFORM)                                                                                                    \
    TEST(COPY_IF)                                                                                                      \
    TEST(EMPLACE)                                                                                                      \
    TEST(EMPLACE_FOUND)                                                                                                \
    TEST(EMPLACE_HINT) /* 30 */                                                                                        \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EXTRACT) /* 33 */                                                                                             \
    TEST(INSERT_GENERIC)                                                                                               \
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
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            size_t a_found = 0;                                                                                        \
            size_t b_found = 0;                                                                                        \
            foreach (uset_digi, &_x, _it)                                                                              \
            {                                                                                                          \
                auto _found = _y.find(DIGI(*_it.ref->value));                                                          \
                assert(_found != _y.end());                                                                            \
                a_found++;                                                                                             \
            }                                                                                                          \
            for (auto x : _y)                                                                                          \
            {                                                                                                          \
                digi d = digi_init(*x.value);                                                                          \
                assert(uset_digi_find_node(&_x, d));                                                                   \
                digi_free(&d);                                                                                         \
                b_found++;                                                                                             \
            }                                                                                                          \
            assert(a_found == b_found);                                                                                \
            /* only if we use the very same policies                                                                   \
            assert(_x.bucket_max + 1 == _y.bucket_count());                                                            \
            for(size_t _i = 0; _i <= _x.bucket_max; _i++)
            \
                assert(uset_digi_bucket_size(&_x, _i) == _y.bucket_size(_i));                                          \
            */                                                                                                         \
        }                                                                                                              \
    }

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if (!uset_digi_it_done(&_it))                                                                                      \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*_it.ref->value == *(*_iter).value);                                                                    \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())

#ifdef DEBUG

void print_uset(uset_digi *a)
{
    int i = 0;
    foreach (uset_digi, a, it)
        printf("%d: %d [%ld]\n", i++, *it.ref->value, it.buckets - a->buckets);
    printf("--\n");
}
void print_unordered_set(std::unordered_set<DIGI, DIGI_hash> &b)
{
    int i = 0;
    for (auto &x : b)
        printf("%d: %d\n", i++, *x.value);
    printf("--\n");
}
#else
#define print_uset(aa)
#define print_unordered_set(bb)
#endif

#ifdef DEBUG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 15
#define TEST_MAX_VALUE TEST_MAX_SIZE
#else
#define TEST_MAX_VALUE INT_MAX
#endif

static void setup_sets(uset_digi *a, std::unordered_set<DIGI, DIGI_hash> &b)
{
    size_t size = TEST_RAND(TEST_MAX_SIZE);
    LOG("\nsetup_uset %lu\n", size);
    *a = uset_digi_init();
    uset_digi_rehash(a, size);
    for (size_t inserts = 0; inserts < size; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        uset_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
}

static void test_small_size(void)
{
    uset_digi a = uset_digi_init();
    uset_digi_insert(&a, digi_init(1));
    uset_digi_insert(&a, digi_init(2));
    print_uset(&a);
    uset_digi_free(&a);
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    test_small_size();
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        uset_digi a, aa, aaa;
        std::unordered_set<DIGI, DIGI_hash> b, bb, bbb;
        uset_digi_it first, found, it;
        std::unordered_set<DIGI, DIGI_hash>::iterator iter;
        size_t num_a, num_b;
        bool is_a, is_b;
        const int value = TEST_RAND(TEST_MAX_VALUE);
        setup_sets(&a, b);
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
            aa = uset_digi_copy(&a);
            LOG("before\n");
            print_uset(&a);
            list_foreach_ref(uset_digi, &aa, it1)
            {
                // LOG("find %d [%zu]\n", *ref->value, it.bucket_index);
                found = uset_digi_find(&a, *it1.ref);
                assert(!uset_digi_it_done(&found));
            }
            LOG("all found\n");
            list_foreach_ref(uset_digi, &a, it2)
                uset_digi_erase(&aa, *it2.ref);
            LOG("all erased\n");
            print_uset(&a);
            assert(uset_digi_empty(&aa));
            uset_digi_free(&aa);
            break;
        }
        case TEST_INSERT: {
            uset_digi_insert(&a, digi_init(value));
            b.insert(DIGI{value});
            break;
        }
        case TEST_INSERT_FOUND: {
            first = uset_digi_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            int a_found;
            it = uset_digi_insert_found(&a, digi_init(vb), &a_found);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_set<DIGI, DIGI_hash>::iterator, bool> pair;
            pair = b.insert(DIGI{vb});
            // STL returns true if not found, and freshly inserted
            assert((!a_found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            auto iter = b.insert(DIGI{vb});
            CHECK_ITER(it, b, iter);
#endif
            break;
        }
        case TEST_ERASE_IF: {
            num_a = uset_digi_erase_if(&a, digi_is_odd);
#if __cpp_lib_erase_if >= 202002L
            num_b = std::erase_if(b, DIGIc_is_odd); // C++20
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
        case TEST_CONTAINS: {
            is_a = uset_digi_contains(&a, digi_init(value));
#if __cpp_lib_erase_if >= 202002L
            is_b = b.contains(DIGI{value}); // C++20
#else
            is_b = b.count(DIGI{value}) == 1;
#endif
            assert(is_a == is_b);
            break;
        }
        case TEST_ERASE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 0)
                {
                    const int key = TEST_RAND(TEST_MAX_SIZE);
                    digi kd = digi_init(key);
                    uset_digi_erase(&a, kd);
                    b.erase(DIGI{key});
                    digi_free(&kd);
                }
            break;
        }
        case TEST_REHASH: {
            size_t size = uset_digi_size(&a);
            LOG("size %lu -> %lu, cap: %lu\n", size, size * 2, a.bucket_max + 1);
            print_uset(&a);
            print_unordered_set(b);
            b.rehash(size * 2);
            LOG("STL size: %lu, cap: %lu\n", b.size(), b.bucket_count());
            uset_digi_rehash(&a, size * 2);
            print_uset(&a);
            break;
        }
        case TEST_RESERVE: {
            size_t size = uset_digi_size(&a);
            float load = uset_digi_load_factor(&a);
            bb = b;
            const int32_t reserve = size * 2 / load;
            LOG("load %f\n", load);
            if (reserve > 0) // avoid std::bad_alloc
            {
                bb.reserve(reserve);
                LOG("STL reserve by %" PRId32 " %zu\n", reserve, bb.bucket_count());
                LOG("before\n");
                print_uset(&a);
                aa = uset_digi_copy(&a);
                LOG("copy\n");
                print_uset(&aa);
                uset_digi_reserve(&aa, reserve);
                LOG("CTL reserve by %" PRId32 " %zu\n", reserve, aa.bucket_max + 1);
                print_uset(&aa);
                CHECK(aa, bb);
                uset_digi_free(&aa);
            }
            break;
        }
        case TEST_SWAP: {
            aa = uset_digi_copy(&a);
            aaa = uset_digi_init();
            bb = b;
            uset_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            uset_digi_free(&aa);
            uset_digi_free(&aaa);
            break;
        }
        case TEST_COUNT: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            num_a = uset_digi_count(&a, digi_init(key));
            num_b = b.count(DIGI{key});
            assert(num_a == num_b);
            break;
        }
        case TEST_FIND: {
            first = uset_digi_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            digi key = digi_init(vb);
            // find is special, it doesnt free the key
            it = uset_digi_find(&a, key);
            iter= b.find(DIGI{vb});
            if (iter == b.end())
                assert(uset_digi_it_done(&it));
            else
                assert(*iter->value == *it.ref->value);
            digi_free(&key);
            break;
        }
        case TEST_CLEAR: {
            b.clear();
            uset_digi_clear(&a);
            break;
        }
        case TEST_COPY: { // C++20
            aa = uset_digi_copy(&a);
            bb = b;
            CHECK(aa, bb);
            uset_digi_free(&aa);
            break;
        }
        case TEST_EQUAL: {
            aa = uset_digi_copy(&a);
            bb = b;
            print_uset(&aa);
            print_unordered_set(bb);
            assert(uset_digi_equal(&a, &aa));
            assert(b == bb);
            uset_digi_free(&aa);
            break;
        }
#ifdef DEBUG
        case TEST_INSERT_GENERIC: {
            setup_sets(&aa, bb);
            first = uset_digi_begin(&a);
            uset_digi_insert_generic(&a, &first);
            b.insert(bb.begin(), bb.end());
            print_uset(&a);
            print_unordered_set(b);
            CHECK(a, b);
            uset_digi_free(&aa);
            break;
        }
#endif
        case TEST_UNION: {
            setup_sets(&aa, bb);
            aaa = uset_digi_union(&a, &aa);
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
            print_uset(&aa);
            print_unordered_set(bb);
            CHECK(aa, bb);
            print_uset(&aaa);
            print_unordered_set(bbb);
            CHECK(aaa, bbb);
            uset_digi_free(&aa);
            uset_digi_free(&aaa);
            break;
        }
        case TEST_INTERSECTION: {
            setup_sets(&aa, bb);
            aaa = uset_digi_intersection(&a, &aa);
#if 0 // If the STL would be actually usable
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, std::next(bbb.begin())));
#else
            for (const auto &elem : b)
            {
                if (bb.find(DIGI(*elem.value)) != bb.end())
                    bbb.insert(elem);
            }
#endif
            CHECK(aa, bb);
            uset_digi_free(&aa);
            CHECK(aaa, bbb);
            uset_digi_free(&aaa);
            break;
        }
        case TEST_DIFFERENCE: {
            setup_sets(&aa, bb);
            LOG("uset a\n");
            print_uset(&a);
            aaa = uset_digi_difference(&a, &aa);
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
            print_uset(&aa);
            print_unordered_set(bb);
            CHECK(aa, bb);
            uset_digi_free(&aa);
            LOG("uset difference (a-b)\n");
            print_uset(&aaa);
            print_unordered_set(bbb);
            CHECK(aaa, bbb);
            uset_digi_free(&aaa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            setup_sets(&aa, bb);
            aaa = uset_digi_symmetric_difference(&a, &aa);
            print_uset(&aaa);
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
            print_unordered_set(bbb);
            // intersection: b - bb
            for (const auto &elem : b)
            {
                if (bb.find(DIGI(*elem.value)) != bb.end())
                    bbb.erase(elem);
            }
            print_unordered_set(bbb);
#endif
            CHECK(aa, bb);
            uset_digi_free(&aa);
            CHECK(aaa, bbb); // fails
            uset_digi_free(&aaa);
            break;
        }
        case TEST_EMPLACE: // 24
        {
            first = uset_digi_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            digi key = digi_init(vb);
            uset_digi_emplace(&a, &key);
            b.emplace(DIGI{vb});
            break;
        }
        case TEST_EMPLACE_FOUND: {
            first = uset_digi_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            digi key = digi_init(vb);
            int a_found;
            it = uset_digi_emplace_found(&a, &key, &a_found);
#if __cplusplus >= 201103L
            // C++11
            std::pair<std::unordered_set<DIGI, DIGI_hash>::iterator, bool> pair;
            pair = b.emplace(DIGI{vb});
            // STL returns true if not found, and freshly inserted
            assert((!a_found) == (int)pair.second);
            CHECK_ITER(it, b, pair.first);
#else
            iter = b.insert(DIGI{vb});
            CHECK_ITER(it, b, iter);
#endif
            break;
        }
        case TEST_EMPLACE_HINT: {
            // makes not much sense for uset, only set
            first = uset_digi_begin(&a);
            const int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : first.ref ? *first.ref->value : 0;
            digi key = digi_init(vb);
            found = uset_digi_find(&a, key);
            it = uset_digi_emplace_hint(&found, &key);
#if __cplusplus >= 201103L
            // C++11
            auto hint = b.find(DIGI{vb});
            iter = b.emplace_hint(hint, DIGI{vb});
            CHECK_ITER(it, b, iter);
#else
            iter = b.insert(DIGI{vb});
            CHECK_ITER(it, b, iter.first);
#endif
            break;
        }
        // algorithm
        case TEST_FIND_IF: {
            it = uset_digi_find_if(&a, digi_is_odd);
            iter = std::find_if(b.begin(), b.end(), DIGIc_is_odd);
            if (iter == b.end())
                assert(!it.node);
            else
                assert(*iter->value % 2);
            break;
        }
        case TEST_FIND_IF_NOT: {
            it = uset_digi_find_if_not(&a, digi_is_odd);
            iter = std::find_if_not(b.begin(), b.end(), DIGIc_is_odd);
            if (iter == b.end())
                assert(!it.node);
            else
                assert(!(*iter->value % 2));
            break;
        }
        case TEST_ALL_OF: {
            is_a = uset_digi_all_of(&a, digi_is_odd);
            is_b = std::all_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF: {
            is_a = uset_digi_any_of(&a, digi_is_odd);
            is_b = std::any_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF: {
            is_a = uset_digi_none_of(&a, digi_is_odd);
            is_b = std::none_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_COUNT_IF: {
            num_a = uset_digi_count_if(&a, digi_is_odd);
            num_b = std::count_if(b.begin(), b.end(), DIGIc_is_odd);
            assert(num_a == num_b);
            break;
        }
        /* Need some C++ help here.
           I don't think std::generate can be made usable for set, we dont care
           for the insert hint, and we have no operator!= for the STL inserter.
           However our CTL generate for set works fine, just a bit expensive. */
        case TEST_GENERATE: {
            print_uset(&a);
            digi_generate_reset();
            uset_digi_generate(&a, digi_generate);
            LOG("=>\n");
            print_uset(&a);
            digi_generate_reset();
            // std::generate(b.begin(), b.end(), DIGIc_generate);
            // FIXME: need operator!= for insert_operator<set<DIGI>>
            // std::generate(std::inserter(b, b.begin()), std::inserter(bb, bb.begin()),
            //              DIGI_generate);
            // LOG("b\n");
            // print_unordered_set(b);
            size_t n = b.size();
            b.clear();
            for (size_t i = 0; i < n; i++)
                b.insert(DIGI_generate());
            LOG("=>\n");
            print_unordered_set(b);
            CHECK(a, b);
            break;
        }
        case TEST_GENERATE_N: {
            print_uset(&a);
            print_unordered_set(b);
            size_t count = TEST_RAND(20);
            LOG("=> %zu\n", count);
            digi_generate_reset();
            uset_digi_generate_n(&a, count, digi_generate);
            print_uset(&a);
            digi_generate_reset();
            // This is a joke
            // std::generate_n(std::inserter(b, b.begin()), count, DIGI_generate);
            b.clear();
            for (size_t i = 0; i < count; i++)
                b.insert(DIGI_generate());
            print_unordered_set(b);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: {
            print_uset(&a);
            aa = uset_digi_transform(&a, digi_untrans);
            std::transform(b.begin(), b.end(), std::inserter(bb, bb.end()), DIGI_untrans);
            print_uset(&aa);
            print_unordered_set(bb);
            CHECK(aa, bb);
            CHECK(a, b);
            uset_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            print_uset(&a);
            aa = uset_digi_copy_if(&a, digi_is_odd);
#if __cplusplus >= 201103L
            std::copy_if(b.begin(), b.end(), std::inserter(bb, bb.begin()), DIGIc_is_odd);
#else
            for (auto &d : b)
                if (DIGI_is_odd(d))
                    bb.insert(d);
#endif
            CHECK(aa, bb);
            uset_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_MERGE: {
            setup_sets(&aa, bb);
            print_uset(&a);
            print_uset(&aa);
            aaa = uset_digi_merge(&a, &aa);
#if __cpp_lib_node_extract >= 201606L
            b.merge(bb); // C++17
            print_uset(&aaa);
            print_unordered_set(b);
            CHECK(aaa, b);
            b.clear();
            uset_digi_clear(&a);
#else
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            uset_digi_free(&aa);
            uset_digi_free(&aaa);
            break;
        }
        case TEST_MERGE_RANGE: {
            uset_digi_it range_a1, range_a2;
            //std::unordered_set<DIGI>::iterator first_b1, last_b1, first_b2, last_b2;
            //get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            setup_sets(&aa, bb);
            range_a1 = uset_digi_begin(&a);
            range_a2 = uset_digi_begin(&aa);
            //get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            aaa = uset_digi_merge_range(&range_a1, &range_a2);
#if !defined(_MSC_VER)
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            uset_digi_free(&aa);
            uset_digi_free(&aaa);
            break;
        }

#if 0
        case TEST_EXTRACT:
        case TEST_REMOVE_IF:
        case TEST_EQUAL_RANGE:
            printf("nyi\n");
            break;
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
        uset_digi_free(&a);
    }

#if defined CTL_USET_GROWTH_POWER2
    FINISH_TEST("tests/func/test_unordered_set_power2");
#elif defined CTL_USET_CACHED_HASH
    FINISH_TEST("tests/func/test_unordered_set_cached");
#else
    FINISH_TEST(__FILE__);
#endif
}

#endif // C++11
