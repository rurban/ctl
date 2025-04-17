#include "../test.h"
#include "digi.hh"

static inline int
digi_key_compare(digi* a, digi* b)
{
    return (*a->value == *b->value) ? 0 : (*a->value < *b->value) ? -1 : 1;
}

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/btree_set.h>

#include <absl/container/btree_set.h>
#include <absl/algorithm/container.h>
#include <iterator>

#define TEST_MAX_VALUE INT_MAX
#ifndef DEBUG
#define print_set(a)
#define print_setpp(a)
#else
//#undef TEST_MAX_SIZE
//#define TEST_MAX_SIZE 15
//#define TEST_MAX_VALUE 50
void print_set(set_digi* a) {
    int i = 0;
    foreach(set_digi, a, it)
        printf("[%d] %d\n", i++, *it.ref->value);
    printf("--\n");
}
void print_setpp(absl::btree_set<DIGI>& b) {
    int i = 0;
    for(auto& d : b)
        printf("[%d] %d\n", i++, *d.value);
    printf("--\n");
}
#endif

#define CHECK(_x, _y) {                           \
    assert(_x.size == _y.size());                 \
    absl::btree_set<DIGI>::iterator _iter = _y.begin();  \
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

#define CHECK_ITER(_node, b, _iter)                              \
    if (_node != NULL)                                           \
    {                                                            \
        assert (_iter != b.end());                               \
        assert(*_node->key.value == *(*_iter).value);            \
    } else                                                       \
        assert (_iter == b.end())

int random_element(set_digi* a)
{
    const size_t index = TEST_RAND(a->size);
    int test_value = 0;
    size_t current = 0;
    foreach(set_digi, a, it)
    {
        if(current == index)
        {
            test_value = *it.ref->value;
            break;
        }
        current++;
    }
    return test_value;
}

static void
get_random_iters (set_digi *a, set_digi_it *first_a, set_digi_it *last_a,
                  absl::btree_set<DIGI>& b, absl::btree_set<DIGI>::iterator& first_b,
                  absl::btree_set<DIGI>::iterator& last_b)
{
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters [%zu, %zu) of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        set_digi_it it1 = set_digi_it_range(a, set_digi_begin(a), NULL);
        first_b = b.begin();
        for(size_t i = 0; i < r1; i++)
        {
            it1.step(&it1);
            first_b++;
        }
        *first_a = it1;
        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            *last_a = set_digi_it_range(a, NULL, NULL);
            last_b = b.end();
        }
        else
        {
            set_digi_it it2 = set_digi_it_range(a, set_digi_begin(a), NULL);
            last_b = b.begin();
            for(size_t i = 0; i < r2; i++)
            {
                it2.step(&it2);
                last_b++;
            }
            *last_a = it2;
        }
        first_a->end = last_a->node;
    }
    else
    {
        set_digi_it end = set_digi_it_range(a, NULL, NULL);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
}

static void
setup_sets(set_digi* a, absl::btree_set<DIGI>& b)
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
    int errors = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        set_digi a;
        absl::btree_set<DIGI> b;
        setup_sets(&a, b);
#define FOREACH_METH(TEST) \
        TEST(SELF) \
        TEST(INSERT) \
        TEST(ERASE) \
        TEST(REMOVE_IF) \
        TEST(ERASE_IF) \
        TEST(ERASE_IT) \
        TEST(CLEAR) \
        TEST(SWAP) \
        TEST(COUNT) \
        TEST(CONTAINS) \
        TEST(FIND) \
        TEST(COPY) \
        TEST(EQUAL) \
        TEST(UNION) \

#define FOREACH_DEBUG(TEST) \
        TEST(ERASE_RANGE) /* broken */ \
        /* TEST(EMPLACE) */ \
        /* TEST(EXTRACT) */ \
        /* TEST(MERGE) */ \
        TEST(EQUAL_RANGE) \
        TEST(INTERSECTION) \
        TEST(SYMMETRIC_DIFFERENCE) \
        TEST(DIFFERENCE) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(COUNT_RANGE) \
        TEST(COUNT_IF) \
        TEST(COUNT_IF_RANGE) \
        TEST(ALL_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF) \
        TEST(NONE_OF_RANGE) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \

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
            case TEST_ERASE_IT:
            {
                const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
                for(size_t i = 0; i < erases; i++)
                    if(a.size > 1)
                    {
                        set_digi_it it = set_digi_it_each(&a);
                        it.step(&it);
                        set_digi_erase_it(&a, &it);
                        auto iter = b.begin();
                        iter++;
                        b.erase(iter);
                        CHECK(a, b);
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
            case TEST_ERASE_IF:
            {
                size_t b_erases = 0;
#if __cpp_lib_erase_if >= 202002000L
                b_erases = std::erase_if(b, DIGIc_is_odd);
#else
                {
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
#endif
                size_t a_erases = set_digi_erase_if(&a, digi_is_odd);
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
                absl::btree_set<DIGI> bb = b;
                absl::btree_set<DIGI> bbb;
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
#if __cpp_lib_erase_if >= 202002L
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
                absl::btree_set<DIGI> bb = b;
                CHECK(aa, bb);
                set_digi_free(&aa);
                break;
            }
            case TEST_EQUAL:
            {
                set_digi aa = set_digi_copy(&a);
                absl::btree_set<DIGI> bb = b;
                assert(set_digi_equal(&a, &aa));
                assert(b == bb);
                set_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_UNION:
            {
                set_digi aa;
                absl::btree_set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_union(&a, &aa);
#if 0
                absl::btree_set<DIGI> bbb;
                absl::btree_set::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                                           std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION:
            {
                set_digi aa;
                absl::btree_set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_intersection(&a, &aa);
#if 0
                absl::btree_set<DIGI> bbb;
                absl::btree_set::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                set_digi aa;
                absl::btree_set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_symmetric_difference(&a, &aa);
#if 0
                absl::btree_set<DIGI> bbb;
                absl::btree_set::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                set_digi aa;
                absl::btree_set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_difference(&a, &aa);
#if 0
                absl::btree_set<DIGI> bbb;
                absl::btree_set::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                                std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_FIND_IF:
            {
                set_digi_node *n = set_digi_find_if(&a, digi_is_odd);
                auto it = find_if(b.begin(), b.end(), DIGIc_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_COUNT_IF:
            {
                size_t count_a = set_digi_count_if(&a, digi_is_odd);
                size_t count_b = count_if(b.begin(), b.end(), DIGIc_is_odd);
                assert(count_a == count_b);
                break;
            }
            case TEST_COUNT_RANGE:
            {
                int test_value = 0;
                int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                     : test_value;
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = set_digi_count_range(&first_a, &last_a, digi_init(v)); // leak?
                size_t numb = count(first_b, last_b, DIGI{v});
                assert(numa == numb); // fails with SEED=2490491988
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = set_digi_count_if_range(&first_a, &last_a,
                                                        digi_is_odd);
                size_t numb = count_if(first_b, last_b, DIGIc_is_odd);
                if (numa != numb)
                {
                    print_set(&a);
                    print_setpp(b);
                    printf ("%d != %d FAIL\n", (int)numa, (int)numb);
                    errors++;
                }
                assert(numa == numb); // off by one, counts one too much
                break;
            }
            case TEST_ALL_OF:
            {
                bool is_a = set_digi_all_of(&a, digi_is_odd);
                bool is_b = all_of(b.begin(), b.end(), DIGIc_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = set_digi_all_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = all_of(first_b, last_b, DIGIc_is_odd);
                if (aa != bb)
                {
                    print_set(&a);
                    print_setpp(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    errors++;
                }
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF:
            {
                bool is_a = set_digi_any_of(&a, digi_is_odd);
                bool is_b = any_of(b.begin(), b.end(), DIGIc_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = set_digi_any_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = any_of(first_b, last_b, DIGIc_is_odd);
                if (aa != bb)
                {
                    print_set(&a);
                    print_setpp(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    errors++;
                }
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = set_digi_none_of(&a, digi_is_odd);
                bool is_b = none_of(b.begin(), b.end(), DIGIc_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                set_digi_node *n = set_digi_find_if_not(&a, digi_is_odd);
                auto it = find_if_not(b.begin(), b.end(), DIGIc_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                      : random_element(&a);
                digi key = digi_init(vb);
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                LOG("find %d\n", vb);
                set_digi_node *n = set_digi_find_range(&first_a, &last_a, key);
                auto it = find(first_b, last_b, vb);
                print_set(&a);
                LOG("%d\n", n == last_a.node ? -1 : *n->key.value);
                print_setpp(b);
                LOG("vs %d\n", it == last_b ? -1 : *it->value);
                if (n == last_a.node) // not found
                {
                    assert(it == last_b);
                }
                else
                    CHECK_ITER(n, b, it);
                digi_free (&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi_node *n = set_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                auto it = find_if(first_b, last_b, DIGIc_is_odd);
                print_set(&a);
                LOG("%d\n", *n->key.value);
                print_setpp(b);
                LOG("vs %d\n", *it->value);
                if (n == last_a.node) // not found
                {
                    assert(it == last_b);
                }
                else
                    CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE: // not ok
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi_node *n =
                    set_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto it = find_if_not(first_b, last_b, DIGIc_is_odd);
                if (n == last_a.node) // not found
                {
                    assert(it == last_b);
                }
                else
                    CHECK_ITER(n, b, it);
                break;
            }
#endif // DEBUG
#if 0  // algorithm and ranges
            case TEST_EQUAL_RANGE:
                printf("nyi\n");
                break;
            case TEST_ERASE_RANGE:
            {
                const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
                for(size_t i = 0; i < erases; i++)
                    if(a.size > 2)
                    {
                        set_digi_it it = set_digi_it_each(&a);
                        it.step(&it);
                        set_digi_it end = set_digi_it_range(&a, NULL, NULL);
                        set_digi_erase_range(&a, &it, &end);
                        auto iter = b.begin();
                        iter++;
                        b.erase(iter, b.end());
                        print_set(&a);
                        print_setpp(b);
                        CHECK(a, b);
                    }
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                set_digi_it first_a, last_a;
                absl::btree_set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = set_digi_none_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = none_of(first_b, last_b, DIGIc_is_odd);
                if (aa != bb)
                {
                    print_set(&a);
                    print_setpp(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    errors++;
                }
                //assert(aa == bb);
                break;
            }
#endif
        }
        CHECK(a, b);
        set_digi_free(&a);
    }
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
