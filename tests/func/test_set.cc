#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

static inline int
digi_key_compare(digi* a, digi* b)
{
    return (*a->value == *b->value) ? 0 : (*a->value < *b->value) ? -1 : 1;
}

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/set.h>

#include <set>
#include <algorithm>
#include <iterator>

# undef TEST_MAX_SIZE
# define TEST_MAX_SIZE 15
# define TEST_MAX_VALUE 50

#ifndef DEBUG
# define print_set(a)
# define print_setpp(a)
//# define TEST_MAX_VALUE INT_MAX
#else
void print_set(set_digi* a) {
    int i = 0;
    list_foreach_ref(set_digi, a, it)
        printf("[%d] %d\n", i++, *it.ref->value);
    printf("--\n");
}
void print_setpp(std::set<DIGI>& b) {
    int i = 0;
    for(auto& d : b)
        printf("[%d] %d\n", i++, *d.value);
    printf("--\n");
}
#endif

#define CHECK(_x, _y) {                           \
    assert(_x.size == _y.size());                 \
    std::set<DIGI>::iterator _iter = _y.begin();  \
    list_foreach_ref(set_digi, &_x, _it) {        \
        assert(*_it.ref->value == *_iter->value); \
        _iter++;                                  \
    }                                             \
    set_digi_it _it = set_digi_begin(&_x);        \
    for(auto& _d : _y) {                          \
        assert(*_it.ref->value == *_d.value);     \
        set_digi_it_next(&_it);                   \
    }                                             \
}

#define CHECK_ITER(_it, b, _iter)                  \
    if ((_it).node)                                \
    {                                              \
        assert (_iter != b.end());                 \
        assert(*(_it).ref->value == *(*_iter).value); \
    } else                                         \
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
                  std::set<DIGI>& b, std::set<DIGI>::iterator& first_b,
                  std::set<DIGI>::iterator& last_b)
{
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters [%zu, %zu) of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        set_digi_it it1 = set_digi_begin(a);
        set_digi_it_advance(&it1, r1);
        *first_a = it1;
        first_b = b.begin();
        advance(first_b, r1);
        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
            first_a->end = last_a->node;
        }
        else if (r2 == a->size)
        {
            *last_a = set_digi_end(a);
            last_b = b.end();
        }
        else
        {
            set_digi_it it2 = set_digi_begin(a);
            set_digi_it_advance(&it2, r2);
            *last_a = it2;
            last_b = b.begin();
            advance(last_b, r2);
        }
        first_a->end = last_a->node;
    }
    else
    {
        set_digi_it end = set_digi_end(a);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
}

static void
setup_sets(set_digi* a, std::set<DIGI>& b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = set_digi_init(digi_key_compare);
    a->equal = digi_equal;
    for(size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        set_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
    //print_set(a);
    //print_setpp(b);
}

int
main(void)
{
    int errors = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(20);
    for(size_t loop = 0; loop < loops; loop++)
    {
        set_digi a;
        std::set<DIGI> b;
        setup_sets(&a, b);

#define FOREACH_METH(TEST) \
        TEST(SELF) \
        TEST(INSERT) \
        TEST(INSERT_FOUND) \
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
        TEST(ERASE_RANGE) \
        TEST(GENERATE) \
        TEST(GENERATE_N) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM) \
        TEST(TRANSFORM_IT) \
        TEST(TRANSFORM_RANGE) \
        TEST(TRANSFORM_IT_RANGE) \
        TEST(MISMATCH) \
        TEST(SEARCH) \
        TEST(SEARCH_RANGE) \
        TEST(ADJACENT_FIND) \
        TEST(ADJACENT_FIND_RANGE) \

#define FOREACH_DEBUG(TEST) \
        TEST(EMPLACE) /* 44 */ \
        TEST(INSERT_RANGE) \
        TEST(EXTRACT) \
        TEST(MERGE) \
        TEST(EQUAL_RANGE) \
        TEST(GENERATE_RANGE) \
        TEST(FIND_END) \
        TEST(FIND_END_RANGE) \
        TEST(LOWER_BOUND) \
        TEST(UPPER_BOUND) \
        TEST(LOWER_BOUND_RANGE) \
        TEST(UPPER_BOUND_RANGE) \

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
                list_foreach_ref(set_digi, &aa, it)
                    assert(set_digi_find_node(&a, *it.ref));
                //set_digi_clear(&aa);
                set_digi_node* node = set_digi_first(&a);
                while (node)
                {
                    set_digi_node* next = set_digi_node_next(node);
                    set_digi_erase(&aa, node->value);
                    node = next;
                }
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
            case TEST_INSERT_FOUND:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                int found;
                LOG("insert_found %d into\n", vb);
                print_set(&a);
                set_digi_node* node = set_digi_insert_found(&a, digi_init(vb), &found);
                std::pair<std::set<DIGI>::iterator,bool> pair = b.insert(DIGI{vb});
                LOG("a found %d, b found %d\n", found, (int)pair.second);
                assert(found == (pair.second ? 0 : 1));
                assert(*node->value.value == *pair.first->value);
                break;
            }
#ifdef DEBUG
            case TEST_INSERT_RANGE:
            {
                const int vb = TEST_RAND(TEST_MAX_SIZE);
                //set_digi_insert_range(&a, digi_init(vb));
                b.insert(DIGI{vb});
                break;
            }
#endif
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
                        set_digi_it it = set_digi_begin(&a);
                        set_digi_it_advance(&it, 1);
                        set_digi_erase_it(&it);
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
#if __cpp_lib_erase_if >= 202002L
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
                std::set<DIGI> bb = b;
                std::set<DIGI> bbb;
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
                set_digi_it aa = set_digi_find(&a, kd);
                auto bb = b.find(DIGI{key});
                if(bb == b.end())
                    assert(set_digi_it_done(&aa));
                else
                    assert(*aa.ref->value == *bb->value);
                CHECK(a, b);
                digi_free(&kd);
                break;
            }
            case TEST_COPY:
            {
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                CHECK(aa, bb);
                set_digi_free(&aa);
                break;
            }
            case TEST_EQUAL:
            {
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                assert(set_digi_equal(&a, &aa));
                assert(b == bb);
                set_digi_free(&aa);
                break;
            }
            case TEST_UNION:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_union(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_intersection(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                set_digi aaa = set_digi_symmetric_difference(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                print_set(&a);
                set_digi aaa = set_digi_difference(&a, &aa);
//#ifndef _WIN32
                std::set<DIGI> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::inserter(bbb, bbb.begin()));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
                set_digi_free(&aaa);
//#endif
                set_digi_free(&aa);
                break;
            }
            case TEST_FIND_IF:
            {
                set_digi_it aa = set_digi_find_if(&a, digi_is_odd);
                auto bb = find_if(b.begin(), b.end(), DIGIc_is_odd);
                CHECK_ITER(aa, b, bb);
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
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = set_digi_count_range(&first_a, &last_a, digi_init(v)); // leak?
                size_t numb = count(first_b, last_b, DIGI{v});
                assert(numa == numb); // fails with SEED=2490491988
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
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
                std::set<DIGI>::iterator first_b, last_b;
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
                std::set<DIGI>::iterator first_b, last_b;
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
            case TEST_NONE_OF_RANGE:
            {
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = set_digi_none_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = none_of(first_b, last_b, DIGIc_is_odd);
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
            case TEST_FIND_IF_NOT:
            {
                set_digi_it aa = set_digi_find_if_not(&a, digi_is_odd);
                auto bb = find_if_not(b.begin(), b.end(), DIGIc_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                      : random_element(&a);
                digi key = digi_init(vb);
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                LOG("find %d\n", vb);
                set_digi_it aa = set_digi_find_range(&first_a, &last_a, key);
                auto bb = find(first_b, last_b, vb);
                print_set(&a);
                LOG("%d\n", aa.node == last_a.node ? -1 : *aa.ref->value);
                print_setpp(b);
                LOG("vs %d\n", bb == last_b ? -1 : *bb->value);
                if (set_digi_it_done(&aa))
                {
                    assert(bb == last_b);
                }
                else
                    CHECK_ITER(aa, b, bb);
                digi_free (&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi_it aa = set_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                auto bb = find_if(first_b, last_b, DIGIc_is_odd);
                print_set(&a);
                print_setpp(b);
                if (set_digi_it_done(&aa))
                {
                    assert(bb == last_b);
                }
                else
                {
                    LOG("%d\n", *aa.ref->value);
                    LOG("vs %d\n", *bb->value);
                    CHECK_ITER(aa, b, bb);
                }
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi_it aa = set_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto bb = find_if_not(first_b, last_b, DIGIc_is_odd);
                if (set_digi_it_done(&aa))
                {
                    assert(bb == last_b);
                }
                else
                    CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_ERASE_RANGE:
            {
                const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
                for(size_t i = 0; i < erases; i++)
                    if(a.size > 2)
                    {
                        set_digi_it it = set_digi_begin(&a);
                        set_digi_it_advance(&it, 1);
                        set_digi_it end = set_digi_end(&a);
                        set_digi_erase_range(&it, &end);
                        auto iter = b.begin();
                        advance(iter, 1);
                        b.erase(iter, b.end());
                        print_set(&a);
                        print_setpp(b);
                        CHECK(a, b);
                    }
                break;
            }
            /* Need some C++ help here.
               I don't think std::generate can be made usable for set, we dont care
               for the insert hint, and we have no operator!= for the STL inserter.
               However our CTL generate for set works fine, just a bit expensive. */
            case TEST_GENERATE: // 49
            {
                print_set(&a);
                digi_generate_reset();
                set_digi_generate(&a, digi_generate);
                LOG("=>\n");
                print_set(&a);
                digi_generate_reset();
                // std::generate(b.begin(), b.end(), DIGIc_generate);
                std::set<DIGI> bb;
                // FIXME: need operator!= for insert_operator<set<DIGI>>
                // std::generate(std::inserter(b, b.begin()), std::inserter(bb, bb.begin()),
                //              DIGI_generate);
                //LOG("b\n");
                //print_setpp(b);
                size_t n = b.size();
                b.clear();
                for (size_t i=0; i<n; i++)
                    b.insert(DIGI_generate());
                LOG("=>\n");
                print_setpp(b);
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_GENERATE_RANGE:
            {
                print_set(&a);
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                digi_generate_reset();
                set_digi_generate_range(&first_a, &last_a, digi_generate);
                LOG("=>\n");
                print_set(&a);
                digi_generate_reset();
                std::set<DIGI> bb;
                //std::generate(std::inserter(b, first_b), std::inserter(b,
                //              last_b), DIGI_generate);
                size_t n = distance(first_b, last_b);
                b.erase(first_b, last_b);
                for (size_t i=0; i<n; i++)
                    b.insert(DIGI_generate());
                LOG("=> b\n");
                print_setpp(b);
                // FIXME: might fail size
                CHECK(a, b);
                break;
            }
#endif
            case TEST_GENERATE_N:
            {
                print_set(&a);
                print_setpp(b);
                size_t count = TEST_RAND(20);
                LOG("=> %zu\n", count);
                digi_generate_reset();
                set_digi_generate_n(&a, count, digi_generate);
                print_set(&a);
                digi_generate_reset();
                std::generate_n(std::inserter(b, b.begin()), count, DIGI_generate);
                print_setpp(b);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_N_RANGE:
            {
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t off = std::distance(b.begin(), first_b);
                size_t count = TEST_RAND(20 - off);
                digi_generate_reset();
                set_digi_generate_n_range(&first_a, count, digi_generate);
                print_set(&a);
                digi_generate_reset();
                std::generate_n(std::inserter(b, first_b), count, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM: // 47
            {
                print_set(&a);
                set_digi aa = set_digi_transform(&a, digi_untrans);
                std::set<DIGI> bb;
                std::transform(b.begin(), b.end(), std::inserter(bb, bb.end()),
                               DIGI_untrans);
                print_set(&aa);
                print_setpp(bb);
                CHECK(aa, bb);
                CHECK(a, b);
                set_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT: // 50
            {
                print_set(&a);
                if (a.size < 2)
                    break;
                set_digi_it pos = set_digi_begin(&a);
                set_digi_it_advance(&pos, 1);
                set_digi aa = set_digi_transform_it(&a, &pos, digi_bintrans);
                print_set(&aa);
                std::set<DIGI> bb;
                auto it = b.begin();
                advance(it, 1);
                auto end = b.end();
                advance(end, -1);
                std::transform(b.begin(), end, it, std::inserter(bb, bb.begin()),
                               DIGI_bintrans);
                print_setpp(bb);
                CHECK(aa, bb);
                CHECK(a, b);
                set_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_RANGE:
            {
                print_set(&a);
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi aa = set_digi_init(digi_key_compare);
                set_digi_it dest = set_digi_begin(&aa);
                /*set_digi_it it = */
                set_digi_transform_range(&first_a, &last_a, dest, digi_untrans);
                print_set(&aa);
                std::set<DIGI> bb;
                /*auto iter =*/
                std::transform(first_b, last_b, std::inserter(bb, bb.begin()),
                               DIGI_untrans);
                print_setpp(bb);
                //CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                CHECK(a, b);
                set_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT_RANGE:
            {
                print_set(&a);
                if (a.size < 2) // ctl does fine, but STL goes into an endless
                                // loop on size=0
                    break;
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                set_digi_it pos = set_digi_begin(&a);
                set_digi_it_advance(&pos, 1);
                set_digi aa = set_digi_init(digi_key_compare);
                set_digi_it dest = set_digi_begin(&aa);
                set_digi_transform_it_range(&first_a, &last_a, &pos, dest, digi_bintrans);
                print_set(&aa);
                std::set<DIGI> bb;
                auto it2 = b.begin();
                std::advance(it2, 1);
                std::transform(first_b, last_b, it2,
                               std::inserter(bb, bb.begin()), DIGI_bintrans);
                print_setpp(bb);
                //CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                CHECK(a, b);
                set_digi_free(&aa);
                break;
            }
            case TEST_MISMATCH:
            {
                print_set(&a);
                if(a.size < 2)
                    break;
                set_digi aa;
                std::set<DIGI> bb;
                setup_sets(&aa, bb);
                print_set(&aa);
                set_digi_it b1, b2;
                b1 = set_digi_begin(&a);
                b2 = set_digi_begin(&aa);
                set_digi_it r1a, last1_a, r2a, last2_a;
                std::set<DIGI>::iterator r1b, last1_b, r2b, last2_b;
                get_random_iters (&a, &r1a, &last1_a, b, r1b, last1_b);
                get_random_iters (&aa, &r2a, &last2_a, bb, r2b, last2_b);
                /*bool found_a = */set_digi_mismatch(&r1a, &r2a);
                auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
                int d1a = set_digi_it_distance(&b1, &r1a);
                int d2a = set_digi_it_distance(&b2, &r2a);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                //TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                set_digi_free(&aa);
                break;
            }
            case TEST_SEARCH:
            {
                print_set(&a);
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                set_digi_it first_a, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&aa, &first_a, &last_a, bb, first_b, last_b);
                if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                    int vb = *first_b->value;
                    set_digi_insert(&aa, digi_init(vb+1));
                    bb.insert(DIGI{vb+1});
                }
                //print_vec_range(first_a);
                set_digi_it found_a = set_digi_search(&a, &first_a, &last_a);
                auto found_b = search(b.begin(), b.end(), first_b, last_b);
                LOG("found a: %s\n", set_digi_it_done(&found_a) ? "no" : "yes");
                LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
                CHECK_ITER(found_a, b, found_b);
                set_digi_free(&aa);
                break;
            }
            case TEST_SEARCH_RANGE:
            {
                set_digi aa = set_digi_copy(&a);
                std::set<DIGI> bb = b;
                set_digi_it needle, last_a, range;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&aa, &needle, &last_a, bb, first_b, last_b);
                if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                    int vb = *first_b->value;
                    set_digi_insert(&aa, digi_init(vb+1));
                    bb.insert(DIGI{vb+1});
                }
                range = set_digi_begin(&a);
                bool found = set_digi_search_range(&range, &needle);
                auto iter = search(b.begin(), b.end(), first_b, last_b);
                LOG("found a: %s\n", found ? "yes" : "no");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                assert(found == !set_digi_it_done(&range));
                CHECK_ITER(range, b, iter);
                set_digi_free(&aa);
                break;
            }
            case TEST_ADJACENT_FIND:
            {
                print_set(&a);
                set_digi_it aa = set_digi_adjacent_find(&a);
                auto bb = adjacent_find(b.begin(), b.end());
                CHECK_ITER(aa, b, bb);
                LOG("found %s\n", set_digi_it_done(&aa) ? "no" : "yes");
                break;
            }
            case TEST_ADJACENT_FIND_RANGE:
            {
                set_digi_it range, last_a;
                std::set<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &range, &last_a, b, first_b, last_b);
                set_digi_it *aa = set_digi_adjacent_find_range(&range);
                auto bb = adjacent_find(first_b, last_b);
                CHECK_ITER(*aa, b, bb);
                LOG("found %s\n", set_digi_it_done(aa) ? "no" : "yes");
                break;
            }
#ifdef DEBUG
            case TEST_LOWER_BOUND: // 64
            {
                set_digi_it it = set_digi_begin(&a);
                set_digi_it_advance(&it, a.size / 2);
                int median = *it.ref->value;
                set_digi_it aa = set_digi_lower_bound(&a, digi_init(median));
                auto bb = lower_bound(b.begin(), b.end(), DIGI{median});
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_UPPER_BOUND:
            {
                set_digi_it it = set_digi_begin(&a);
                set_digi_it_advance(&it, a.size / 2);
                int median = *it.ref->value;
                set_digi_it aa = set_digi_upper_bound(&a, digi_init(median));
                auto bb = upper_bound(b.begin(), b.end(), DIGI{median});
                CHECK_ITER(aa, b, bb);
                break;
            }
            /**/case TEST_LOWER_BOUND_RANGE:
            {
                break;
            }
            /**/case TEST_UPPER_BOUND_RANGE:
            {
                break;
            }
#endif // DEBUG
#if 0
            case TEST_FIND_END:
            {
                if(a.size > 0)
                {
                    set_digi_it first_a, last_a;
                    set_digi_it aa = set_digi_find_end(&a, &s_first, &s_last);
                    auto bb = std::find_end(b.begin(), b.end(), ...);
                    bool found_a = !set_digi_it_done(&aa);
                    bool found_b = bb != b.end();
                    assert(found_a == found_b);
                    if(found_a && found_b)
                        assert(*(aa->value) == *bb->value);
                }
                break;
            }
            case TEST_FIND_END_RANGE:
            {
                set_digi_it first_a, last_a, s_first, s_last;
                std::set<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                first_a = set_digi_find_end_range(&first_a, &last_a, &s_first_a, &s_last_a);
                auto it = std::find_end(first_b, last_b, vb);
                CHECK_ITER(first_a, b, it);
                CHECK(a, b);
# endif
                break;
            }
#endif // 0
            default:
#ifdef DEBUG
                printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
                printf("unhandled testcase %d\n", which);
#endif
                break;
        }
        //print_set(&a);
        //print_setpp(b);
        CHECK(a, b);
        set_digi_free(&a);
    }
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
