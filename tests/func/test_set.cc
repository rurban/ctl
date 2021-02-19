#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define USE_INTERNAL_VERIFY
#define T digi
#include <ctl/set.h>

#include <algorithm>
#include <iterator>
#include <set>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(SELF)                                                                                                         \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_FOUND)                                                                                                 \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(ERASE)                                                                                                        \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(ERASE_IF)                                                                                                     \
    TEST(ERASE_IT)                                                                                                     \
    TEST(ERASE_RANGE)                                                                                                  \
    TEST(CLEAR)                                                                                                        \
    TEST(SWAP)                                                                                                         \
    TEST(COUNT)                                                                                                        \
    TEST(CONTAINS)                                                                                                     \
    TEST(FIND)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(EQUAL)                                                                                                        \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(ALL_OF)                                                                                                       \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF)                                                                                                       \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF)                                                                                                      \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_N)                                                                                                   \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM)                                                                                                    \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(TRANSFORM_IT_RANGE)                                                                                           \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)                                                                                                \
    TEST(MISMATCH)                                                                                                     \
    TEST(SEARCH)                                                                                                       \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(SEARCH_N)                                                                                                     \
    TEST(SEARCH_N_RANGE)                                                                                               \
    TEST(ADJACENT_FIND)                                                                                                \
    TEST(ADJACENT_FIND_RANGE)                                                                                          \
    TEST(FIND_FIRST_OF)                                                                                                \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END)                                                                                                     \
    TEST(FIND_END_RANGE)                                                                                               \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)                                                                                          \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(EMPLACE) /* 62 */                                                                                             \
    TEST(EXTRACT)                                                                                                      \
    TEST(GENERATE_RANGE)

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
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
#ifdef DEBUG
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""};
#endif
// clang-format on

#ifndef LONG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 15
#endif
#define TEST_MAX_VALUE 50

// see if 3-way compare can disrupt us
// diable for now, breaks find_range, and is much slower than lower_than compare
static inline int digi_3way_compare(digi *a, digi *b)
{
    return (*a->value == *b->value) ? 0 : (*a->value < *b->value) ? -1 : 1;
}

#ifndef DEBUG
#define print_set(a)
#define print_setpp(a)
//# define TEST_MAX_VALUE INT_MAX
#else
void print_set(set_digi *a)
{
    int i = 0;
    list_foreach_ref(set_digi, a, it) printf("[%d] %d\n", i++, *it.ref->value);
    printf("--\n");
}
void print_setpp(std::set<DIGI> &b)
{
    int i = 0;
    for (auto &d : b)
        printf("[%d] %d\n", i++, *d.value);
    printf("--\n");
}
#endif

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        std::set<DIGI>::iterator _iter = _y.begin();                                                                   \
        list_foreach_ref(set_digi, &_x, _it)                                                                           \
        {                                                                                                              \
            assert(*_it.ref->value == *_iter->value);                                                                  \
            _iter++;                                                                                                   \
        }                                                                                                              \
        set_digi_it _it = set_digi_begin(&_x);                                                                         \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_it.ref->value == *_d.value);                                                                      \
            set_digi_it_next(&_it);                                                                                    \
        }                                                                                                              \
    }

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if (!set_digi_it_done(&_it))                                                                                       \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!set_digi_it_done(&_it))                                                                                       \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

int middle(set_digi *a)
{
    if (!a->size)
        return 0;
    set_digi_node *n1 = set_digi_first(a);
    set_digi_node *n2 = set_digi_last(a);
    return (*n1->value.value - *n2->value.value) / 2;
}

int median(set_digi *a)
{
    set_digi_it it = set_digi_begin(a);
    set_digi_it_advance(&it, a->size / 2);
    return a->size ? *it.ref->value : 0;
}

int pick_element(set_digi *a)
{
    if (!a->size)
        return 0;
    set_digi_it it = set_digi_begin(a);
    set_digi_it_advance(&it, TEST_RAND(a->size));
    return *it.ref->value;
}

int pick_random(set_digi *a)
{
    switch (TEST_RAND(4))
    {
    case 0:
        return middle(a);
    case 1:
        return median(a);
    case 2:
        return pick_element(a);
    case 3:
        return TEST_RAND(TEST_MAX_VALUE);
    }
    assert(0);
}

static void get_random_iters(set_digi *a, set_digi_it *first_a, std::set<DIGI> &b, std::set<DIGI>::iterator &first_b,
                             std::set<DIGI>::iterator &last_b)
{
    set_digi_it last_a;
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
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            last_a = set_digi_end(a);
            last_b = b.end();
        }
        else
        {
            set_digi_it it2 = set_digi_begin(a);
            set_digi_it_advance(&it2, r2);
            last_a = it2;
            last_b = b.begin();
            advance(last_b, r2);
        }
    }
    else
    {
        set_digi_it end = set_digi_end(a);
        *first_a = end;
        last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.node;
}

static void setup_sets(set_digi *a, std::set<DIGI> &b)
{
    size_t iters = TEST_RAND(TEST_MAX_SIZE);
    *a = set_digi_init(digi_compare);
    a->equal = digi_equal;
    for (size_t inserts = 0; inserts < iters; inserts++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        set_digi_insert(a, digi_init(vb));
        b.insert(DIGI{vb});
    }
    // print_set(a);
    // print_setpp(b);
}

int main(void)
{
    int errors = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(20);
    for (size_t loop = 0; loop < loops; loop++)
    {
        set_digi a;
        std::set<DIGI> b;
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
        switch (which)
        {
        case TEST_SELF: {
            set_digi aa = set_digi_copy(&a);
            list_foreach_ref(set_digi, &aa, it) assert(set_digi_find_node(&a, *it.ref));
            // set_digi_clear(&aa);
            set_digi_node *node = set_digi_first(&a);
            while (node)
            {
                set_digi_node *next = set_digi_node_next(node);
                set_digi_erase(&aa, node->value);
                node = next;
            }
            assert(set_digi_empty(&aa));
            set_digi_free(&aa);
            break;
        }
        case TEST_INSERT: {
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            set_digi_insert(&a, digi_init(vb));
            b.insert(DIGI{vb});
            break;
        }
        case TEST_INSERT_FOUND: {
            const int vb = TEST_RAND(TEST_MAX_SIZE);
            int found;
            LOG("insert_found %d into\n", vb);
            print_set(&a);
            set_digi_node *node = set_digi_insert_found(&a, digi_init(vb), &found);
            std::pair<std::set<DIGI>::iterator, bool> pair = b.insert(DIGI{vb});
            LOG("a found %d, b found %d\n", found, (int)pair.second);
            assert(found == (pair.second ? 0 : 1));
            assert(*node->value.value == *pair.first->value);
            break;
        }
        case TEST_INSERT_RANGE: {
            print_set(&a);
            set_digi aa = set_digi_init_from(&a);
            std::set<DIGI> bb;
            for (int i = 0; i < TEST_RAND(25); i++)
            {
                set_digi_insert(&aa, digi_init(i));
                bb.insert(DIGI{i});
            }
            print_set(&aa);
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &first_a, bb, first_b, last_b);

            set_digi_insert_range(&a, &first_a);
            b.insert(first_b, last_b);
            print_set(&a);
            print_setpp(b);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_GENERIC: {
            print_set(&a);
            set_digi aa = set_digi_init_from(&a);
            std::set<DIGI> bb;
            for (int i = 0; i < TEST_RAND(25); i++)
            {
                set_digi_insert(&aa, digi_init(i));
                bb.insert(DIGI{i});
            }
            print_set(&aa);
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &first_a, bb, first_b, last_b);

            set_digi_insert_generic(&a, &first_a);
            b.insert(first_b, last_b);
            print_set(&a);
            print_setpp(b);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_ERASE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 0)
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
        case TEST_ERASE_IT: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 1)
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
        case TEST_REMOVE_IF: {
            size_t b_erases = 0;
            { // C++20 STD::ERASE_IF
                auto iter = b.begin();
                auto end = b.end();
                while (iter != end)
                {
                    if (*iter->value % 2)
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
        case TEST_ERASE_IF: {
            size_t b_erases = 0;
#if __cpp_lib_erase_if >= 202002L
            b_erases = std::erase_if(b, DIGIc_is_odd);
#else
            {
                auto iter = b.begin();
                auto end = b.end();
                while (iter != end)
                {
                    if (*iter->value % 2)
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
        case TEST_CLEAR: {
            b.clear();
            set_digi_clear(&a);
            break;
        }
        case TEST_SWAP: {
            set_digi aa = set_digi_copy(&a);
            set_digi aaa = set_digi_init(digi_compare);
            std::set<DIGI> bb = b;
            std::set<DIGI> bbb;
            set_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            break;
        }
        case TEST_COUNT: {
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
        case TEST_FIND: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            digi kd = digi_init(key);
            set_digi_it aa = set_digi_find(&a, kd);
            auto bb = b.find(DIGI{key});
            if (bb == b.end())
                assert(set_digi_it_done(&aa));
            else
                assert(*aa.ref->value == *bb->value);
            CHECK(a, b);
            digi_free(&kd);
            break;
        }
        case TEST_COPY: {
            set_digi aa = set_digi_copy(&a);
            std::set<DIGI> bb = b;
            CHECK(aa, bb);
            set_digi_free(&aa);
            break;
        }
        case TEST_EQUAL: {
            set_digi aa = set_digi_copy(&a);
            std::set<DIGI> bb = b;
            assert(set_digi_equal(&a, &aa));
            assert(b == bb);
            set_digi_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            size_t size1 = MIN(TEST_RAND(a.size), 5);
            set_digi_it r1a;
            if (a.size > size1)
            {
                r1a = set_digi_begin(&a);
                set_digi_it_advance(&r1a, size1);
                set_digi_erase_range(&r1a);
                auto it = b.begin();
                std::advance(it, size1);
                b.erase(it, b.end());
            }
            std::set<DIGI>::iterator r1b, last1_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            int value = a.size ? *a.root->value.value : 0;
            LOG("equal_value %d\n", value);
            print_set(&a);
            bool same_a = set_digi_equal_value(&r1a, digi_init(value));
            bool same_b = r1b != last1_b;
            for (; r1b != last1_b; r1b++)
            {
                if (value != *(*r1b).value)
                {
                    same_b = false;
                    break;
                }
            }
            LOG("same_a: %d same_b: %d\n", (int)same_a, (int)same_b);
            assert(same_a == same_b);
            break;
        }
#ifdef DEBUG
        case TEST_EQUAL_RANGE: {
            int key = median(&a);
            set_digi_it lower, upper;
            set_digi_equal_range(&a, digi_init(key), &lower, &upper);
            auto pair = b.equal_range(DIGI{key});
            (void)pair;
            // TODO test
            break;
        }
#endif // DEBUG
        case TEST_UNION: {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            set_digi aaa = set_digi_union(&a, &aa);
            //#ifndef _WIN32
            std::set<DIGI> bbb;
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_INTERSECTION: {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            set_digi aaa = set_digi_intersection(&a, &aa);
            //#ifndef _WIN32
            std::set<DIGI> bbb;
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            set_digi aaa = set_digi_symmetric_difference(&a, &aa);
            //#ifndef _WIN32
            std::set<DIGI> bbb;
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_DIFFERENCE: {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            print_set(&a);
            print_set(&aa);
            set_digi aaa = set_digi_difference(&a, &aa);
            //#ifndef _WIN32
            std::set<DIGI> bbb;
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_IF: {
            set_digi_it aa = set_digi_find_if(&a, digi_is_odd);
            auto bb = find_if(b.begin(), b.end(), DIGIc_is_odd);
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_COUNT_IF: {
            size_t count_a = set_digi_count_if(&a, digi_is_odd);
            size_t count_b = count_if(b.begin(), b.end(), DIGIc_is_odd);
            assert(count_a == count_b);
            break;
        }
        case TEST_COUNT_RANGE: {
            int test_value = 0;
            int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : test_value;
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t numa = set_digi_count_range(&first_a, digi_init(v)); // leak?
            size_t numb = count(first_b, last_b, DIGI{v});
            assert(numa == numb); // fails with SEED=2490491988
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t numa = set_digi_count_if_range(&first_a, digi_is_odd);
            size_t numb = count_if(first_b, last_b, DIGIc_is_odd);
            if (numa != numb)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d FAIL\n", (int)numa, (int)numb);
                errors++;
            }
            assert(numa == numb); // off by one, counted one too much
            break;
        }
        case TEST_ALL_OF: {
            bool is_a = set_digi_all_of(&a, digi_is_odd);
            bool is_b = all_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = set_digi_all_of_range(&first_a, digi_is_odd);
            bool bb = all_of(first_b, last_b, DIGIc_is_odd);
            if (aa != bb)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
                errors++;
            }
            assert(aa == bb);
            break;
        }
        case TEST_ANY_OF: {
            bool is_a = set_digi_any_of(&a, digi_is_odd);
            bool is_b = any_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = set_digi_any_of_range(&first_a, digi_is_odd);
            bool bb = any_of(first_b, last_b, DIGIc_is_odd);
            if (aa != bb)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
                errors++;
            }
            assert(aa == bb);
            break;
        }
        case TEST_NONE_OF: {
            bool is_a = set_digi_none_of(&a, digi_is_odd);
            bool is_b = none_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = set_digi_none_of_range(&first_a, digi_is_odd);
            bool bb = none_of(first_b, last_b, DIGIc_is_odd);
            if (aa != bb)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
                errors++;
            }
            assert(aa == bb);
            break;
        }
        case TEST_FIND_IF_NOT: {
            set_digi_it aa = set_digi_find_if_not(&a, digi_is_odd);
            auto bb = find_if_not(b.begin(), b.end(), DIGIc_is_odd);
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_FIND_RANGE: // 29
        {
            int vb = pick_random(&a);
            digi key = digi_init(vb);
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            LOG("find_range %d\n", vb);
            print_set(&a);
            bool found_a = set_digi_find_range(&first_a, key);
            auto bb = find(first_b, last_b, vb);
            LOG("%d\n", first_a.node == first_a.end ? -1 : *first_a.ref->value);
            // print_setpp(b);
            LOG("vs %d\n", bb == last_b ? -1 : *bb->value);
            if (found_a)
                assert(bb != last_b);
            else
                assert(bb == last_b);
            CHECK_RANGE(first_a, bb, last_b);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            set_digi_it aa = set_digi_find_if_range(&first_a, digi_is_odd);
            auto bb = find_if(first_b, last_b, DIGIc_is_odd);
            print_set(&a);
            print_setpp(b);
            if (set_digi_it_done(&aa))
                assert(bb == last_b);
            else
            {
                LOG("%d\n", *aa.ref->value);
                LOG("vs %d\n", *bb->value);
                CHECK_RANGE(aa, bb, last_b);
            }
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            set_digi_it aa = set_digi_find_if_not_range(&first_a, digi_is_odd);
            auto bb = find_if_not(first_b, last_b, DIGIc_is_odd);
            if (set_digi_it_done(&aa))
                assert(bb == last_b);
            else
                CHECK_RANGE(aa, bb, last_b);
            break;
        }
        case TEST_ERASE_RANGE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 2)
                {
                    set_digi_it it = set_digi_begin(&a);
                    set_digi_it_advance(&it, 1);
                    set_digi_erase_range(&it);
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
            // LOG("b\n");
            // print_setpp(b);
            size_t n = b.size();
            b.clear();
            for (size_t i = 0; i < n; i++)
                b.insert(DIGI_generate());
            LOG("=>\n");
            print_setpp(b);
            CHECK(a, b);
            break;
        }
#ifdef DEBUG
        case TEST_GENERATE_RANGE: {
            print_set(&a);
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            digi_generate_reset();
            set_digi_generate_range(&first_a, digi_generate);
            LOG("=>\n");
            print_set(&a);
            digi_generate_reset();
            std::set<DIGI> bb;
            // std::generate(std::inserter(b, first_b), std::inserter(b,
            //              last_b), DIGI_generate);
            size_t n = distance(first_b, last_b);
            b.erase(first_b, last_b);
            for (size_t i = 0; i < n; i++)
                b.insert(DIGI_generate());
            LOG("=> b\n");
            print_setpp(b);
            // FIXME: might fail size
            CHECK(a, b);
            break;
        }
#endif
        case TEST_GENERATE_N: {
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
        case TEST_GENERATE_N_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
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
            std::transform(b.begin(), b.end(), std::inserter(bb, bb.end()), DIGI_untrans);
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
            std::transform(b.begin(), end, it, std::inserter(bb, bb.begin()), DIGI_bintrans);
            print_setpp(bb);
            CHECK(aa, bb);
            CHECK(a, b);
            set_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            print_set(&a);
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            set_digi aa = set_digi_init(digi_compare);
            set_digi_it dest = set_digi_begin(&aa);
            /*set_digi_it it = */
            set_digi_transform_range(&first_a, dest, digi_untrans);
            print_set(&aa);
            std::set<DIGI> bb;
            /*auto iter = */
            std::transform(first_b, last_b, std::inserter(bb, bb.begin()), DIGI_untrans);
            print_setpp(bb);
            // CHECK_RANGE(it, iter, last_b);
            CHECK(aa, bb);
            CHECK(a, b);
            set_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_IT_RANGE: {
            print_set(&a);
            if (a.size < 2) // ctl does fine, but STL goes into an endless
                            // loop on size=0
                break;
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            set_digi_it pos = set_digi_begin(&a);
            set_digi_it_advance(&pos, 1);
            set_digi aa = set_digi_init(digi_compare);
            set_digi_it dest = set_digi_begin(&aa);
            set_digi_transform_it_range(&first_a, &pos, dest, digi_bintrans);
            print_set(&aa);
            std::set<DIGI> bb;
            auto it2 = b.begin();
            std::advance(it2, 1);
            std::transform(first_b, last_b, it2, std::inserter(bb, bb.begin()), DIGI_bintrans);
            print_setpp(bb);
            // CHECK_RANGE(it, iter, last_b);
            CHECK(aa, bb);
            CHECK(a, b);
            set_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            set_digi aa = set_digi_copy_if(&a, digi_is_odd);
            std::set<DIGI> bb;
#if __cplusplus >= 201103L
            std::copy_if(b.begin(), b.end(), std::inserter(bb, bb.begin()), DIGIc_is_odd);
#else
            for (auto &d : b)
                if (DIGI_is_odd(d))
                    bb.push_back(d);
#endif
            CHECK(aa, bb);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY_IF_RANGE: {
            set_digi_it range;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            set_digi aa = set_digi_copy_if_range(&range, digi_is_odd);
            std::set<DIGI> bb;
#if __cplusplus >= 201103L
            std::copy_if(first_b, last_b, std::inserter(bb, bb.begin()), DIGIc_is_odd);
#else
            for (auto d = first_b; d != last_b; d++) {
                if (DIGI_is_odd(*d))
                    bb.push_back(*d);
            }
#endif
            CHECK(aa, bb);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_MISMATCH: {
            print_set(&a);
            if (a.size < 2)
                break;
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            print_set(&aa);
            set_digi_it b1, b2;
            b1 = set_digi_begin(&a);
            b2 = set_digi_begin(&aa);
            set_digi_it r1a, r2a;
            std::set<DIGI>::iterator r1b, last1_b, r2b, last2_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            get_random_iters(&aa, &r2a, bb, r2b, last2_b);
            /*bool found_a = */ set_digi_mismatch(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
#else
            if (!bb.size() || !distance(r2b, last2_b))
            {
                printf("skip std::mismatch with empty 2nd range. use C++14\n");
                set_digi_free(&aa);
                break;
            }
            auto pair = std::mismatch(r1b, last1_b, r2b);
#endif
            int d1a = set_digi_it_distance(&b1, &r1a);
            int d2a = set_digi_it_distance(&b2, &r2a);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == distance(b.begin(), pair.first));
            assert(d2a == distance(bb.begin(), pair.second));
            set_digi_free(&aa);
            break;
        }
        case TEST_SEARCH: {
            print_set(&a);
            set_digi aa = set_digi_copy(&a);
            std::set<DIGI> bb = b;
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &first_a, bb, first_b, last_b);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                int vb = *first_b->value;
                set_digi_insert(&aa, digi_init(vb + 1));
                bb.insert(DIGI{vb + 1});
            }
            // print_vec_range(first_a);
            set_digi_it found_a = set_digi_search(&a, &first_a);
            auto found_b = search(b.begin(), b.end(), first_b, last_b);
            LOG("found a: %s\n", set_digi_it_done(&found_a) ? "no" : "yes");
            LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
            CHECK_ITER(found_a, b, found_b);
            set_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            set_digi aa = set_digi_copy(&a);
            std::set<DIGI> bb = b;
            set_digi_it needle, range;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &needle, bb, first_b, last_b);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                int vb = *first_b->value;
                set_digi_insert(&aa, digi_init(vb + 1));
                bb.insert(DIGI{vb + 1});
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
        case TEST_SEARCH_N: {
            print_set(&a);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            set_digi_it aa = set_digi_search_n(&a, count, digi_init(value));
            auto bb = search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(aa, b, bb);
            LOG("found %s at %zu\n", set_digi_it_done(&aa) ? "no" : "yes",
                set_digi_it_index(&aa));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            set_digi_it range;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            set_digi_it *aa = set_digi_search_n_range(&range, count, digi_init(value));
            auto bb = search_n(first_b, last_b, count, DIGI{value});
            CHECK_RANGE(*aa, bb, last_b);
            LOG("found %s at %zu\n", set_digi_it_done(aa) ? "no" : "yes",
                set_digi_it_index(aa));
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_set(&a);
            set_digi_it aa = set_digi_adjacent_find(&a);
            auto bb = adjacent_find(b.begin(), b.end());
            CHECK_ITER(aa, b, bb);
            LOG("found %s\n", set_digi_it_done(&aa) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            set_digi_it range;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            set_digi_it *aa = set_digi_adjacent_find_range(&range);
            auto bb = adjacent_find(first_b, last_b);
            CHECK_RANGE(*aa, bb, last_b);
            LOG("found %s\n", set_digi_it_done(aa) ? "no" : "yes");
            break;
        }
        case TEST_FIND_FIRST_OF: // 51
        {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            std::set<DIGI>::iterator bb_last = bb.end();
            set_digi_it range2 = set_digi_begin(&aa);
            if (set_digi_it_index(&range2) + 5 < aa.size)
            {
                set_digi_it_advance_end(&range2, 5);
                bb_last = bb.begin();
                std::advance(bb_last, 5);
            }
            print_set(&a);
            LOG("bb_last: %ld\n", std::distance(bb.begin(), bb_last));
            print_set(&aa);
            set_digi_it it = set_digi_find_first_of(&a, &range2);
            auto iter = std::find_first_of(b.begin(), b.end(), bb.begin(), bb_last);
            LOG("=> %s/%s, %ld/%ld\n", !set_digi_it_done(&it) ? "yes" : "no", iter != b.end() ? "yes" : "no",
                set_digi_it_index(&it), distance(b.begin(), iter));
            CHECK_ITER(it, b, iter);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            set_digi_it first_a, s_first;
            std::set<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            print_set(&a);
            get_random_iters(&aa, &s_first, bb, s_first_b, s_last_b);
            print_set(&aa);

            bool found_a = set_digi_find_first_of_range(&first_a, &s_first);
            auto it = std::find_first_of(first_b, last_b, s_first_b, s_last_b);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", it != last_b ? "yes" : "no", set_digi_it_index(&first_a),
                distance(b.begin(), it));
            if (found_a)
                assert(it != last_b);
            else
                assert(it == last_b);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            print_set(&a);
            set_digi aa;
            std::set<DIGI> bb;
            set_digi_it it;
            setup_sets(&aa, bb);
            if (aa.size > 4)
            {
                int size2 = TEST_RAND(4);
                it = set_digi_begin(&aa);
                set_digi_it_advance(&it, size2);
                set_digi_erase_range(&it);
                auto itb = bb.begin();
                std::advance(itb, size2);
                bb.erase(itb, bb.end());
            }
            print_set(&aa);
            set_digi_it s_first = set_digi_begin(&aa);
            it = set_digi_find_end(&a, &s_first);
            auto iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
            bool found_a = !set_digi_it_done(&it);
            bool found_b = iter != b.end();
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", set_digi_it_index(&it),
                std::distance(b.begin(), iter));
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            set_digi_it first_a, s_first;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            set_digi aa;
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            print_set(&aa);
            s_first = set_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
            first_a = set_digi_find_end_range(&first_a, &s_first);
            auto it = find_end(first_b, last_b, bb.begin(), bb.end());
            CHECK_RANGE(first_a, it, last_b);
#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_LOWER_BOUND: {
            int key = pick_random(&a);
            set_digi_it aa = set_digi_lower_bound(&a, digi_init(key));
            std::set<DIGI>::iterator bb = lower_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_UPPER_BOUND: {
            int key = pick_random(&a);
            set_digi_it aa = set_digi_upper_bound(&a, digi_init(key));
            std::set<DIGI>::iterator bb = upper_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            set_digi_it *aa = set_digi_lower_bound_range(&first_a, digi_init(key));
            std::set<DIGI>::iterator bb = lower_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            set_digi_it first_a;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            set_digi_it *aa = set_digi_upper_bound_range(&first_a, digi_init(key));
            std::set<DIGI>::iterator bb = upper_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_BINARY_SEARCH: {
            int key = pick_random(&a);
            print_set(&a);
            bool found_a = set_digi_binary_search(&a, digi_init(key));
            bool found_b = binary_search(b.begin(), b.end(), DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            set_digi_it range;
            std::set<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            print_set(&a);
            int key = pick_random(&a);
            bool found_a = set_digi_binary_search_range(&range, digi_init(key));
            bool found_b = binary_search(first_b, last_b, DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_MERGE: {
            set_digi aa = set_digi_init_from(&a);
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            print_set(&a);
            print_set(&aa);
            set_digi aaa = set_digi_merge(&a, &aa);
#if __cpp_lib_node_extract >= 201606L
            b.merge(bb); // C++17
            print_set(&aaa);
            print_setpp(b);
            CHECK(aaa, b);
            b.clear();
            set_digi_clear(&a);
#else
            std::set<DIGI> bbb;
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            set_digi_free(&aa);
            set_digi_free(&aaa);
            break;
        }
        case TEST_MERGE_RANGE: {
            set_digi_it range_a1, range_a2;
            std::set<DIGI>::iterator first_b1, last_b1, first_b2, last_b2;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            set_digi aa = set_digi_init_from(&a);
            std::set<DIGI> bb;
            setup_sets(&aa, bb);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            set_digi aaa = set_digi_merge_range(&range_a1, &range_a2);
#if !defined(_MSC_VER)
            std::set<DIGI> bbb;
            merge(first_b1, last_b1, first_b2, last_b2, std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            set_digi_free(&aa);
            set_digi_free(&aaa);
            break;
        }

        default:
#ifdef DEBUG
            printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
        // print_set(&a);
        // print_setpp(b);
        CHECK(a, b);
        set_digi_free(&a);
    }
    queue_int_free(&tests);
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
