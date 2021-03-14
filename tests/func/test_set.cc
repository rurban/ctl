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
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(EMPLACE) /* 68 */                                                                                             \
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
#define print_set_range(it)
#define print_setpp(a)
//# define TEST_MAX_VALUE INT_MAX
#else
void print_set(set_digi *a)
{
    list_foreach_ref(set_digi, a, it) printf("%d, ", *it.ref->value);
    printf("\n");
}
void print_set_range(set_digi_it it)
{
    set_digi *a = it.container;
    if (!a->size)
        return;
    set_digi_node *n = set_digi_first(a);
    set_digi_node *end = set_digi_last(a);
    for(; n != it.node; n = set_digi_node_next(n))
        printf("%d, ", *n->value.value);
    printf("[");
    for(; n != it.end; n = set_digi_node_next(n))
        printf("%d, ", *n->value.value);
    printf(") ");
    for(; n != end; n = set_digi_node_next(n))
        printf("%d, ", *n->value.value);
    printf("\n");
}
void print_setpp(std::set<DIGI> &b)
{
    for (auto &d : b)
        printf("%d, ", *d.value);
    printf("\n");
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
    if (!set_digi_it_done(&(_it)))                                                                                     \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!set_digi_it_done(&(_it)))                                                                                     \
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
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(20);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        set_digi a, aa, aaa;
        std::set<DIGI> b, bb, bbb;
        set_digi_it it, first_a1, first_a2;
        set_digi_it *pos;
        std::set<DIGI>::iterator iter, first_b1, last_b1, first_b2, last_b2;
        size_t num_a, num_b;
        bool is_a, is_b;

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
        case TEST_SELF: {
            aa = set_digi_copy(&a);
            list_foreach_ref(set_digi, &aa, it1)
                assert(set_digi_find_node(&a, *it1.ref));
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
            aa = set_digi_init_from(&a);
            for (int i = 0; i < TEST_RAND(25); i++)
            {
                set_digi_insert(&aa, digi_init(i));
                bb.insert(DIGI{i});
            }
            print_set(&aa);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            set_digi_insert_range(&a, &first_a2);
            b.insert(first_b2, last_b2);
            print_set(&a);
            print_setpp(b);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_INSERT_GENERIC: {
            print_set(&a);
            aa = set_digi_init_from(&a);
            for (int i = 0; i < TEST_RAND(25); i++)
            {
                set_digi_insert(&aa, digi_init(i));
                bb.insert(DIGI{i});
            }
            print_set(&aa);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            set_digi_insert_generic(&a, &first_a2);
            b.insert(first_b2, last_b2);
            print_set(&a);
            print_setpp(b);
            set_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_ERASE: {
            num_a = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < num_a; i++)
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
            num_a = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < num_a; i++)
                if (a.size > 1)
                {
                    it = set_digi_begin(&a);
                    set_digi_it_advance(&it, 1);
                    set_digi_erase_it(&it);
                    iter = b.begin();
                    iter++;
                    b.erase(iter);
                    CHECK(a, b);
                }
            break;
        }
        case TEST_REMOVE_IF: {
            num_b = 0;
            { // C++20 STD::ERASE_IF
                iter = b.begin();
                auto end = b.end();
                while (iter != end)
                {
                    if (*iter->value % 2)
                    {
                        iter = b.erase(iter);
                        num_b++;
                    }
                    else
                        iter++;
                }
            }
            num_a = set_digi_remove_if(&a, digi_is_odd);
            assert(num_a == num_b);
            break;
        }
        case TEST_ERASE_IF: {
            num_b = 0;
#if __cpp_lib_erase_if >= 202002L
            num_b = std::erase_if(b, DIGIc_is_odd);
#else
            {
                iter = b.begin();
                auto end = b.end();
                while (iter != end)
                {
                    if (*iter->value % 2)
                    {
                        iter = b.erase(iter);
                        num_b++;
                    }
                    else
                        iter++;
                }
            }
#endif
            num_a = set_digi_erase_if(&a, digi_is_odd);
            assert(num_a == num_b);
            break;
        }
        case TEST_CLEAR: {
            b.clear();
            set_digi_clear(&a);
            break;
        }
        case TEST_SWAP: {
            aa = set_digi_copy(&a);
            aaa = set_digi_init(digi_compare);
            bb = b;
            set_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            break;
        }
        case TEST_COUNT: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            num_a = set_digi_count(&a, digi_init(key));
            num_b = b.count(DIGI{key});
            assert(num_a == num_b);
            CHECK(a, b);
            break;
        }
        case TEST_CONTAINS: // C++20
        {
            int key = TEST_RAND(TEST_MAX_SIZE);
            num_a = set_digi_contains(&a, digi_init(key));
#if __cpp_lib_erase_if >= 202002L
            num_b = b.contains(DIGI{key});
#else
            num_b = b.count(DIGI{key}) == 1;
#endif
            assert(num_a == num_b);
            break;
        }
        case TEST_FIND: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            digi kd = digi_init(key);
            it = set_digi_find(&a, kd);
            iter = b.find(DIGI{key});
            if (iter == b.end())
                assert(set_digi_it_done(&it));
            else
                assert(*it.ref->value == *iter->value);
            CHECK(a, b);
            digi_free(&kd);
            break;
        }
        case TEST_COPY: {
            aa = set_digi_copy(&a);
            bb = b;
            CHECK(aa, bb);
            set_digi_free(&aa);
            break;
        }
        case TEST_EQUAL: {
            aa = set_digi_copy(&a);
            bb = b;
            assert(set_digi_equal(&a, &aa));
            assert(b == bb);
            set_digi_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            size_t size1 = MIN(TEST_RAND(a.size), 5);
            if (a.size > size1)
            {
                first_a1 = set_digi_begin(&a);
                set_digi_it_advance(&first_a1, size1);
                set_digi_erase_range(&first_a1);
                iter = b.begin();
                std::advance(iter, size1);
                b.erase(iter, b.end());
            }
            get_random_iters(&a, &first_a1, b, first_b2, last_b2);
            int value = a.size ? *a.root->value.value : 0;
            LOG("equal_value %d\n", value);
            print_set(&a);
            bool same_a = set_digi_equal_value(&first_a1, digi_init(value));
            bool same_b = first_b2 != last_b2;
            for (; first_b2 != last_b2; first_b2++)
            {
                if (value != *(*first_b2).value)
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
            setup_sets(&aa, bb);
            aaa = set_digi_union(&a, &aa);
            //#ifndef _WIN32
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_INTERSECTION: {
            setup_sets(&aa, bb);
            aaa = set_digi_intersection(&a, &aa);
            //#ifndef _WIN32
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            setup_sets(&aa, bb);
            aaa = set_digi_symmetric_difference(&a, &aa);
            //#ifndef _WIN32
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_DIFFERENCE: {
            setup_sets(&aa, bb);
            print_set(&a);
            print_set(&aa);
            aaa = set_digi_difference(&a, &aa);
            //#ifndef _WIN32
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
            set_digi_free(&aaa);
            //#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_IF: {
            it = set_digi_find_if(&a, digi_is_odd);
            iter = find_if(b.begin(), b.end(), DIGIc_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_COUNT_IF: {
            num_a = set_digi_count_if(&a, digi_is_odd);
            num_b = count_if(b.begin(), b.end(), DIGIc_is_odd);
            assert(num_a == num_b);
            break;
        }
        case TEST_COUNT_RANGE: {
            int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : 0;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            num_a = set_digi_count_range(&first_a1, digi_init(v)); // leak?
            num_b = count(first_b1, last_b1, DIGI{v});
            assert(num_a == num_b); // fails with SEED=2490491988
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            num_a = set_digi_count_if_range(&first_a1, digi_is_odd);
            num_b = count_if(first_b1, last_b1, DIGIc_is_odd);
            if (num_a != num_b)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                fail++;
            }
            assert(num_a == num_b); // off by one, counted one too much
            break;
        }
        case TEST_ALL_OF: {
            is_a = set_digi_all_of(&a, digi_is_odd);
            is_b = all_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            is_a = set_digi_all_of_range(&first_a1, digi_is_odd);
            is_b = all_of(first_b1, last_b1, DIGIc_is_odd);
            if (is_a != is_b)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)is_a, (int)is_b);
                fail++;
            }
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF: {
            is_a = set_digi_any_of(&a, digi_is_odd);
            is_b = any_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            is_a = set_digi_any_of_range(&first_a1, digi_is_odd);
            is_b = any_of(first_b1, last_b1, DIGIc_is_odd);
            if (is_a != is_b)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)is_a, (int)is_b);
                fail++;
            }
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF: {
            is_a = set_digi_none_of(&a, digi_is_odd);
            is_b = none_of(b.begin(), b.end(), DIGIc_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_NONE_OF_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            is_a = set_digi_none_of_range(&first_a1, digi_is_odd);
            is_b = none_of(first_b1, last_b1, DIGIc_is_odd);
            if (is_a != is_b)
            {
                print_set(&a);
                print_setpp(b);
                printf("%d != %d is_odd\n", (int)is_a, (int)is_b);
                fail++;
            }
            assert(is_a == is_b);
            break;
        }
        case TEST_FIND_IF_NOT: {
            it = set_digi_find_if_not(&a, digi_is_odd);
            iter = find_if_not(b.begin(), b.end(), DIGIc_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_FIND_RANGE: // 29
        {
            int vb = pick_random(&a);
            digi key = digi_init(vb);
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            LOG("find_range %d\n", vb);
            print_set(&a);
            bool found_a = set_digi_find_range(&first_a1, key);
            iter = find(first_b1, last_b1, vb);
            LOG("%d\n", first_a1.node == first_a1.end ? -1 : *first_a1.ref->value);
            // print_setpp(b);
            LOG("vs %d\n", iter == last_b1 ? -1 : *iter->value);
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            CHECK_RANGE(first_a1, iter, last_b1);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            it = set_digi_find_if_range(&first_a1, digi_is_odd);
            iter = find_if(first_b1, last_b1, DIGIc_is_odd);
            print_set(&a);
            print_setpp(b);
            if (set_digi_it_done(&it))
                assert(iter == last_b1);
            else
            {
                LOG("%d\n", *it.ref->value);
                LOG("vs %d\n", *iter->value);
                CHECK_RANGE(it, iter, last_b1);
            }
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            it = set_digi_find_if_not_range(&first_a1, digi_is_odd);
            iter = find_if_not(first_b1, last_b1, DIGIc_is_odd);
            if (set_digi_it_done(&it))
                assert(iter == last_b1);
            else
                CHECK_RANGE(it, iter, last_b1);
            break;
        }
        case TEST_ERASE_RANGE: {
            const size_t erases = TEST_RAND(TEST_MAX_SIZE) / 4;
            for (size_t i = 0; i < erases; i++)
                if (a.size > 2)
                {
                    it = set_digi_begin(&a);
                    set_digi_it_advance(&it, 1);
                    set_digi_erase_range(&it);
                    iter = b.begin();
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
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            digi_generate_reset();
            set_digi_generate_range(&first_a1, digi_generate);
            LOG("=>\n");
            print_set(&a);
            digi_generate_reset();
            // std::generate(std::inserter(b, first_b), std::inserter(b,
            //              last_b2), DIGI_generate);
            size_t n = distance(first_b1, last_b1);
            b.erase(first_b1, last_b1);
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
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            size_t off = std::distance(first_b1, last_b1);
            size_t count = off > 20 ? TEST_RAND(off - 20) : TEST_RAND(off);
            LOG("generate_n_range %zu\n", count);
            digi_generate_reset();
            set_digi_generate_n_range(&first_a1, count, digi_generate);
            print_set(&a);
            digi_generate_reset();
            std::generate_n(std::inserter(b, first_b1), count, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: // 47
        {
            print_set(&a);
            aa = set_digi_transform(&a, digi_untrans);
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
            it = set_digi_begin(&a);
            set_digi_it_advance(&it, 1);
            aa = set_digi_transform_it(&a, &it, digi_bintrans);
            print_set(&aa);
            iter = b.begin();
            advance(iter, 1);
            auto end = b.end();
            advance(end, -1);
            std::transform(b.begin(), end, iter, std::inserter(bb, bb.begin()), DIGI_bintrans);
            print_setpp(bb);
            CHECK(aa, bb);
            CHECK(a, b);
            set_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            print_set(&a);
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            aa = set_digi_init(digi_compare);
            it = set_digi_begin(&aa);
            /*set_digi_it it = */
            set_digi_transform_range(&first_a1, it, digi_untrans);
            print_set(&aa);
            /*auto iter = */
            std::transform(first_b1, last_b1, std::inserter(bb, bb.begin()), DIGI_untrans);
            print_setpp(bb);
            // CHECK_RANGE(it, iter, last_b1);
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
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            set_digi_it begin = set_digi_begin(&a);
            set_digi_it_advance(&begin, 1);
            aa = set_digi_init(digi_compare);
            set_digi_it dest = set_digi_begin(&aa);
            set_digi_transform_it_range(&first_a1, &begin, dest, digi_bintrans);
            print_set(&aa);
            auto it2 = b.begin();
            std::advance(it2, 1);
            std::transform(first_b1, last_b1, it2, std::inserter(bb, bb.begin()), DIGI_bintrans);
            print_setpp(bb);
            // CHECK_RANGE(it, iter, last_b1);
            CHECK(aa, bb);
            CHECK(a, b);
            set_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            aa = set_digi_copy_if(&a, digi_is_odd);
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
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            aa = set_digi_copy_if_range(&first_a1, digi_is_odd);
#if __cplusplus >= 201103L
            std::copy_if(first_b1, last_b1, std::inserter(bb, bb.begin()), DIGIc_is_odd);
#else
            for (auto d = first_b1; d != last_b1; d++) {
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
            setup_sets(&aa, bb);
            print_set(&aa);
            set_digi_it b1, b2;
            b1 = set_digi_begin(&a);
            b2 = set_digi_begin(&aa);
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
            /*bool found_a = */ set_digi_mismatch(&first_a1, &first_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
            if (!bb.size() || !distance(first_b2, last_b2))
            {
                printf("skip std::mismatch with empty 2nd range. use C++14\n");
                set_digi_free(&aa);
                break;
            }
            auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
            int d1a = set_digi_it_distance(&b1, &first_a1);
            int d2a = set_digi_it_distance(&b2, &first_a2);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == distance(b.begin(), pair.first));
            assert(d2a == distance(bb.begin(), pair.second));
            set_digi_free(&aa);
            break;
        }
        case TEST_SEARCH: {
            print_set(&a);
            aa = set_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                int vb = *first_b2->value;
                set_digi_insert(&aa, digi_init(vb + 1));
                bb.insert(DIGI{vb + 1});
            }
            // print_vec_range(first_a);
            it = set_digi_search(&a, &first_a2);
            iter = search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", set_digi_it_done(&it) ? "no" : "yes");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            CHECK_ITER(it, b, iter);
            set_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            aa = set_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                int vb = *first_b2->value;
                set_digi_insert(&aa, digi_init(vb + 1));
                bb.insert(DIGI{vb + 1});
            }
            first_a1 = set_digi_begin(&a);
            is_a = set_digi_search_range(&first_a1, &first_a2);
            iter = search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", is_a ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(is_a == !set_digi_it_done(&first_a1));
            CHECK_ITER(first_a1, b, iter);
            set_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_set(&a);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            it = set_digi_search_n(&a, count, digi_init(value));
            iter = search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(it, b, iter);
            LOG("found %s at %zu\n", set_digi_it_done(&it) ? "no" : "yes",
                set_digi_it_index(&it));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            pos = set_digi_search_n_range(&first_a1, count, digi_init(value));
            iter = search_n(first_b1, last_b1, count, DIGI{value});
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s at %zu\n", set_digi_it_done(pos) ? "no" : "yes",
                set_digi_it_index(pos));
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_set(&a);
            it = set_digi_adjacent_find(&a);
            iter = adjacent_find(b.begin(), b.end());
            CHECK_ITER(it, b, iter);
            LOG("found %s\n", set_digi_it_done(&it) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            pos = set_digi_adjacent_find_range(&first_a1);
            iter = adjacent_find(first_b1, last_b1);
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s\n", set_digi_it_done(pos) ? "no" : "yes");
            break;
        }
        case TEST_FIND_FIRST_OF: // 51
        {
            setup_sets(&aa, bb);
            last_b2 = bb.end();
            first_a2 = set_digi_begin(&aa);
            if (set_digi_it_index(&first_a2) + 5 < aa.size)
            {
                set_digi_it_advance_end(&first_a2, 5);
                last_b2 = bb.begin();
                std::advance(last_b2, 5);
            }
            print_set(&a);
            LOG("last_b2: %ld\n", std::distance(bb.begin(), last_b2));
            print_set(&aa);
            it = set_digi_find_first_of(&a, &first_a2);
            iter = std::find_first_of(b.begin(), b.end(), bb.begin(), last_b2);
            LOG("=> %s/%s, %ld/%ld\n", !set_digi_it_done(&it) ? "yes" : "no", iter != b.end() ? "yes" : "no",
                set_digi_it_index(&it), distance(b.begin(), iter));
            CHECK_ITER(it, b, iter);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            setup_sets(&aa, bb);
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            print_set(&a);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
            print_set(&aa);

            is_a = set_digi_find_first_of_range(&first_a1, &first_a2);
            iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
            LOG("=> %s/%s, %ld/%ld\n", is_a ? "yes" : "no", iter != last_b1 ? "yes" : "no",
                set_digi_it_index(&first_a1), distance(b.begin(), iter));
            if (is_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            print_set(&a);
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
            first_a2 = set_digi_begin(&aa);
            it = set_digi_find_end(&a, &first_a2);
            iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
            is_a = !set_digi_it_done(&it);
            is_b = iter != b.end();
            LOG("=> %s/%s, %ld/%ld\n", is_a ? "yes" : "no", is_b ? "yes" : "no", set_digi_it_index(&it),
                std::distance(b.begin(), iter));
            CHECK_ITER(it, b, iter);
            assert(is_a == is_b);
            set_digi_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            setup_sets(&aa, bb);
            print_set(&aa);
            first_a2 = set_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
            it = set_digi_find_end_range(&first_a1, &first_a2);
            iter = find_end(first_b1, last_b1, bb.begin(), bb.end());
            CHECK_RANGE(it, iter, last_b1);
#endif
            set_digi_free(&aa);
            break;
        }
        case TEST_LOWER_BOUND: {
            int key = pick_random(&a);
            it = set_digi_lower_bound(&a, digi_init(key));
            iter = lower_bound(b.begin(), b.end(), DIGI{key});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", key, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_UPPER_BOUND: {
            int key = pick_random(&a);
            it = set_digi_upper_bound(&a, digi_init(key));
            iter = upper_bound(b.begin(), b.end(), DIGI{key});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", key, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            int key = pick_random(&a);
            pos = set_digi_lower_bound_range(&first_a1, digi_init(key));
            iter = lower_bound(first_b1, last_b1, DIGI{key});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", key, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            int key = pick_random(&a);
            pos = set_digi_upper_bound_range(&first_a1, digi_init(key));
            iter = upper_bound(first_b1, last_b1, DIGI{key});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", key, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        }
        case TEST_BINARY_SEARCH: {
            int key = pick_random(&a);
            print_set(&a);
            is_a = set_digi_binary_search(&a, digi_init(key));
            is_b = binary_search(b.begin(), b.end(), DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)is_a, (int)is_b);
            assert(is_a == is_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            print_set(&a);
            int key = pick_random(&a);
            is_a = set_digi_binary_search_range(&first_a1, digi_init(key));
            is_b = binary_search(first_b1, last_b1, DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)is_a, (int)is_b);
            assert(is_a == is_b);
            break;
        }
        case TEST_MERGE: {
            aa = set_digi_init_from(&a);
            setup_sets(&aa, bb);
            print_set(&a);
            print_set(&aa);
            aaa = set_digi_merge(&a, &aa);
#if __cpp_lib_node_extract >= 201606L
            b.merge(bb); // C++17
            print_set(&aaa);
            print_setpp(b);
            CHECK(aaa, b);
            b.clear();
            set_digi_clear(&a);
#else
            merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            set_digi_free(&aa);
            set_digi_free(&aaa);
            break;
        }
        case TEST_MERGE_RANGE: {
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            aa = set_digi_init_from(&a);
            setup_sets(&aa, bb);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            aaa = set_digi_merge_range(&first_a1, &first_a2);
#if !defined(_MSC_VER)
            merge(first_b1, last_b1, first_b2, last_b2, std::inserter(bbb, bbb.begin()));
            CHECK(aaa, bbb);
#endif
            set_digi_free(&aa);
            set_digi_free(&aaa);
            break;
        }
        case TEST_INCLUDES: {
          setup_sets(&aa, bb);
          is_a = set_digi_includes(&a, &aa);
          is_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
          LOG("a_found: %d b_found %d\n", (int)is_a, (int)is_b);
          assert(is_a == is_b);
          CHECK(aa, bb);
          set_digi_free(&aa);
          break;
        }
        case TEST_INCLUDES_RANGE: {
          setup_sets(&aa, bb);
          get_random_iters(&a, &first_a1, b, first_b2, last_b2);
          get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
          is_a = set_digi_includes_range(&first_a1, &first_a2);
          is_b = std::includes(first_b1, last_b1, first_b2, last_b2);
          LOG("a_found: %d b_found %d\n", (int)is_a, (int)is_b);
          assert(is_a == is_b);
          CHECK(aa, bb);
          set_digi_free(&aa);
          break;
        }
        case TEST_LEXICOGRAPHICAL_COMPARE: {
            aa = set_digi_copy(&a);
            bb = b;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);
            print_set_range(first_a1);
            print_set_range(first_a2);
            is_a = set_digi_lexicographical_compare(&first_a1, &first_a2);
            is_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
            assert(is_a == is_b);
            set_digi_free(&aa);
            break;
        }
        case TEST_IS_SORTED: {
            get_random_iters(&a, &first_a1, b, first_b2, last_b2);
            print_set_range(first_a1);
            is_a = set_digi_is_sorted(&first_a1);
            is_b = std::is_sorted(first_b2, last_b2);
            LOG("a_yes: %d b_yes %d\n", (int)is_a, (int)is_b);
            assert(is_a == is_b);
            break;
        }
        case TEST_IS_SORTED_UNTIL: {
            get_random_iters(&a, &first_a1, b, first_b2, last_b2);
            print_set_range(first_a1);
            first_a2 = first_a1;
            first_a2.node = first_a1.end;
            pos = set_digi_is_sorted_until(&first_a1, &first_a2);
            first_b2 = std::is_sorted_until(first_b2, last_b2);
            CHECK_RANGE(*pos, first_b2, last_b2);
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
    FINISH_TEST(__FILE__);
}

#endif // C++11
