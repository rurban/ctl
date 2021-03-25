#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else
#include "digi.hh"

#define T digi
#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#include <ctl/forward_list.h>

#include <forward_list>
#include <algorithm>
#include <numeric>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH_FRONT)                                                                                                   \
    TEST(POP_FRONT)                                                                                                    \
    TEST(ERASE_AFTER)                                                                                                  \
    TEST(ERASE_RANGE)                                                                                                  \
    TEST(INSERT_AFTER)                                                                                                 \
    TEST(CLEAR)                                                                                                        \
    TEST(SWAP)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(REVERSE)                                                                                                      \
    TEST(REMOVE)                                                                                                       \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(EQUAL)                                                                                                        \
    TEST(UNIQUE)                                                                                                       \
    TEST(FIND)                                                                                                         \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)                                                                                                \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_RANGE)                                                                                               \
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(MISMATCH)                                                                                                     \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(SEARCH_N)                                                                                                     \
    TEST(ADJACENT_FIND)                                                                                                \
    TEST(ADJACENT_FIND_RANGE)                                                                                          \
    TEST(FIND_FIRST_OF)                                                                                                \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END)                                                                                                     \
    TEST(FIND_END_RANGE)                                                                                               \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(SORT)                                                                                                         \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_UNSORTED)                                                                                               \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(SEARCH_N_RANGE)                                                                                               \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(ASSIGN)                                                                                                       \
    TEST(SPLICE_AFTER)                                                                                                 \
    TEST(SORT_RANGE)                                                                                                   \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(SEARCH)                                                                                                       \
    TEST(TRANSFORM)                                                                                                    \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(DIFFERENCE_RANGE)                                                                                             \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(UNIQUE_RANGE)                                                                                                 \
    TEST(GENERATE_N)                                                                                                   \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(REVERSE_RANGE) /* 81 */

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

void print_slist(slist_digi *a)
{
    foreach(slist_digi, a, it)
        printf ("%d ", *it.ref->value);
    printf ("\n");
}
void print_slist_range(slist_digi_it it)
{
    slist_digi *a = it.container;
    slist_digi_node *n = a->head;
    for(; n != it.node; n = n->next)
        printf("%d ", *n->value.value);
    printf("[");
    for(; n != it.end; n = n->next)
        printf("%d ", *n->value.value);
    printf(") ");
    for(; n; n = n->next)
        printf("%d ", *n->value.value);
    printf("\n");
}
void print_fwlist(std::forward_list<DIGI> &b)
{
    for(auto& d: b)
        printf ("%d ", *d.value);
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 100
#ifndef LONG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 25
#endif
#else
#define print_slist(x)
#define print_slist_range(x)
#define print_fwlist(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int pick_random(slist_digi *a)
{
    (void)a;
    return TEST_RAND(TEST_MAX_VALUE);
}

#define CHECK(_x, _y) {                                                 \
    assert(slist_digi_empty(&_x) == _y.empty());                        \
    if(!slist_digi_empty(&_x)) {                                        \
      assert(*_y.front().value == *slist_digi_front(&_x)->value);       \
    }                                                                   \
    std::forward_list<DIGI>::iterator _iter = _y.begin();               \
    foreach(slist_digi, &_x, _it) {                                     \
      assert(*_it.ref->value == *_iter->value);                         \
      _iter++;                                                          \
    }                                                                   \
    slist_digi_it _it = slist_digi_begin(&_x);                          \
    for(auto& _d : _y) {                                                \
      assert(*_it.ref->value == *_d.value);                             \
      slist_digi_it_next(&_it);                                         \
    }                                                                   \
}

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if (!slist_digi_it_done(&(_it)))                                                                                   \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!slist_digi_it_done(&(_it)))                                                                                   \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

static void
setup_lists(slist_digi* a, std::forward_list<DIGI>& b, size_t size, int* max_value)
{
    *a = slist_digi_init();
    a->equal = digi_equal;
    a->compare = digi_compare;
    for(size_t pushes = 0; pushes < size; pushes++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE);
        if(max_value && value > *max_value)
            *max_value = value;
        slist_digi_push_front(a, digi_init(value));
        b.push_front(DIGI{value});
    }
}

// slist_digi_it* first_a;
// _List_iterator<DIGI>* first_b, *last_b;
static void get_random_iters(slist_digi *a, slist_digi_it *first_a, std::forward_list<DIGI> &b,
                             std::forward_list<DIGI>::iterator &first_b, std::forward_list<DIGI>::iterator &last_b)
{
    slist_digi_it last_a;
    size_t size = slist_digi_size(a);
    size_t r1 = TEST_RAND(size / 2);
    const size_t rnd = TEST_RAND(size / 2);
    size_t r2 = MIN(r1 + rnd, size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, size);
    if (size)
    {
        slist_digi_it it1 = slist_digi_begin(a);
        slist_digi_it_advance(&it1, r1);
        first_b = b.begin();
        std::advance(first_b, r1);
        *first_a = it1;
        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
            first_a->end = last_a.node;
        }
        else if (r2 == size)
        {
            last_a = slist_digi_end(a);
            last_b = b.end();
        }
        else
        {
            slist_digi_it it2 = slist_digi_begin(a);
            slist_digi_it_advance(&it2, r2);
            last_b = b.begin();
            std::advance(last_b, r2);
            last_a = it2;
        }
    }
    else
    {
        slist_digi_it end = slist_digi_end(a);
        *first_a = end;
        last_a = end;
        last_a.end = first_a->node;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.node;
}

int
main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for(size_t loop = 0; loop < loops; loop++)
    {
        slist_digi a, aa, aaa;
        std::forward_list<DIGI> b, bb, bbb;
        int value = TEST_RAND(TEST_MAX_VALUE);
        const size_t size = TEST_RAND(TEST_MAX_SIZE);
        size_t index = TEST_RAND(size);
        slist_digi_it range_a1, range_a2, it;
        slist_digi_it *pos;
        std::forward_list<DIGI>::iterator first_b1, last_b1, first_b2, last_b2, iter;
        size_t num_a, num_b;
        bool found_a, found_b;

        int max_value = 0;
        setup_lists(&a, b, size, &max_value);

        u16 which;
        if (tests.size)
        {
            which = (u16)*queue_int_front(&tests);
            queue_int_pop(&tests);
        } else
            which = (u16)(test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        RECORD_WHICH;
        LOG ("TEST %s %d\n", test_names[which], which);
        switch (which)
        {
        case TEST_PUSH_FRONT:
            slist_digi_push_front(&a, digi_init(value));
            b.push_front(DIGI{value});
            CHECK(a, b);
            break;
        case TEST_POP_FRONT:
            if (!slist_digi_empty(&a))
            {
                slist_digi_pop_front(&a);
                b.pop_front();
            }
            CHECK(a, b);
            break;
        case TEST_ERASE_AFTER: {
            size_t current = 0;
            iter = b.begin();
            LOG("erase_after %ld: ", index);
            print_slist(&a);
            if (index == 0)
            {
                slist_digi_erase_after(&a, NULL);
                if (!b.empty())
                    b.erase_after(b.before_begin()); // STL crashes with empty list
                print_slist(&a);
                print_fwlist(b);
                break;
            }
            foreach (slist_digi, &a, it1)
            {
                if (current == index)
                {
                    if (it1.node->next) // STL crashes with erase at end
                        b.erase_after(iter);
                    slist_digi_erase_after(&a, it1.node);
                    print_slist(&a);
                    print_fwlist(b);
                    break;
                }
                iter++;
                current++;
            }
            CHECK(a, b);
            break;
        }
        case TEST_ERASE_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            if (first_b1 == last_b1)
                break;                
            /*iter = */b.erase_after(first_b1, last_b1);
            slist_digi_erase_range(&range_a1);
            print_slist(&a);
            print_fwlist(b);
            //CHECK_ITER(range_a1, b, iter);
            CHECK(a, b);
            break;
        case TEST_INSERT_AFTER: {
            size_t current = 0;
            iter = b.begin();
            foreach (slist_digi, &a, it1)
            {
                if (current == index)
                {
                    LOG("insert_after %zu: %d\n", index, value);
                    print_slist(&a);
                    slist_digi_insert_after(&it1, digi_init(value));
                    b.insert_after(iter, DIGI{value});
                    break;
                }
                iter++;
                current++;
            }
            print_slist(&a);
            print_fwlist(b);
            CHECK(a, b);
            break;
        }
        case TEST_CLEAR: {
            slist_digi_clear(&a);
            b.clear();
            CHECK(a, b);
            break;
        }
#ifdef DEBUG
        case TEST_ASSIGN:
            if (index > 2)
            {
                slist_digi_assign(&a, index, digi_init(value));
                b.assign(index, DIGI{value});
            }
            CHECK(a, b);
            break;
        //case TEST_ASSIGN_GENERIC: { // ie from vector
        // }
#endif // DEBUG
        case TEST_SWAP:
            aa = slist_digi_copy(&a);
            aaa = slist_digi_init();
            bb = b;
            slist_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb)
            slist_digi_free(&aaa);
            CHECK(a, b);
            break;
        case TEST_COPY:
            aa = slist_digi_copy(&a);
            bb = b;
            CHECK(aa, bb);
            slist_digi_free(&aa);
            CHECK(a, b);
            break;
        case TEST_REVERSE:
            print_slist(&a);
            slist_digi_reverse(&a);
            b.reverse();
            print_slist(&a);
            print_fwlist(b);
            CHECK(a, b);
            break;
        case TEST_REMOVE:
            if (a.head)
            {
                LOG("remove %d from ", value);
                print_slist(&a);
                num_a = slist_digi_remove(&a, digi_init(value));
#if __cpp_lib_erase_if >= 202002L
                num_b = b.remove(DIGI{value});
                LOG("=> %zu vs %zu\n", num_a, num_b);
                assert(num_a == num_b);
#else
                b.remove(DIGI{value});
                LOG("=> %zu vs %zu\n", num_a, num_b);
#endif
                print_slist(&a);
                print_fwlist(b);
            }
            CHECK(a, b);
            break;
        case TEST_REMOVE_IF:
            if (a.head)
            {
                print_slist(&a);
                slist_digi_remove_if(&a, digi_is_odd);
                b.remove_if(DIGI_is_odd);
                print_slist(&a);
                print_fwlist(b);
            }
            CHECK(a, b);
            break;
        case TEST_EQUAL:
            aa = slist_digi_copy(&a);
            bb = b;
            if (TEST_RAND(2) == 1)
            {
                value = TEST_RAND(TEST_MAX_VALUE);
                LOG("push %d\n", value);
                slist_digi_push_front(&aa, digi_init(value));
                bb.push_front(DIGI{value});
            }
            print_slist(&a);
            print_slist(&aa);
            found_a = slist_digi_equal(&a, &aa);
            print_fwlist(b);
            print_fwlist(bb);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            found_b = std::equal(b.begin(), b.end(), bb.begin(), bb.end());
#else
            found_b = std::equal(b.begin(), b.end(), bb.begin());
#endif
            LOG("found_a: %d found_b: %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            slist_digi_free(&aa);
            CHECK(a, b);
            break;
#ifdef DEBUG
        case TEST_SPLICE_AFTER: {
            size_t current = 0;
            iter = b.begin();
            it = slist_digi_begin(&a);
            while (!slist_digi_it_done(&it))
            {
                if (current == index)
                    break;
                iter++;
                current += 1;
                slist_digi_it_next(&it);
            }
            setup_lists(&aa, bb, size, NULL);
            slist_digi_splice_after(&a, it.node, &aa);
            b.splice_after(iter, bb);
            CHECK(a, b);
            break;
        }
#endif
        case TEST_MERGE:
            aa = slist_digi_init_from(&a);
            setup_lists(&aa, bb, size, NULL);
            slist_digi_sort(&a);
            b.sort();
            slist_digi_sort(&aa);
            bb.sort();

            print_slist(&a);
            print_slist(&aa);
            slist_digi_merge(&a, &aa);
            print_slist(&a);
            b.merge(bb);
            CHECK(a, b);
            break;
        case TEST_MERGE_UNSORTED: {
            aa = slist_digi_init_from(&a);
            int total = 0;
            for (size_t pushes = 0; pushes < size; pushes++)
            {
                value = TEST_RAND(128);
                total += value;
                if (pushes == (size - 1))
                    total = max_value + 1; // MAX + 1 ENSURES MERGE CAN APPEND TO TAIL.
                slist_digi_push_front(&aa, digi_init(total));
                bb.push_front(DIGI{total});
            }
            print_slist(&a);
            print_slist(&aa);
            slist_digi_merge(&a, &aa);
            print_slist(&a);
            b.merge(bb);
            CHECK(a, b);
            break;
        }
        case TEST_SORT:
            slist_digi_sort(&a);
            b.sort();
            CHECK(a, b);
            break;
        case TEST_UNIQUE:
            slist_digi_unique(&a);
            b.unique();
            CHECK(a, b);
            break;
        case TEST_FIND:
            if (size > 0)
            {
                int test_value = 0;
                size_t current = 0;
                foreach (slist_digi, &a, it1)
                {
                    if (current == index)
                    {
                        test_value = *it1.ref->value;
                        break;
                    }
                    current += 1;
                }
                value = TEST_RAND(2) ? value : test_value;
                digi key = digi_init(value);
                it = slist_digi_find(&a, key);
                iter = std::find(b.begin(), b.end(), DIGI{value});
                found_a = !slist_digi_it_done(&it);
                found_b = iter != b.end();
                assert(found_a == found_b);
                if (found_a && found_b)
                    assert(*it.ref->value == *iter->value);
                digi_free(&key);
                CHECK(a, b);
            }
            break;
        case TEST_ALL_OF:
            found_a = slist_digi_all_of(&a, digi_is_odd);
            found_b = all_of(b.begin(), b.end(), DIGI_is_odd);
            if (found_a != found_b)
            {
                print_slist(&a);
                print_fwlist(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        case TEST_ANY_OF:
            found_a = slist_digi_any_of(&a, digi_is_odd);
            found_b = any_of(b.begin(), b.end(), DIGI_is_odd);
            if (found_a != found_b)
            {
                print_slist(&a);
                print_fwlist(b);
                printf("%d != %d is_odd FAIL\n", (int)found_a, (int)found_b);
                fail++;
            }
            assert(found_a == found_b);
            break;
        case TEST_NONE_OF:
            found_a = slist_digi_none_of(&a, digi_is_odd);
            found_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
            assert(found_a == found_b);
            break;
#ifdef DEBUG
        case TEST_SORT_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            // FIXME misses the last range elem
            slist_digi_sort_range(&range_a1);
            print_slist(&a);
#if 0
            // yet unsupported by the STL
            std::sort(first_b1, last_b1);
            CHECK(a, b);
#else
            slist_digi_clear(&a);
            b.clear();
#endif
            break;
#endif
        case TEST_FIND_RANGE: {
            value = pick_random(&a);
            digi key = digi_init(value);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            found_a = slist_digi_find_range(&range_a1, key);
            iter = find(first_b1, last_b1, DIGI{value});
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            CHECK_RANGE(range_a1, iter, last_b1);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_ALL_OF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = slist_digi_all_of_range(&range_a1, digi_is_odd);
            found_b = all_of(first_b1, last_b1, DIGI_is_odd);
            if (found_a != found_b)
            {
                print_slist_range(range_a1);
                print_fwlist(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        case TEST_ANY_OF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = slist_digi_any_of_range(&range_a1, digi_is_odd);
            found_b = any_of(first_b1, last_b1, DIGI_is_odd);
            if (found_a != found_b)
            {
                print_slist_range(range_a1);
                print_fwlist(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        case TEST_NONE_OF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            found_a = slist_digi_none_of_range(&range_a1, digi_is_odd);
            found_b = none_of(first_b1, last_b1, DIGI_is_odd);
            if (found_a != found_b)
            {
                print_slist_range(range_a1);
                print_fwlist(b);
                printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
            }
            assert(found_a == found_b);
            break;
        case TEST_FIND_IF:
            it = slist_digi_find_if(&a, digi_is_odd);
            iter = find_if(b.begin(), b.end(), DIGI_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        case TEST_FIND_IF_NOT:
            it = slist_digi_find_if_not(&a, digi_is_odd);
            iter = find_if_not(b.begin(), b.end(), DIGI_is_odd);
            CHECK_ITER(it, b, iter);
            break;
        case TEST_FIND_IF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = slist_digi_find_if_range(&range_a1, digi_is_odd);
            iter = find_if(first_b1, last_b1, DIGI_is_odd);
            print_slist_range(range_a1);
            print_fwlist(b);
            CHECK_RANGE(it, iter, last_b1);
            break;
        case TEST_FIND_IF_NOT_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            it = slist_digi_find_if_not_range(&range_a1, digi_is_odd);
            iter = find_if_not(first_b1, last_b1, DIGI_is_odd);
            print_slist_range(range_a1);
            CHECK_RANGE(it, iter, last_b1);
            break;
        case TEST_COUNT:
            num_a = slist_digi_count(&a, digi_init(value));
            num_b = count(b.begin(), b.end(), DIGI{value});
            assert(num_a == num_b);
            break;
        case TEST_COUNT_IF:
            num_a = slist_digi_count_if(&a, digi_is_odd);
            num_b = count_if(b.begin(), b.end(), DIGI_is_odd);
            assert(num_a == num_b);
            break;
        case TEST_COUNT_RANGE:
            value = TEST_RAND(2) ? value : 0;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            num_a = slist_digi_count_range(&range_a1, digi_init(value));
            num_b = count(first_b1, last_b1, DIGI{value});
            print_slist_range(range_a1);
            assert(num_a == num_b);
            break;
        case TEST_COUNT_IF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            num_a = slist_digi_count_if_range(&range_a1, digi_is_odd);
            num_b = count_if(first_b1, last_b1, DIGI_is_odd);
            if (num_a != num_b)
            {
                print_slist_range(range_a1);
                print_fwlist(b);
                printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                fail++;
            }
            assert(num_a == num_b);
            break;
        case TEST_GENERATE:
            digi_generate_reset();
            slist_digi_generate(&a, digi_generate);
            digi_generate_reset();
            std::generate(b.begin(), b.end(), DIGI_generate);
            CHECK(a, b);
            break;
        case TEST_GENERATE_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            digi_generate_reset();
            slist_digi_generate_range(&range_a1, digi_generate);
            digi_generate_reset();
            std::generate(first_b1, last_b1, DIGI_generate);
            print_slist_range(range_a1);
            CHECK(a, b);
            break;
#ifdef DEBUG
        // algorithms + ranges
        case TEST_INSERT_RANGE: {
            size_t size2 = TEST_RAND(TEST_MAX_SIZE);
            aa = slist_digi_init_from(&a);
            for (size_t pushes = 0; pushes < size2; pushes++)
            {
                const int v = TEST_RAND(TEST_MAX_VALUE);
                slist_digi_push_front(&aa, digi_init(v));
                bb.push_front(DIGI{v});
            }
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            it = slist_digi_begin(&a);
            slist_digi_it_advance(&it, index);
            iter = b.begin();
            advance(iter, index);
            b.insert_after(iter, first_b2, last_b2);
            print_slist_range(it);
            print_slist_range(range_a2);
            slist_digi_insert_range(&it, &range_a2);
            print_slist(&a);
            print_fwlist(b);
            CHECK(a, b);
            slist_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM: {
            aa = slist_digi_transform(&a, digi_untrans);
            //bb.resize(b.size());
            std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
            CHECK(aa, bb);
            CHECK(a, b);
            slist_digi_free(&aa);
            break;
        }
#endif // DEBUG
        case TEST_COPY_IF:
            aa = slist_digi_copy_if(&a, digi_is_odd);
#if __cplusplus >= 201103L && !defined(_MSC_VER)
            std::copy_if(b.begin(), b.end(), std::front_inserter(bb), DIGI_is_odd);
#else
            for (auto &d : b)
            {
                if (DIGI_is_odd(d))
                    bb.push_back(d);
            }
#endif
            CHECK(aa, bb);
            slist_digi_free(&aa);
            CHECK(a, b);
            break;
        case TEST_COPY_IF_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = slist_digi_copy_if_range(&range_a1, digi_is_odd);
#if __cplusplus >= 201103L && !defined(_MSC_VER)
            std::copy_if(first_b1, last_b1, std::front_inserter(bb), DIGI_is_odd);
#else
            for (auto d = first_b1; d != last_b1; d++)
            {
                if (DIGI_is_odd(*d))
                    bb.push_back(*d);
            }
#endif
            print_slist_range(range_a1);
            CHECK(aa, bb);
            slist_digi_free(&aa);
            CHECK(a, b);
            break;
        case TEST_INCLUDES:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            found_a = slist_digi_includes(&a, &aa);
            found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
            assert(found_a == found_b);
            print_fwlist(b);
            print_fwlist(bb);
            CHECK(aa, bb);
            slist_digi_free(&aa);
            break;
        case TEST_INCLUDES_RANGE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a includes aa\n");
            print_slist_range(range_a1);
            print_slist_range(range_a2);
            found_a = slist_digi_includes_range(&range_a1, &range_a2);
            LOG("STL b - bb\n");
            print_fwlist(b);
            print_fwlist(bb);
            found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
            assert(found_a == found_b);
            CHECK(aa, bb);
            slist_digi_free(&aa);
            break;
#ifdef DEBUG
        case TEST_UNION: // 48
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            aaa = slist_digi_union(&a, &aa);
#ifndef _MSC_VER
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));
            print_fwlist(b);
            print_fwlist(bb);
            print_fwlist(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
        case TEST_INTERSECTION:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            aaa = slist_digi_intersection(&a, &aa);
#ifndef _MSC_VER
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
        case TEST_SYMMETRIC_DIFFERENCE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            aaa = slist_digi_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
        case TEST_DIFFERENCE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            print_slist(&a);
            aaa = slist_digi_difference(&a, &aa);
#ifndef _MSC_VER
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));
            CHECK(aaa, bbb);
#endif
            CHECK(aa, bb);
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
        case TEST_UNION_RANGE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_slist_range(range_a1);
            print_slist_range(range_a2);
            aaa = slist_digi_union_range(&range_a1, &range_a2);
            LOG("CTL => aaa\n");
            print_slist(&aaa);

            LOG("STL b + bb\n");
            print_fwlist(b);
            print_fwlist(bb);
#ifndef _MSC_VER
            std::set_union(first_b1, last_b1, first_b2, last_b2, std::front_inserter(bbb));
            LOG("STL => bbb\n");
            print_fwlist(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
#endif // DEBUG
        case TEST_INTERSECTION_RANGE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_slist_range(range_a1);
            print_slist_range(range_a2);
            aaa = slist_digi_intersection_range(&range_a1, &range_a2);
            LOG("CTL => aaa\n");
            print_slist(&aaa);

            LOG("STL b + bb\n");
            print_fwlist(b);
            print_fwlist(bb);
#ifndef _MSC_VER
            std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::front_inserter(bbb));
            LOG("STL => bbb\n");
            print_fwlist(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
#ifdef DEBUG
        case TEST_DIFFERENCE_RANGE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_slist_range(range_a1);
            print_slist_range(range_a2);
            aaa = slist_digi_difference_range(&range_a1, &range_a2);
            LOG("CTL => aaa\n");
            print_slist(&aaa);
            LOG("STL b + bb\n");
            print_fwlist(b);
            print_fwlist(bb);
#ifndef _MSC_VER
            std::set_difference(first_b1, last_b1, first_b2, last_b2, std::front_inserter(bbb));
            LOG("STL => bbb\n");
            print_fwlist(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
        case TEST_SYMMETRIC_DIFFERENCE_RANGE:
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            slist_digi_sort(&a);
            slist_digi_sort(&aa);
            b.sort();
            bb.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_slist_range(range_a1);
            print_slist_range(range_a2);
            aaa = slist_digi_symmetric_difference_range(&range_a1, &range_a2);
            LOG("CTL => aaa\n");
            print_slist(&aaa);
            LOG("STL b + bb\n");
            print_fwlist(b);
            print_fwlist(bb);
#ifndef _MSC_VER
            std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::front_inserter(bbb));
            LOG("STL => bbb\n");
            print_fwlist(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            slist_digi_free(&aaa);
            slist_digi_free(&aa);
            break;
#endif
        case TEST_EQUAL_VALUE:
            //size_t size1 = MIN(TEST_RAND(size), 5);
            //slist_digi_resize(&a, size1, digi_init(0));
            //b.resize(size1);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = size ? *a.head->value.value : 0;
            LOG("equal_value %d\n", value);
            print_slist_range(range_a1);
            found_a = slist_digi_equal_value(&range_a1, digi_init(value));
            found_b = first_b1 != last_b1;
            while (first_b1 != last_b1 && first_b1 != b.end())
            {
                if (value != *first_b1->value)
                {
                    found_b = false;
                    break;
                }
                first_b1++;
            }
            LOG("found_a: %d found_b: %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        case TEST_EQUAL_RANGE:
            aa = slist_digi_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = slist_digi_equal_range(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            found_b = std::equal(first_b1, last_b1, first_b2, last_b2);
            LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
#else
            found_b = std::equal(first_b1, last_b1, first_b2);
            LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
            if (found_a != found_b)
                printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
            slist_digi_free(&aa);
            break;
        case TEST_IOTA: {
            digi key = digi_init(0);
            slist_digi_iota(&a, key);
            print_slist(&a);
            std::iota(b.begin(), b.end(), DIGI{0});
            print_fwlist(b);
            CHECK(a, b);
            digi_free(&key);
            break;
        }
        case TEST_IOTA_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            digi key = digi_init(0);
            slist_digi_iota_range(&range_a1, key);
            print_slist_range(range_a1);
            std::iota(first_b1, last_b1, DIGI{0});
            print_fwlist(b);
            CHECK(a, b);
            digi_free(&key);
            break;
        }
#ifdef DEBUG
        case TEST_GENERATE_N: // TEST=63
        {
            size_t count = TEST_RAND(20);
#ifndef _MSC_VER
            digi_generate_reset();
            slist_digi_generate_n(&a, count, digi_generate);
            digi_generate_reset();
            /*
            std::generate_n(b.begin(), count, DIGI_generate);
            */
            // FIXME The STL is arguably broken here. Or we should use a
            // different generate_n.
            int n = MIN(count, size);
            auto end = b.begin();
            std::advance(end, n);
            b.erase_after(b.begin(), end);
            std::generate_n(std::front_inserter(b), n, DIGI_generate);
            print_fwlist(b);
            CHECK(a, b);
#endif
            break;
        }
        case TEST_GENERATE_N_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t off = std::distance(b.begin(), first_b1);
            size_t len = std::distance(first_b1, last_b1);
            size_t count = TEST_RAND(20 - off);
            LOG("generate_n_range %zu\n", count);
#ifndef _MSC_VER
            digi_generate_reset();
            slist_digi_generate_n_range(&range_a1, count, digi_generate);
            print_slist(&a);
            digi_generate_reset();
            int n = MIN(MIN(count, size), len);
            last_b1 = first_b1;
            std::advance(last_b1, n);
            b.erase_after(first_b1, last_b1);
            first_b1 = b.begin();
            std::advance(first_b1, off);
            std::generate_n(std::front_inserter(b), n, DIGI_generate);
            print_fwlist(b);
            CHECK(a, b);
#endif
            break;
        }
        case TEST_TRANSFORM_IT: {
            it = slist_digi_begin(&a);
            slist_digi_it_advance(&it, 1);
            // aa = slist_digi_transform_it(&a, &it, digi_bintrans);
            // bb.resize(b.size());
            std::transform(b.begin(), b.end(), ++b.begin(), bb.begin(), DIGI_bintrans);
            CHECK(aa, bb);
            CHECK(a, b);
            slist_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            aa = slist_digi_init();
            //size_t dist = std::distance(first_b1, last_b1);
            //slist_digi_resize(&aa, dist, digi_init(0));
            range_a2 = slist_digi_begin(&aa);
            it = slist_digi_transform_range(&range_a1, range_a2, digi_untrans);
            //bb.resize(dist);
            iter = std::transform(first_b1, last_b1, b.begin()++, bb.begin(), DIGI_bintrans);
            CHECK_RANGE(it, iter, last_b1);
            CHECK(aa, bb);
            // heap use-after-free
            CHECK(a, b);
            slist_digi_free(&aa);
            break;
        }
#endif // DEBUG
        case TEST_MISMATCH: {
            if (size < 2)
                break;
            setup_lists(&aa, bb, 1 + TEST_RAND(size-1), NULL);
            slist_digi_it b1, b2;
            b1 = slist_digi_begin(&a);
            b2 = slist_digi_begin(&aa);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            // STL crashes with empty 2nd range
            if (std::distance(first_b2, last_b2) == 0)
            {
                if (last_b2 == bb.end())
                    break;
                last_b2++;
                slist_digi_it_advance_end(&range_a2, 1);
            }
            /*found_a = */ slist_digi_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
            if (!size || !distance(first_b2, last_b2))
            {
                printf("skip std::mismatch with empty 2nd range. use C++14\n");
                slist_digi_free(&aa);
                break;
            }
            auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
            int d1a = slist_digi_it_distance(&b1, &range_a1);
            int d2a = slist_digi_it_distance(&b2, &range_a2);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == distance(b.begin(), pair.first));
            assert(d2a == distance(bb.begin(), pair.second));
            slist_digi_free(&aa);
            break;
        }
#ifdef DEBUG            
        // fails with iter 0 ..
        case TEST_SEARCH: // 33
        {
            print_slist(&a);
            print_fwlist(b);
            aa = slist_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (size && TEST_RAND(2))
            { // 50% unsuccessful
                if (range_a2.node)
                {
                    digi_free(range_a2.ref);
                    range_a2.node->value = digi_init(0);
                    iter = first_b2;
                    iter++;
                    *iter = DIGI{0};
                }
            }
            print_slist_range(range_a2);
            it = slist_digi_search(&a, &range_a2);
            iter = search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", slist_digi_it_done(&it) ? "no" : "yes");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            CHECK_RANGE(it, iter, b.end());
            slist_digi_free(&aa);
            break;
        }
#endif // DEBUG
        case TEST_SEARCH_RANGE: {
            aa = slist_digi_copy(&a);
            bb = b;
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            if (size && TEST_RAND(2))
            {   // 50% unsuccessful
                if (range_a2.node)
                {
                    digi_free(range_a2.ref);
                    range_a2.node->value = digi_init(0);
                    *first_b2 = DIGI{0};
                }
            }
            print_slist_range(range_a2);
            range_a1 = slist_digi_begin(&a);
            found_a = slist_digi_search_range(&range_a1, &range_a2);
            iter = search(b.begin(), b.end(), first_b2, last_b2);
            LOG("found a: %s\n", found_a ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(found_a == !slist_digi_it_done(&range_a1));
            CHECK_RANGE(range_a1, iter, b.end());
            slist_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_slist(&a);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            it = slist_digi_search_n(&a, count, digi_init(value));
            iter = search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(it, b, iter);
            LOG("found %s at %zu\n", slist_digi_it_done(&it) ? "no" : "yes", slist_digi_it_index(&it));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            size_t count = TEST_RAND(4);
            value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            print_slist_range(range_a1);
            pos = slist_digi_search_n_range(&range_a1, count, digi_init(value));
            iter = search_n(first_b1, last_b1, count, DIGI{value});
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s at %zu\n", slist_digi_it_done(pos) ? "no" : "yes", slist_digi_it_index(pos));
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_slist(&a);
            it = slist_digi_adjacent_find(&a);
            iter = adjacent_find(b.begin(), b.end());
            CHECK_ITER(it, b, iter);
            LOG("found %s\n", slist_digi_it_done(&it) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            pos = slist_digi_adjacent_find_range(&range_a1);
            iter = adjacent_find(first_b1, last_b1);
            CHECK_RANGE(*pos, iter, last_b1);
            LOG("found %s\n", slist_digi_it_done(pos) ? "no" : "yes");
            break;
        }
        case TEST_FIND_FIRST_OF: {
            size_t size2 = TEST_RAND(5);
            setup_lists(&aa, bb, size2, NULL);
            last_b2 = bb.end();
            range_a2 = slist_digi_begin(&aa);
            //if (slist_digi_it_index(&range_a2) + 5 < size2)
            //{
            //    slist_digi_it_advance_end(&range_a2, 5);
            //    last_b2 = bb.begin();
            //    std::advance(last_b2, 5);
            //}
            print_slist(&a);
            LOG("last_b2: %ld\n", std::distance(bb.begin(), last_b2));
            print_slist(&aa);
            it = slist_digi_find_first_of(&a, &range_a2);
            iter = std::find_first_of(b.begin(), b.end(), bb.begin(), last_b2);
            LOG("=> %s/%s, %ld/%ld: %d/%d\n", !slist_digi_it_done(&it) ? "yes" : "no",
                iter != b.end() ? "yes" : "no", slist_digi_it_index(&it),
                distance(b.begin(), iter), !slist_digi_it_done(&it) ? *it.ref->value : -1,
                iter != b.end() ? *iter->value : -1);
            CHECK_RANGE(it, iter, b.end());
            slist_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            setup_lists(&aa, bb, TEST_RAND(5), NULL);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist(&a);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            print_slist(&aa);

            found_a = slist_digi_find_first_of_range(&range_a1, &range_a2);
            iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", iter != last_b1 ? "yes" : "no",
                slist_digi_it_index(&range_a1), distance(b.begin(), iter));
            if (found_a)
                assert(iter != last_b1);
            else
                assert(iter == last_b1);
            // CHECK_RANGE(range_a1, iter, last_b1);
            slist_digi_free(&aa);
            break;
        }
        case TEST_FIND_END:
            setup_lists(&aa, bb, TEST_RAND(4), NULL);
            print_slist(&aa);
            range_a2 = slist_digi_begin(&aa);
            it = slist_digi_find_end(&a, &range_a2);
            iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.end());
            found_a = !slist_digi_it_done(&it);
            found_b = iter != b.end();
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
            slist_digi_free(&aa);
            break;
        case TEST_FIND_END_RANGE:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            setup_lists(&aa, bb, TEST_RAND(4), NULL);
            print_slist(&aa);
            range_a2 = slist_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
            range_a1 = slist_digi_find_end_range(&range_a1, &range_a2);
            iter = std::find_end(first_b1, last_b1, bb.begin(), bb.end());
            CHECK_RANGE(range_a1, iter, last_b1);
#endif
            slist_digi_free(&aa);
            break;
#ifdef DEBUG
        case TEST_UNIQUE_RANGE: {
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            it = slist_digi_unique_range(&range_a1);
            found_a = !slist_digi_it_done(&it);
            index = slist_digi_it_index(&it);
            iter = unique(first_b1, last_b1);
            found_b = iter != last_b1;
            long dist = std::distance(b.begin(), iter);
            if (found_b)
                b.erase_after(iter, last_b1);
            print_slist_range(range_a1);
            print_fwlist(b);
            LOG("found %s at %zu, ", found_a ? "yes" : "no", index);
            LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
            assert(found_a == found_b);
            assert((long)index == dist); // FIXME
            break;
        }
#endif // DEBUG
        case TEST_LOWER_BOUND: // 73
            slist_digi_sort(&a);
            b.sort();
            value = pick_random(&a);
            it = slist_digi_lower_bound(&a, digi_init(value));
            iter = lower_bound(b.begin(), b.end(), DIGI{value});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        case TEST_UPPER_BOUND:
            slist_digi_sort(&a);
            b.sort();
            value = pick_random(&a);
            it = slist_digi_upper_bound(&a, digi_init(value));
            iter = upper_bound(b.begin(), b.end(), DIGI{value});
            if (iter != b.end())
            {
                LOG("%d: %d vs %d\n", value, *it.ref->value, *iter->value);
            }
            CHECK_ITER(it, b, iter);
            break;
        case TEST_LOWER_BOUND_RANGE:
            slist_digi_sort(&a);
            b.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = slist_digi_lower_bound_range(&range_a1, digi_init(value));
            iter = lower_bound(first_b1, last_b1, DIGI{value});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        case TEST_UPPER_BOUND_RANGE:
            slist_digi_sort(&a);
            b.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            pos = slist_digi_upper_bound_range(&range_a1, digi_init(value));
            iter = upper_bound(first_b1, last_b1, DIGI{value});
            if (iter != last_b1)
            {
                LOG("%d: %d vs %d\n", value, *pos->ref->value, *iter->value);
            }
            CHECK_RANGE(*pos, iter, last_b1);
            break;
        case TEST_BINARY_SEARCH:
            slist_digi_sort(&a);
            b.sort();
            value = pick_random(&a);
            found_a = slist_digi_binary_search(&a, digi_init(value));
            found_b = binary_search(b.begin(), b.end(), DIGI{value});
            LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        case TEST_BINARY_SEARCH_RANGE:
            slist_digi_sort(&a);
            b.sort();
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            value = pick_random(&a);
            found_a = slist_digi_binary_search_range(&range_a1, digi_init(value));
            found_b = binary_search(first_b1, last_b1, DIGI{value});
            LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        case TEST_LEXICOGRAPHICAL_COMPARE:
            aa = slist_digi_copy(&a);
            bb = b;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
            found_a = slist_digi_lexicographical_compare(&range_a1, &range_a2);
            found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
            LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            slist_digi_free(&aa);
            break;
        case TEST_IS_SORTED:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            found_a = slist_digi_is_sorted(&range_a1);
            found_b = std::is_sorted(first_b1, last_b1);
            LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        case TEST_IS_SORTED_UNTIL:
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            range_a2 = range_a1;
            range_a2.node = range_a1.end;
            pos = slist_digi_is_sorted_until(&range_a1, &range_a2);
            first_b1 = std::is_sorted_until(first_b1, last_b1);
            LOG("=> %s/%s, %ld/%ld: %d/%d\n", !slist_digi_it_done(pos) ? "yes" : "no",
                first_b1 != last_b1 ? "yes" : "no", slist_digi_it_index(pos), distance(b.begin(), first_b1),
                !slist_digi_it_done(pos) ? *pos->ref->value : -1, first_b1 != last_b1 ? *first_b1->value : -1);
            CHECK_RANGE(*pos, first_b1, last_b1);
            break;
#ifdef DEBUG
        case TEST_REVERSE_RANGE: {
            aa = slist_digi_copy(&a);
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            print_slist_range(range_a1);
            slist_digi_reverse_range(&range_a1);
            print_slist(&a);
#if 0
            // STL limitation:
            b.reverse(first_b1, last_b1); // __reverse missing
#else
            for(int i = 0; i < std::distance(first_b1, last_b1) / 2; i++)
            {
                auto f = first_b1; std::advance(f, i);
                auto l = last_b1; std::advance(l, -(i + 1));
                std::iter_swap(f, l);
            }
#endif
            print_fwlist(b);
            //a = slist_digi_copy(&aa);
            break;
        }
#endif // DEBUG

        default:
#ifdef DEBUG
            printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
        CHECK(a, b);
        slist_digi_free(&a);
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
