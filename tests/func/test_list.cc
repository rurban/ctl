#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/list.h>

#include <algorithm>
#include <list>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH_BACK)                                                                                                    \
    TEST(PUSH_FRONT)                                                                                                   \
    TEST(POP_BACK)                                                                                                     \
    TEST(POP_FRONT)                                                                                                    \
    TEST(ERASE)                                                                                                        \
    TEST(INSERT) /* 5 */                                                                                               \
    TEST(CLEAR)                                                                                                        \
    TEST(RESIZE)                                                                                                       \
    TEST(ASSIGN)                                                                                                       \
    TEST(SWAP)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(REVERSE)                                                                                                      \
    TEST(REMOVE)                                                                                                       \
    TEST(EMPLACE)                                                                                                      \
    TEST(EMPLACE_FRONT)                                                                                                \
    TEST(EMPLACE_BACK) /* 15 */                                                                                        \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(ERASE_IF)                                                                                                     \
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(SPLICE)                                                                                                       \
    TEST(SPLICE_IT)                                                                                                    \
    TEST(SPLICE_RANGE)                                                                                                 \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(EQUAL)                                                                                                        \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(SORT)                                                                                                         \
    TEST(UNIQUE)                                                                                                       \
    TEST(FIND)                                                                                                         \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(INSERT_COUNT) /* 41 */                                                                                        \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(ERASE_RANGE)                                                                                                  \
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(UNION)                                                                                                        \
    TEST(INTERSECTION)                                                                                                 \
    TEST(DIFFERENCE)                                                                                                   \
    TEST(SYMMETRIC_DIFFERENCE)                                                                                         \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(DIFFERENCE_RANGE)                                                                                             \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(GENERATE)                                                                                                     \
    TEST(GENERATE_RANGE)                                                                                               \
    TEST(GENERATE_N)                                                                                                   \
    TEST(TRANSFORM)                                                                                                    \
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
    TEST(UNIQUE_RANGE)                                                                                                 \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(ERASE_GENERIC)                                                                                                \
    TEST(GENERATE_N_RANGE) /* 70 */                                                                                    \
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(TRANSFORM_RANGE)

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


void print_lst(list_digi *a)
{
    int i = 0;
    if (a->size)
        list_foreach_ref(list_digi, a, it) printf("%d: %d\n", i++, *it.ref->value);
    printf("====\n");
}

void print_list(std::list<DIGI> &b)
{
    int i = 0;
    if (b.size())
        for (auto &d : b)
            printf("%d: %d\n", i++, *d.value);
    printf("----\n");
}

#define print_lst_range(x)
#ifdef DEBUG
#define TEST_MAX_VALUE 15
#ifndef LONG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 10
#endif
#else
#define print_lst(x)
#define print_list(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int middle(list_digi *a)
{
    if (!a->size)
        return 0;
    return (*list_digi_front(a)->value - *list_digi_back(a)->value) / 2;
}

int median(list_digi *a)
{
    list_digi_it it = list_digi_begin(a);
    list_digi_it_advance(&it, a->size / 2);
    return a->size ? *it.ref->value : 0;
}

int random_element(list_digi *a)
{
    const size_t index = TEST_RAND(a->size);
    list_digi_it it = list_digi_begin(a);
    list_digi_it_advance(&it, index);
    return a->size ? *it.ref->value : 0;
}

int pick_random(list_digi *a)
{
    switch (TEST_RAND(4))
    {
    case 0:
        return middle(a);
    case 1:
        return median(a);
    case 2:
        return random_element(a);
    case 3:
        return TEST_RAND(TEST_MAX_VALUE);
    }
    assert(0);
}

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        assert(list_digi_empty(&_x) == _y.empty());                                                                    \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            assert(*_y.front().value == *list_digi_front(&_x)->value);                                                 \
            assert(*_y.back().value == *list_digi_back(&_x)->value);                                                   \
        }                                                                                                              \
        std::list<DIGI>::iterator _iter = _y.begin();                                                                  \
        int i = 0;                                                                                                     \
        list_foreach_ref(list_digi, &_x, _it)                                                                          \
        {                                                                                                              \
            LOG("%d: %d, ", i, *_it.ref->value);                                                                       \
            assert(*_it.ref->value == *_iter->value);                                                                  \
            i++;                                                                                                       \
            _iter++;                                                                                                   \
        }                                                                                                              \
        LOG("\n");                                                                                                     \
        list_digi_it _it = list_digi_begin(&_x);                                                                       \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_it.ref->value == *_d.value);                                                                      \
            list_digi_it_next(&_it);                                                                                   \
        }                                                                                                              \
    }

#define LOG_ITER(_it, b, _iter, line)                                                                                  \
    if ((_it)->node != NULL)                                                                                           \
    {                                                                                                                  \
        if (_iter == b.end())                                                                                          \
            printf("STL iter at end, line %u FAIL\n", line);                                                           \
        if (*((_it)->ref->value) != *(*_iter).value)                                                                   \
            printf("iter %d vs %d, line %u FAIL\n", *((_it)->ref->value), *(*_iter).value, line);                      \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if (!list_digi_it_done(&_it))                                                                                      \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!list_digi_it_done(&_it))                                                                                      \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref->value == *(*_iter).value);                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

static void setup_lists(list_digi *a, std::list<DIGI> &b, size_t size, int *max_value)
{
    *a = list_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for (size_t pushes = 0; pushes < size; pushes++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE - 1); // SEE COMMENT IN CASE MERGE.
        if (max_value && value > *max_value)
            *max_value = value;
        list_digi_push_back(a, digi_init(value));
        b.push_back(DIGI{value});
    }
}

// list_digi_it* first_a;
// _List_iterator<DIGI>* first_b, *last_b;
static void get_random_iters(list_digi *a, list_digi_it *first_a, std::list<DIGI> &b,
                             std::list<DIGI>::iterator &first_b, std::list<DIGI>::iterator &last_b)
{
    list_digi_it last_a;
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        list_digi_it it1 = list_digi_begin(a);
        list_digi_it_advance(&it1, r1);
        first_b = b.begin();
        for (size_t i = 0; i < r1; i++)
        {
            first_b++;
        }
        *first_a = it1;
        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
            first_a->end = last_a.node;
        }
        else if (r2 == a->size)
        {
            last_a = list_digi_end(a);
            last_b = b.end();
        }
        else
        {
            list_digi_it it2 = list_digi_begin(a);
            list_digi_it_advance(&it2, r2);
            last_b = b.begin();
            for (size_t i = 0; i < r2; i++)
                last_b++;
            last_a = it2;
        }
    }
    else
    {
        list_digi_it end = list_digi_end(a);
        *first_a = end;
        last_a = end;
        last_a.end = first_a->node;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.node;
}

int main(void)
{
    int errors = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for (size_t loop = 0; loop < loops; loop++)
    {
        list_digi a;
        std::list<DIGI> b;
        int max_value = 0;
        const size_t size = TEST_RAND(TEST_MAX_SIZE);
        setup_lists(&a, b, size, &max_value);
        int which;
        if (tests.size)
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
        } else
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
        LOG("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
        switch (which)
        {
        case TEST_PUSH_FRONT: {
            int value = TEST_RAND(TEST_MAX_VALUE);
            list_digi_push_front(&a, digi_init(value));
            b.push_front(DIGI{value});
            CHECK(a, b);
            break;
        }
        case TEST_PUSH_BACK: {
            int value = TEST_RAND(TEST_MAX_VALUE);
            list_digi_push_back(&a, digi_init(value));
            b.push_back(DIGI{value});
            CHECK(a, b);
            break;
        }
        case TEST_POP_FRONT: {
            if (a.size > 0)
            {
                list_digi_pop_front(&a);
                b.pop_front();
            }
            CHECK(a, b);
            break;
        }
        case TEST_POP_BACK: {
            if (a.size > 0)
            {
                list_digi_pop_back(&a);
                b.pop_back();
            }
            CHECK(a, b);
            break;
        }
        case TEST_ERASE: {
            if (a.size > 0) // we survive, but STL segfaults
            {
                size_t index = TEST_RAND(a.size);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance(&it, index);
                LOG("erase %zu\n", index);
                list_digi_erase(&it);
                b.erase(iter);
                CHECK(a, b);
            }
            break;
        }
        case TEST_INSERT: {
            size_t index = TEST_RAND(a.size);
            int value = TEST_RAND(TEST_MAX_VALUE);
            std::list<DIGI>::iterator iter = b.begin();
            std::advance(iter, index);
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, index);
            list_digi_it *aa = list_digi_insert(&it, digi_init(value));
            std::list<DIGI>::iterator bb = b.insert(iter, DIGI{value});
            // insert libstc++ seems to violate the specs, as insert_count
            // LOG("inserted %d at %zu\n", value, index);
            // print_lst(&a);
            // print_list(b);
            CHECK_ITER(*aa, b, bb);
            CHECK(a, b);
            break;
        }
        case TEST_CLEAR: {
            list_digi_clear(&a);
            b.clear();
            CHECK(a, b);
            break;
        }
        case TEST_RESIZE: {
            size_t resize = 2 * TEST_RAND(TEST_MAX_SIZE);
            list_digi_resize(&a, resize, digi_init(0));
            b.resize(resize);
            print_lst(&a);
            print_list(b);
            CHECK(a, b);
            break;
        }
        case TEST_ASSIGN: {
            size_t width = TEST_RAND(a.size);
            if (width > 2)
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                list_digi_assign(&a, width, digi_init(value));
                b.assign(width, DIGI{value});
            }
            CHECK(a, b);
            break;
        }
        case TEST_SWAP: {
            list_digi aa = list_digi_copy(&a);
            list_digi aaa = list_digi_init();
            std::list<DIGI> bb = b;
            std::list<DIGI> bbb;
            list_digi_swap(&aaa, &aa);
            std::swap(bb, bbb);
            CHECK(aaa, bbb)
            list_digi_free(&aaa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY: {
            list_digi aa = list_digi_copy(&a);
            std::list<DIGI> bb = b;
            CHECK(aa, bb);
            list_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_REVERSE: {
            list_digi_reverse(&a);
            b.reverse();
            CHECK(a, b);
            break;
        }
        case TEST_REMOVE: {
            digi *value = list_digi_front(&a);
            if (value) // not empty
            {
                int vb = *value->value;
                LOG("before remove %d\n", vb);
                print_lst(&a);
#if __cpp_lib_erase_if >= 202002L
                size_t erased_a = list_digi_remove(&a, digi_init(vb));
                LOG("removed %zu\n", erased_a);
#else
                list_digi_remove(&a, digi_init(vb));
#endif
                print_lst(&a);
#if __cpp_lib_erase_if >= 202002L
                size_t erased_b = b.remove(DIGI{vb});
                assert(erased_a == erased_b);
#else
                b.remove(DIGI{vb});
#endif
                LOG("removed STL\n");
                print_list(b);
                CHECK(a, b);
            }
            break;
        }
        case TEST_EMPLACE: {
            int value = TEST_RAND(TEST_MAX_VALUE);
            digi aa = digi_init(value);
            if (a.size < 2)
            {
                list_digi_resize(&a, 10, digi_init(0));
                b.resize(10);
            }
#ifdef DEBUG
            list_digi_resize(&a, 10, digi_init(0));
            b.resize(10);
            LOG("before emplace\n");
            print_lst(&a);
#endif
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, 1);
            list_digi_emplace(&it, &aa);
            LOG("CTL emplace head->next %d\n", *aa.value);
            // print_lst(&a);
            auto iter = b.begin();
#if __cplusplus >= 201103L
            b.emplace(++iter, DIGI{value});
#else
            b.insert(++iter, DIGI{value});
#endif
            LOG("STL emplace begin++ %d\n", *DIGI{value});
            // print_list(b);
            CHECK(a, b);
            digi_free(&aa);
            break;
        }
        case TEST_EMPLACE_FRONT: {
            int value = TEST_RAND(TEST_MAX_VALUE);
            digi aa = digi_init(value);
            list_digi_emplace_front(&a, &aa);
#if __cplusplus >= 201103L
            b.emplace_front(DIGI{value});
#else
            b.push_front(DIGI{value});
#endif
            CHECK(a, b);
            digi_free(&aa);
            break;
        }
        case TEST_EMPLACE_BACK: {
            int value = TEST_RAND(TEST_MAX_VALUE);
            digi aa = digi_init(value);
            list_digi_emplace_back(&a, &aa);
#if __cplusplus >= 201103L
            b.emplace_back(DIGI{value});
#else
            b.push_back(DIGI{value});
#endif
            CHECK(a, b);
            digi_free(&aa);
            break;
        }
        case TEST_REMOVE_IF: {
            print_lst(&a);
            list_digi_remove_if(&a, digi_is_odd);
            b.remove_if(DIGI_is_odd);
            CHECK(a, b);
            break;
        }
        case TEST_ERASE_IF: {
            print_lst(&a);
#if __cpp_lib_erase_if >= 202002L
            size_t num_a = list_digi_erase_if(&a, digi_is_odd);
            size_t num_b = std::erase_if(b, DIGI_is_odd);
            assert(num_a == num_b);
#else
            list_digi_erase_if(&a, digi_is_odd);
            b.remove_if(DIGI_is_odd);
#endif
            CHECK(a, b);
            break;
        }
        case TEST_SPLICE: {
            size_t index = TEST_RAND(a.size);
            std::list<DIGI>::iterator iter = b.begin();
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, index);
            std::advance(iter, index);
            list_digi aa;
            std::list<DIGI> bb;
            LOG("splice at b[%zu]: bb => result, a\n", index);
            print_list(b);
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            print_list(bb);
            b.splice(iter, bb);
            print_list(b);
            list_digi_splice(&it, &aa);
            print_lst(&a);
            CHECK(a, b);
            break;
        }
        case TEST_MERGE: {
            list_digi aa = list_digi_init_from(&a);
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_merge(&a, &aa);
            b.merge(bb);
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
        case TEST_MERGE_RANGE: {
            list_digi_it range_a1, range_a2;
            std::list<DIGI>::iterator first_b1, last_b1, first_b2, last_b2;
            get_random_iters(&a, &range_a1, b, first_b1, last_b1);
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

            list_digi aaa = list_digi_merge_range(&range_a1, &range_a2);
#if !defined(_MSC_VER)
            std::list<DIGI> bbb;
            merge(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aa);
            list_digi_free(&aaa);
            break;
        }
        case TEST_EQUAL: {
            list_digi aa = list_digi_copy(&a);
            std::list<DIGI> bb = b;
            assert(list_digi_equal(&a, &aa));
            assert(b == bb);
            list_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_SORT: {
            list_digi_sort(&a);
            b.sort();
            CHECK(a, b);
            break;
        }
        case TEST_UNIQUE: {
            list_digi_unique(&a);
            b.unique();
            CHECK(a, b);
            break;
        }
        case TEST_FIND: {
            int value = pick_random(&a);
            digi key = digi_init(value);
            list_digi_it aa = list_digi_find(&a, key);
            auto bb = find(b.begin(), b.end(), DIGI{value});
            CHECK_ITER(aa, b, bb);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_ALL_OF: {
            bool aa = list_digi_all_of(&a, digi_is_odd);
            bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
            if (aa != bb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_ANY_OF: {
            bool aa = list_digi_any_of(&a, digi_is_odd);
            bool bb = any_of(b.begin(), b.end(), DIGI_is_odd);
            if (aa != bb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d is_odd FAIL\n", (int)aa, (int)bb);
                errors++;
            }
            assert(aa == bb);
            break;
        }
        case TEST_NONE_OF: {
            bool is_a = list_digi_none_of(&a, digi_is_odd);
            bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
            assert(is_a == is_b);
            break;
        }
        case TEST_FIND_RANGE: {
            int vb = pick_random(&a);
            digi key = digi_init(vb);
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool found_a = list_digi_find_range(&first_a, key);
            auto it = find(first_b, last_b, vb);
            if (found_a)
                assert(it != last_b);
            else
                assert(it == last_b);
            CHECK_RANGE(first_a, it, last_b);
            digi_free(&key); // special
            CHECK(a, b);
            break;
        }
        case TEST_ALL_OF_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = list_digi_all_of_range(&first_a, digi_is_odd);
            bool bb = all_of(first_b, last_b, DIGI_is_odd);
            if (aa != bb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_ANY_OF_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = list_digi_any_of_range(&first_a, digi_is_odd);
            bool bb = any_of(first_b, last_b, DIGI_is_odd);
            if (aa != bb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_NONE_OF_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            bool aa = list_digi_none_of_range(&first_a, digi_is_odd);
            bool bb = none_of(first_b, last_b, DIGI_is_odd);
            if (aa != bb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d is_odd\n", (int)aa, (int)bb);
            }
            assert(aa == bb);
            break;
        }
        case TEST_FIND_IF: {
            list_digi_it aa = list_digi_find_if(&a, digi_is_odd);
            auto bb = find_if(b.begin(), b.end(), DIGI_is_odd);
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_FIND_IF_NOT: {
            list_digi_it aa = list_digi_find_if_not(&a, digi_is_odd);
            auto bb = find_if_not(b.begin(), b.end(), DIGI_is_odd);
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_FIND_IF_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            list_digi_it aa = list_digi_find_if_range(&first_a, digi_is_odd);
            auto bb = find_if(first_b, last_b, DIGI_is_odd);
            print_lst(&a);
            print_list(b);
            CHECK_RANGE(aa, bb, last_b);
            break;
        }
        case TEST_FIND_IF_NOT_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            list_digi_it aa = list_digi_find_if_not_range(&first_a, digi_is_odd);
            auto bb = find_if_not(first_b, last_b, DIGI_is_odd);
            CHECK_RANGE(aa, bb, last_b);
            break;
        }
        case TEST_INSERT_COUNT: {
            size_t index = TEST_RAND(a.size);
            size_t count = TEST_RAND(10);
            int value = TEST_RAND(TEST_MAX_VALUE);
            std::list<DIGI>::iterator iter = b.begin();
            std::advance(iter, index);
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, index);
            LOG("insert %d (%zux) at %zu\n", value, count, index);
            list_digi_it *aa = list_digi_insert_count(&it, count, digi_init(value));
            // does libstc++ violate its docs?
            std::list<DIGI>::iterator bb = b.insert(iter, count, DIGI{value});
            // print_lst(&a);
            // print_list(b);
            CHECK_ITER(*aa, b, bb);
            CHECK(a, b);
            break;
        }
        case TEST_COUNT: {
            int key = TEST_RAND(TEST_MAX_SIZE);
            int aa = list_digi_count(&a, digi_init(key));
            int bb = count(b.begin(), b.end(), DIGI{key});
            assert(aa == bb);
            break;
        }
        case TEST_COUNT_IF: {
            size_t count_a = list_digi_count_if(&a, digi_is_odd);
            size_t count_b = count_if(b.begin(), b.end(), DIGI_is_odd);
            assert(count_a == count_b);
            break;
        }
        case TEST_COUNT_RANGE: {
            int test_value = 0;
            int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : test_value;
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            // used to fail with 0,0 of 0
            size_t numa = list_digi_count_range(&first_a, digi_init(v));
            size_t numb = count(first_b, last_b, DIGI{v});
            assert(numa == numb);
            break;
        }
        case TEST_COUNT_IF_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t numa = list_digi_count_if_range(&first_a, digi_is_odd);
            size_t numb = count_if(first_b, last_b, DIGI_is_odd);
            if (numa != numb)
            {
                print_lst(&a);
                print_list(b);
                printf("%d != %d FAIL\n", (int)numa, (int)numb);
                errors++;
            }
            assert(numa == numb); // fails. off by one, counts one too much
            break;
        }
        case TEST_SPLICE_IT: {
            size_t index = TEST_RAND(a.size);
            std::list<DIGI>::iterator iter = b.begin();
            std::advance(iter, index);
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, index);
            list_digi aa;
            std::list<DIGI> bb;
            size_t bsize = TEST_RAND(TEST_MAX_SIZE);
            setup_lists(&aa, bb, bsize, NULL);
            // STL crashes with empty lists, CTL not
            if (b.size() && bb.size())
            {
                std::list<DIGI>::iterator bbpos = bb.begin();
                std::advance(bbpos, bsize / 2);
                list_digi_it aapos = list_digi_begin(&aa);
                list_digi_it_advance(&aapos, bsize / 2);
                LOG("splice at b[%zu]: bb[%zu] => result, a\n", index, bsize / 2);
                print_list(b);
                print_list(bb);
                b.splice(iter, bb, bbpos);
                print_list(b);
                list_digi_splice_it(&it, &aapos);
                print_lst(&a);
                CHECK(a, b);
            }
            list_digi_free(&aa);
            break;
        }
        case TEST_SPLICE_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            size_t index = TEST_RAND(a.size);
            std::list<DIGI>::iterator iter = b.begin();
            std::advance(iter, index);
            list_digi_it it = list_digi_begin(&a);
            list_digi_it_advance(&it, index);
            list_digi aa = list_digi_init_from(&a);
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            get_random_iters(&aa, &first_a, bb, first_b, last_b);

            if (b.size() && bb.size())
            {
                b.splice(iter, bb, first_b, last_b);
                list_digi_splice_range(&it, &first_a);
                CHECK(a, b);
            }
            list_digi_free(&aa);
            break;
        }
        // algorithms + ranges
        case TEST_INSERT_RANGE: {
            print_lst(&a);
            size_t size2 = TEST_RAND(TEST_MAX_SIZE);
            list_digi aa = list_digi_init_from(&a);
            std::list<DIGI> bb;
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            for (size_t pushes = 0; pushes < size2; pushes++)
            {
                const int value = TEST_RAND(TEST_MAX_VALUE);
                list_digi_push_back(&aa, digi_init(value));
                bb.push_back(DIGI{value});
            }
            print_lst(&aa);
            get_random_iters(&aa, &first_a, bb, first_b, last_b);
            const size_t index = TEST_RAND(a.size);
            list_digi_it pos = list_digi_begin(&a);
            list_digi_it_advance(&pos, index);
            auto it = b.begin();
            advance(it, index);
            b.insert(it, first_b, last_b);
            list_digi_insert_range(&pos, &first_a);
            print_lst(&a);
            print_list(b);
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
        case TEST_ERASE_RANGE:
            if (a.size)
            {
                print_lst(&a);
                list_digi_it first_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters(&a, &first_a, b, first_b, last_b);
                /*auto it = */
                b.erase(first_b, last_b);
                list_digi_erase_range(&first_a);
                print_lst(&a);
                print_list(b);
                // CHECK_RANGE(first_a, it, last_b);
                CHECK(a, b);
            }
            break;
        case TEST_INSERT_GENERIC: {
            print_lst(&a);
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_it begin = list_digi_begin(&a);
            list_digi_it range2 = list_digi_begin(&aa);
            print_lst(&aa);
            b.insert(b.begin(), bb.begin(), bb.end());
            list_digi_insert_generic(&begin, &range2);
            print_lst(&a);
            print_list(b);
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
#ifdef DEBUG
        case TEST_ERASE_GENERIC:
            if (a.size)
            {
                print_lst(&a);
                list_digi aa;
                std::list<DIGI> bb;
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_digi_it range2 = list_digi_begin(&aa);
                b.erase(bb.begin(), bb.end());
                list_digi_erase_generic(&a, &range2);
                print_lst(&a);
                print_list(b);
                CHECK(a, b);
            }
            break;
#endif
        case TEST_GENERATE: {
            digi_generate_reset();
            list_digi_generate(&a, digi_generate);
            digi_generate_reset();
            std::generate(b.begin(), b.end(), DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_GENERATE_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            digi_generate_reset();
            list_digi_generate_range(&first_a, digi_generate);
            digi_generate_reset();
            std::generate(first_b, last_b, DIGI_generate);
            CHECK(a, b);
            break;
        }
        case TEST_TRANSFORM: {
            list_digi aa = list_digi_transform(&a, digi_untrans);
            std::list<DIGI> bb;
            bb.resize(b.size());
            std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
            CHECK(aa, bb);
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
        case TEST_COPY_IF: {
            list_digi aa = list_digi_copy_if(&a, digi_is_odd);
            std::list<DIGI> bb;
#if __cplusplus >= 201103L && !defined(_MSC_VER)
            std::copy_if(b.begin(), b.end(), std::back_inserter(bb), DIGI_is_odd);
#else
            for (auto &d : b)
            {
                if (DIGI_is_odd(d))
                    bb.push_back(d);
            }
#endif
            CHECK(aa, bb);
            list_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_COPY_IF_RANGE: {
            list_digi_it range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            list_digi aa = list_digi_copy_if_range(&range, digi_is_odd);
            std::list<DIGI> bb;
#if __cplusplus >= 201103L && !defined(_MSC_VER)
            std::copy_if(first_b, last_b, std::back_inserter(bb), DIGI_is_odd);
#else
            for (auto d = first_b; d != last_b; d++) {
                if (DIGI_is_odd(*d))
                    bb.push_back(*d);
            }
#endif
            CHECK(aa, bb);
            list_digi_free(&aa);
            CHECK(a, b);
            break;
        }
        case TEST_INCLUDES: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            bool a_found = list_digi_includes(&a, &aa);
            bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
            assert(a_found == b_found);
            print_list(b);
            print_list(bb);
            CHECK(aa, bb);
            list_digi_free(&aa);
            break;
        }
        case TEST_INCLUDES_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_it first_a1;
            std::list<DIGI>::iterator first_b1, last_b1;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            list_digi_it first_a2;
            std::list<DIGI>::iterator first_b2, last_b2;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            LOG("CTL a includes aa\n");
            print_lst_range(first_a1);
            print_lst_range(first_a2);
            bool a_found = list_digi_includes_range(&first_a1, &first_a2);
            LOG("STL b - bb\n");
            print_list(b);
            print_list(bb);
            bool b_found = std::includes(first_b1, last_b1, first_b2, last_b2);
            assert(a_found == b_found);
            CHECK(aa, bb);
            list_digi_free(&aa);
            break;
        }
        case TEST_UNION: // 48
        {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi aaa = list_digi_union(&a, &aa);
#ifndef _MSC_VER
            std::list<DIGI> bbb;
            std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
            print_list(b);
            print_list(bb);
            print_list(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_INTERSECTION: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi aaa = list_digi_intersection(&a, &aa);
#ifndef _MSC_VER
            std::list<DIGI> bbb;
            std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi aaa = list_digi_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
            std::list<DIGI> bbb;
            std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_DIFFERENCE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            print_lst(&a);
            list_digi aaa = list_digi_difference(&a, &aa);
#ifndef _MSC_VER
            std::list<DIGI> bbb;
            std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
            CHECK(aaa, bbb);
#endif
            CHECK(aa, bb);
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_UNION_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_it first_a1;
            std::list<DIGI>::iterator first_b1, last_b1;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            list_digi_it first_a2;
            std::list<DIGI>::iterator first_b2, last_b2;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_lst_range(first_a1);
            print_lst_range(first_a2);
            list_digi aaa = list_digi_union_range(&first_a1, &first_a2);
            LOG("CTL => aaa\n");
            print_lst(&aaa);

            std::list<DIGI> bbb;
            LOG("STL b + bb\n");
            print_list(b);
            print_list(bb);
#ifndef _MSC_VER
            std::set_union(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
            LOG("STL => bbb\n");
            print_list(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_INTERSECTION_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_it first_a1;
            std::list<DIGI>::iterator first_b1, last_b1;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            list_digi_it first_a2;
            std::list<DIGI>::iterator first_b2, last_b2;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_lst_range(first_a1);
            print_lst_range(first_a2);
            list_digi aaa = list_digi_intersection_range(&first_a1, &first_a2);
            LOG("CTL => aaa\n");
            print_lst(&aaa);

            std::list<DIGI> bbb;
            LOG("STL b + bb\n");
            print_list(b);
            print_list(bb);
#ifndef _MSC_VER
            std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
            LOG("STL => bbb\n");
            print_list(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_DIFFERENCE_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_it first_a1;
            std::list<DIGI>::iterator first_b1, last_b1;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            list_digi_it first_a2;
            std::list<DIGI>::iterator first_b2, last_b2;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_lst_range(first_a1);
            print_lst_range(first_a2);
            list_digi aaa = list_digi_difference_range(&first_a1, &first_a2);
            LOG("CTL => aaa\n");
            print_lst(&aaa);

            std::list<DIGI> bbb;
            LOG("STL b + bb\n");
            print_list(b);
            print_list(bb);
#ifndef _MSC_VER
            std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
            LOG("STL => bbb\n");
            print_list(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
            list_digi_sort(&a);
            list_digi_sort(&aa);
            b.sort();
            bb.sort();
            list_digi_it first_a1;
            std::list<DIGI>::iterator first_b1, last_b1;
            get_random_iters(&a, &first_a1, b, first_b1, last_b1);
            list_digi_it first_a2;
            std::list<DIGI>::iterator first_b2, last_b2;
            get_random_iters(&aa, &first_a2, bb, first_b2, last_b2);

            LOG("CTL a + aa\n");
            print_lst_range(first_a1);
            print_lst_range(first_a2);
            list_digi aaa = list_digi_symmetric_difference_range(&first_a1, &first_a2);
            LOG("CTL => aaa\n");
            print_lst(&aaa);

            std::list<DIGI> bbb;
            LOG("STL b + bb\n");
            print_list(b);
            print_list(bb);
#ifndef _MSC_VER
            std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
            LOG("STL => bbb\n");
            print_list(bbb);
            CHECK(aa, bb);
            CHECK(aaa, bbb);
#endif
            list_digi_free(&aaa);
            list_digi_free(&aa);
            break;
        }
        case TEST_EQUAL_VALUE: {
            size_t size1 = MIN(TEST_RAND(a.size), 5);
            list_digi_resize(&a, size1, digi_init(0));
            b.resize(size1);
            list_digi_it r1a;
            std::list<DIGI>::iterator r1b, last1_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            int value = a.size ? *a.head->value.value : 0;
            LOG("equal_value %d\n", value);
            print_lst(&a);
            bool same_a = list_digi_equal_value(&r1a, digi_init(value));
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
        case TEST_EQUAL_RANGE: {
            list_digi aa = list_digi_copy(&a);
            std::list<DIGI> bb = b;
            list_digi_it r1a, r2a;
            std::list<DIGI>::iterator r1b, last1_b, r2b, last2_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            get_random_iters(&aa, &r2a, bb, r2b, last2_b);
            bool same_a = list_digi_equal_range(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            bool same_b = std::equal(r1b, last1_b, r2b, last2_b);
            LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
            assert(same_a == same_b);
#else
            bool same_b = std::equal(r1b, last1_b, r2b);
            LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
            if (same_a != same_b)
                printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
            list_digi_free(&aa);
            break;
        }
        case TEST_GENERATE_N: // TEST=63
        {
            size_t count = TEST_RAND(20);
#ifndef _MSC_VER
            digi_generate_reset();
            list_digi_generate_n(&a, count, digi_generate);
            digi_generate_reset();
            /*
            std::generate_n(b.begin(), count, DIGI_generate);
            */
            // FIXME The STL is arguably broken here. Or we should use a
            // different generate_n.
            int n = MIN(count, b.size());
            auto end = b.begin();
            std::advance(end, n);
            b.erase(b.begin(), end);
            std::generate_n(std::inserter(b, b.begin()), n, DIGI_generate);
            print_list(b);
            CHECK(a, b);
#endif
            break;
        }
#ifdef DEBUG
        case TEST_GENERATE_N_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            size_t off = std::distance(b.begin(), first_b);
            size_t len = std::distance(first_b, last_b);
            size_t count = TEST_RAND(20 - off);
            LOG("generate_n_range %zu\n", count);
#ifndef _MSC_VER
            digi_generate_reset();
            list_digi_generate_n_range(&first_a, count, digi_generate);
            print_lst(&a);
            digi_generate_reset();
            int n = MIN(MIN(count, b.size()), len);
            last_b = first_b;
            std::advance(last_b, n);
            b.erase(first_b, last_b);
            first_b = b.begin();
            std::advance(first_b, off);
            std::generate_n(std::inserter(b, first_b), n, DIGI_generate);
            print_list(b);
            CHECK(a, b);
#endif
            break;
        }
        case TEST_TRANSFORM_IT: {
            list_digi_it pos = list_digi_begin(&a);
            list_digi_it_advance(&pos, 1);
            list_digi aa = list_digi_transform_it(&a, &pos, digi_bintrans);
            std::list<DIGI> bb;
            // bb.resize(b.size());
            std::transform(b.begin(), b.end(), b.begin()++, bb.begin(), DIGI_bintrans);
            CHECK(aa, bb);
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
        case TEST_TRANSFORM_RANGE: {
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            list_digi aa = list_digi_init();
            size_t dist = std::distance(first_b, last_b);
            list_digi_resize(&aa, dist, digi_init(0));
            list_digi_it dest = list_digi_begin(&aa);
            list_digi_it it = list_digi_transform_range(&first_a, dest, digi_untrans);
            std::list<DIGI> bb;
            // bb.resize(dist);
            auto iter = std::transform(first_b, last_b, b.begin()++, bb.begin(), DIGI_bintrans);
            CHECK_RANGE(it, iter, last_b);
            CHECK(aa, bb);
            // heap use-after-free
            CHECK(a, b);
            list_digi_free(&aa);
            break;
        }
#endif // DEBUG
        case TEST_MISMATCH: {
            if (a.size < 2)
                break;
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(a.size), NULL);
            list_digi_it b1, b2;
            b1 = list_digi_begin(&a);
            b2 = list_digi_begin(&aa);
            list_digi_it r1a, r2a;
            std::list<DIGI>::iterator r1b, last1_b, r2b, last2_b;
            get_random_iters(&a, &r1a, b, r1b, last1_b);
            get_random_iters(&aa, &r2a, bb, r2b, last2_b);
            /*bool found_a = */ list_digi_mismatch(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
            auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
#else
            if (!bb.size() || !distance(r2b, last2_b))
            {
                printf("skip std::mismatch with empty 2nd range. use C++14\n");
                list_digi_free(&aa);
                break;
            }
            auto pair = std::mismatch(r1b, last1_b, r2b);
#endif
            int d1a = list_digi_it_distance(&b1, &r1a);
            int d2a = list_digi_it_distance(&b2, &r2a);
            LOG("iter1 %d, iter2 %d\n", d1a, d2a);
            // TODO check found_a against iter results
            assert(d1a == distance(b.begin(), pair.first));
            assert(d2a == distance(bb.begin(), pair.second));
            list_digi_free(&aa);
            break;
        }
        case TEST_SEARCH: // 57
        {
            print_lst(&a);
            list_digi aa = list_digi_copy(&a);
            std::list<DIGI> bb = b;
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &first_a, bb, first_b, last_b);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                if (first_a.node)
                {
                    digi_free(first_a.ref);
                    first_a.node->value = digi_init(0);
                }
                *first_b = DIGI{0};
            }
            // print_lst_range(first_a);
            list_digi_it found_a = list_digi_search(&a, &first_a);
            auto found_b = search(b.begin(), b.end(), first_b, last_b);
            LOG("found a: %s\n", list_digi_it_done(&found_a) ? "no" : "yes");
            LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
            CHECK_RANGE(found_a, found_b, b.end());
            list_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_RANGE: {
            list_digi aa = list_digi_copy(&a);
            std::list<DIGI> bb = b;
            list_digi_it needle, range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&aa, &needle, bb, first_b, last_b);
            if (aa.size && TEST_RAND(2))
            { // 50% unsuccessful
                if (needle.node)
                {
                    digi_free(needle.ref);
                    needle.node->value = digi_init(0);
                }
                *first_b = DIGI{0};
            }
            // print_list_range(needle);
            range = list_digi_begin(&a);
            bool found = list_digi_search_range(&range, &needle);
            auto iter = search(b.begin(), b.end(), first_b, last_b);
            LOG("found a: %s\n", found ? "yes" : "no");
            LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
            assert(found == !list_digi_it_done(&range));
            CHECK_RANGE(range, iter, b.end());
            list_digi_free(&aa);
            break;
        }
        case TEST_SEARCH_N: {
            print_lst(&a);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n %zu %d\n", count, value);
            list_digi_it aa = list_digi_search_n(&a, count, digi_init(value));
            auto bb = search_n(b.begin(), b.end(), count, DIGI{value});
            CHECK_ITER(aa, b, bb);
            LOG("found %s at %zu\n", list_digi_it_done(&aa) ? "no" : "yes", list_digi_it_index(&aa));
            break;
        }
        case TEST_SEARCH_N_RANGE: {
            list_digi_it range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            size_t count = TEST_RAND(4);
            int value = pick_random(&a);
            LOG("search_n_range %zu %d\n", count, value);
            print_lst_range(&range);
            list_digi_it *aa = list_digi_search_n_range(&range, count, digi_init(value));
            auto bb = search_n(first_b, last_b, count, DIGI{value});
            CHECK_RANGE(*aa, bb, last_b);
            LOG("found %s at %zu\n", list_digi_it_done(aa) ? "no" : "yes", list_digi_it_index(aa));
            break;
        }
        case TEST_ADJACENT_FIND: {
            print_lst(&a);
            list_digi_it aa = list_digi_adjacent_find(&a);
            auto bb = adjacent_find(b.begin(), b.end());
            CHECK_ITER(aa, b, bb);
            LOG("found %s\n", list_digi_it_done(&aa) ? "no" : "yes");
            break;
        }
        case TEST_ADJACENT_FIND_RANGE: {
            list_digi_it range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            // print_list_range(range);
            list_digi_it *aa = list_digi_adjacent_find_range(&range);
            auto bb = adjacent_find(first_b, last_b);
            CHECK_RANGE(*aa, bb, last_b);
            LOG("found %s\n", list_digi_it_done(aa) ? "no" : "yes");
            break;
        }
        case TEST_FIND_FIRST_OF: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(5), NULL);
            std::list<DIGI>::iterator bb_last = bb.end();
            list_digi_it range2 = list_digi_begin(&aa);
            if (list_digi_it_index(&range2) + 5 < aa.size)
            {
                list_digi_it_advance_end(&range2, 5);
                bb_last = bb.begin();
                std::advance(bb_last, 5);
            }
            print_lst(&a);
            LOG("bb_last: %ld\n", std::distance(bb.begin(), bb_last));
            print_lst(&aa);
            list_digi_it it = list_digi_find_first_of(&a, &range2);
            auto iter = std::find_first_of(b.begin(), b.end(), bb.begin(), bb_last);
            LOG("=> %s/%s, %ld/%ld: %d/%d\n", !list_digi_it_done(&it) ? "yes" : "no", iter != b.end() ? "yes" : "no",
                list_digi_it_index(&it), distance(b.begin(), iter), !list_digi_it_done(&it) ? *it.ref->value : -1,
                iter != b.end() ? *iter->value : -1);
            CHECK_RANGE(it, iter, b.end());
            list_digi_free(&aa);
            break;
        }
        case TEST_FIND_FIRST_OF_RANGE: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(5), NULL);
            list_digi_it first_a, s_first;
            std::list<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            print_lst(&a);
            get_random_iters(&aa, &s_first, bb, s_first_b, s_last_b);
            print_lst(&aa);

            bool found_a = list_digi_find_first_of_range(&first_a, &s_first);
            auto it = std::find_first_of(first_b, last_b, s_first_b, s_last_b);
            LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", it != last_b ? "yes" : "no",
                list_digi_it_index(&first_a), distance(b.begin(), it));
            if (found_a)
                assert(it != last_b);
            else
                assert(it == last_b);
            // CHECK_RANGE(first_a, it, last_b);
            list_digi_free(&aa);
            break;
        }
        case TEST_FIND_END: {
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(4), NULL);
            print_lst(&aa);
            list_digi_it s_first = list_digi_begin(&aa);
            list_digi_it it = list_digi_find_end(&a, &s_first);
            auto iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.end());
            bool found_a = !list_digi_it_done(&it);
            bool found_b = iter != b.end();
            CHECK_ITER(it, b, iter);
            assert(found_a == found_b);
            list_digi_free(&aa);
            break;
        }
        case TEST_FIND_END_RANGE: {
            list_digi_it first_a, s_first;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            list_digi aa;
            std::list<DIGI> bb;
            setup_lists(&aa, bb, TEST_RAND(4), NULL);
            print_lst(&aa);
            s_first = list_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
            first_a = list_digi_find_end_range(&first_a, &s_first);
            auto it = std::find_end(first_b, last_b, bb.begin(), bb.end());
            CHECK_RANGE(first_a, it, last_b);
#endif
            list_digi_free(&aa);
            break;
        }
        case TEST_UNIQUE_RANGE: {
            list_digi_it range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            print_lst_range(range);
            list_digi_it aa = list_digi_unique_range(&range);
            bool found_a = !list_digi_it_done(&aa);
            size_t index = list_digi_it_index(&aa);
            auto bb = unique(first_b, last_b);
            bool found_b = bb != last_b;
            long dist = std::distance(b.begin(), bb);
            if (found_b)
                b.erase(bb, last_b);
            LOG("found %s at %zu, ", found_a ? "yes" : "no", index);
            LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
            assert(found_a == found_b);
            assert((long)index == dist);
            break;
        }
        case TEST_LOWER_BOUND: // 73
        {
            list_digi_sort(&a);
            b.sort();
            int key = pick_random(&a);
            list_digi_it aa = list_digi_lower_bound(&a, digi_init(key));
            auto bb = lower_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_UPPER_BOUND: {
            list_digi_sort(&a);
            b.sort();
            int key = pick_random(&a);
            list_digi_it aa = list_digi_upper_bound(&a, digi_init(key));
            auto bb = upper_bound(b.begin(), b.end(), DIGI{key});
            if (bb != b.end())
            {
                LOG("%d: %d vs %d\n", key, *aa.ref->value, *bb->value);
            }
            CHECK_ITER(aa, b, bb);
            break;
        }
        case TEST_LOWER_BOUND_RANGE: {
            list_digi_sort(&a);
            b.sort();
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            list_digi_it *aa = list_digi_lower_bound_range(&first_a, digi_init(key));
            std::list<DIGI>::iterator bb = lower_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_UPPER_BOUND_RANGE: {
            list_digi_sort(&a);
            b.sort();
            list_digi_it first_a;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &first_a, b, first_b, last_b);
            int key = pick_random(&a);
            list_digi_it *aa = list_digi_upper_bound_range(&first_a, digi_init(key));
            std::list<DIGI>::iterator bb = upper_bound(first_b, last_b, DIGI{key});
            if (bb != last_b)
            {
                LOG("%d: %d vs %d\n", key, *aa->ref->value, *bb->value);
            }
            CHECK_RANGE(*aa, bb, last_b);
            break;
        }
        case TEST_BINARY_SEARCH: {
            list_digi_sort(&a);
            b.sort();
            int key = pick_random(&a);
            bool found_a = list_digi_binary_search(&a, digi_init(key));
            bool found_b = binary_search(b.begin(), b.end(), DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
            break;
        }
        case TEST_BINARY_SEARCH_RANGE: {
            list_digi_sort(&a);
            b.sort();
            list_digi_it range;
            std::list<DIGI>::iterator first_b, last_b;
            get_random_iters(&a, &range, b, first_b, last_b);
            int key = pick_random(&a);
            bool found_a = list_digi_binary_search_range(&range, digi_init(key));
            bool found_b = binary_search(first_b, last_b, DIGI{key});
            LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
            assert(found_a == found_b);
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
        CHECK(a, b);
        list_digi_free(&a);
    }
    queue_int_free(&tests);
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
