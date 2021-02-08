#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/list.h>

#include <list>
#include <algorithm>

void print_lst(list_digi *a)
{
    int i = 0;
    if (a->size)
        list_foreach_ref(list_digi, a, it)
            printf ("%d: %d\n", i++, *it.ref->value);
    printf ("====\n");
}

void print_list(std::list<DIGI> &b)
{
    int i = 0;
    if (b.size())
        for(auto& d: b)
            printf ("%d: %d\n", i++, *d.value);
    printf ("----\n");
}

#define print_lst_range(x)
#ifdef DEBUG
#define TEST_MAX_VALUE 15
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 10
#else
#define print_lst(x)
#define print_list(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(list_digi* a)
{
    const size_t index = TEST_RAND(a->size);
    int test_value = 0;
    size_t current = 0;
    list_foreach_ref(list_digi, a, it)
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

#define CHECK(_x, _y) {                                           \
    assert(_x.size == _y.size());                                 \
    assert(list_digi_empty(&_x) == _y.empty());                   \
    if(_x.size > 0) {                                             \
        assert(*_y.front().value == *list_digi_front(&_x)->value);\
        assert(*_y.back().value == *list_digi_back(&_x)->value);  \
    }                                                             \
    std::list<DIGI>::iterator _iter = _y.begin();                 \
    int i = 0;                                                    \
    list_foreach_ref(list_digi, &_x, _it) {                       \
        LOG("%d: %d, ", i, *_it.ref->value);                      \
        assert(*_it.ref->value == *_iter->value);                 \
        i++;                                                      \
        _iter++;                                                  \
    }                                                             \
    LOG("\n");                                                    \
    list_digi_it _it = list_digi_begin(&_x);                      \
    for(auto& _d : _y) {                                          \
        assert(*_it.ref->value == *_d.value);                     \
        list_digi_it_next(&_it);                                  \
    }                                                             \
}

#define LOG_ITER(_it, b, _iter, line)                             \
    if ((_it)->node != NULL)                                      \
    {                                                             \
        if (_iter == b.end())                                     \
            printf("STL iter at end, line %u FAIL\n", line);      \
        if (*((_it)->ref->value) != *(*_iter).value)              \
            printf("iter %d vs %d, line %u FAIL\n",               \
                   *((_it)->ref->value),                          \
                   *(*_iter).value, line);                        \
    } else                                                        \
        assert (_iter == b.end())
#define CHECK_ITER(_it, b, _iter)                                 \
    if ((_it).node != NULL)                                       \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*(_it).ref->value == *(*_iter).value);             \
    } else                                                        \
        assert (_iter == b.end())

static void
setup_lists(list_digi* a, std::list<DIGI>& b, size_t size, int* max_value)
{
    *a = list_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for(size_t pushes = 0; pushes < size; pushes++)
    {
        int value = TEST_RAND(TEST_MAX_VALUE - 1); // SEE COMMENT IN CASE MERGE.
        if(max_value && value > *max_value)
            *max_value = value;
        list_digi_push_back(a, digi_init(value));
        b.push_back(DIGI{value});
    }
}

// list_digi_it* first_a, *last_a;
// _List_iterator<DIGI>* first_b, *last_b;
static void
get_random_iters (list_digi *a, list_digi_it *first_a, list_digi_it *last_a,
                  std::list<DIGI>& b, std::list<DIGI>::iterator& first_b,
                  std::list<DIGI>::iterator& last_b)
{
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        list_digi_it it1 = list_digi_begin(a);
        list_digi_it_advance(&it1, r1);
        first_b = b.begin();
        for (size_t i = 0; i<r1; i++)
        {
            first_b++;
        }
        *first_a = it1;
        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
            first_a->end = last_a->node;

        }
        else if (r2 == a->size)
        {
            *last_a = list_digi_end(a);
            last_b = b.end();
        }
        else
        {
            list_digi_it it2 = list_digi_begin(a);
            list_digi_it_advance(&it2, r2);
            last_b = b.begin();
            for(size_t i = 0; i < r2; i++)
                last_b++;
            *last_a = it2;
        }
    }
    else
    {
        list_digi_it end = list_digi_end (a);
        *first_a = end;
        *last_a = end;
        last_a->end = first_a->node;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a->node;
}

int
main(void)
{
    int errors = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        list_digi a;
        std::list<DIGI> b;
        int max_value = 0;
        const size_t size = TEST_RAND(TEST_MAX_SIZE);
        setup_lists(&a, b, size, &max_value);

#define FOREACH_METH(TEST) \
        TEST(PUSH_BACK) \
        TEST(PUSH_FRONT) \
        TEST(POP_BACK) \
        TEST(POP_FRONT) \
        TEST(ERASE) \
        TEST(INSERT) /* 5 */ \
        TEST(CLEAR) \
        TEST(RESIZE) \
        TEST(ASSIGN) \
        TEST(SWAP) \
        TEST(COPY) \
        TEST(REVERSE) \
        TEST(REMOVE) \
        TEST(EMPLACE) \
        TEST(EMPLACE_FRONT) \
        TEST(EMPLACE_BACK) /* 15 */ \
        TEST(REMOVE_IF) \
        TEST(ERASE_IF) \
        TEST(SPLICE) /* 18 */ \
        TEST(SPLICE_IT) \
        TEST(SPLICE_RANGE) \
        TEST(MERGE) \
        TEST(EQUAL) \
        TEST(SORT) \
        TEST(UNIQUE) \
        TEST(FIND) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(COUNT) \
        TEST(COUNT_IF) \
        TEST(COUNT_RANGE) \
        TEST(COUNT_IF_RANGE) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(INSERT_COUNT) /* 41 */ \
        TEST(INSERT_RANGE) \
        TEST(ERASE_RANGE) \
        TEST(UNION) \
        TEST(INTERSECTION) \
        TEST(UNION_RANGE) \
        TEST(INTERSECTION_RANGE) \
        TEST(GENERATE) \
        TEST(GENERATE_RANGE) \
        TEST(TRANSFORM) \

#define FOREACH_DEBUG(TEST) \
        TEST(EQUAL_RANGE) /* 47 */ \
        TEST(DIFFERENCE) \
        TEST(SYMMETRIC_DIFFERENCE) \
        TEST(DIFFERENCE_RANGE) \
        TEST(SYMMETRIC_DIFFERENCE_RANGE) \
        TEST(FIND_END) \
        TEST(FIND_END_IF) \
        TEST(FIND_END_RANGE) \
        TEST(FIND_END_IF_RANGE) \
        TEST(LOWER_BOUND) \
        TEST(UPPER_BOUND) \
        TEST(LOWER_BOUND_RANGE) \
        TEST(UPPER_BOUND_RANGE) \
        TEST(GENERATE_N) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM_IT) \
        TEST(TRANSFORM_RANGE) \

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
            case TEST_PUSH_FRONT:
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                list_digi_push_front(&a, digi_init(value));
                b.push_front(DIGI{value});
                CHECK(a, b);
                break;
            }
            case TEST_PUSH_BACK:
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                list_digi_push_back(&a, digi_init(value));
                b.push_back(DIGI{value});
                CHECK(a, b);
                break;
            }
            case TEST_POP_FRONT:
            {
                if(a.size > 0)
                {
                    list_digi_pop_front(&a);
                    b.pop_front();
                }
                CHECK(a, b);
                break;
            }
            case TEST_POP_BACK:
            {
                if(a.size > 0)
                {
                    list_digi_pop_back(&a);
                    b.pop_back();
                }
                CHECK(a, b);
                break;
            }
            case TEST_ERASE:
            {
                if (a.size > 0) // we survive, but STL segfaults
                {
                    size_t index = TEST_RAND(a.size);
                    std::list<DIGI>::iterator iter = b.begin();
                    std::advance(iter, index);
                    list_digi_it it = list_digi_begin(&a);
                    list_digi_it_advance (&it, index);
                    LOG("erase %zu\n", index);
                    list_digi_erase(&it);
                    b.erase(iter);
                    CHECK(a, b);
                }
                break;
            }
            case TEST_INSERT:
            {
                size_t index = TEST_RAND(a.size);
                int value = TEST_RAND(TEST_MAX_VALUE);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
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
            case TEST_CLEAR:
            {
                list_digi_clear(&a);
                b.clear();
                CHECK(a, b);
                break;
            }
            case TEST_RESIZE:
            {
                size_t resize = 2 * TEST_RAND(TEST_MAX_SIZE);
                list_digi_resize(&a, resize, digi_init(0));
                b.resize(resize);
                print_lst(&a);
                print_list(b);
                CHECK(a, b);
                break;
            }
            case TEST_ASSIGN:
            {
                size_t width = TEST_RAND(a.size);
                if(width > 2)
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    list_digi_assign(&a, width, digi_init(value));
                    b.assign(width, DIGI{value});
                }
                CHECK(a, b);
                break;
            }
            case TEST_SWAP:
            {
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
            case TEST_COPY:
            {
                list_digi aa = list_digi_copy(&a);
                std::list<DIGI> bb = b;
                CHECK(aa, bb);
                list_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_REVERSE:
            {
                list_digi_reverse(&a);
                b.reverse();
                CHECK(a, b);
                break;
            }
            case TEST_REMOVE:
            {
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
            case TEST_EMPLACE:
            {
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
                //print_lst(&a);
                auto iter = b.begin();
#if __cplusplus >= 201103L
                b.emplace(++iter, DIGI{value});
#else
                b.insert(++iter, DIGI{value});
#endif
                LOG("STL emplace begin++ %d\n", *DIGI{value});
                //print_list(b);
                CHECK(a, b);
                digi_free(&aa);
                break;
            }
            case TEST_EMPLACE_FRONT:
            {
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
            case TEST_EMPLACE_BACK:
            {
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
            case TEST_REMOVE_IF:
            {
                print_lst(&a);
                list_digi_remove_if(&a, digi_is_odd);
                b.remove_if(DIGI_is_odd);
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_IF:
            {
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
            case TEST_SPLICE:
            {
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
            case TEST_MERGE:
            {
                list_digi aa = list_digi_init();
                std::list<DIGI> bb;
                int total = 0;
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    int value = TEST_RAND(128);
                    total += value;
                    if(pushes == (size - 1))
                        // MAX + 1 ENSURES MERGE CAN APPEND TO TAIL.
                        total = max_value + 1;
                    list_digi_push_back(&aa, digi_init(total));
                    bb.push_back(DIGI{total});
                }
                b.merge(bb);
                list_digi_merge(&a, &aa);
                CHECK(a, b);
                break;
            }
            case TEST_EQUAL:
            {
                list_digi aa = list_digi_copy(&a);
                std::list<DIGI> bb = b;
                assert(list_digi_equal(&a, &aa));
                assert(b == bb);
                list_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_SORT:
            {
                list_digi_sort(&a);
                b.sort();
                CHECK(a, b);
                break;
            }
            case TEST_UNIQUE:
            {
                list_digi_unique(&a);
                b.unique();
                CHECK(a, b);
                break;
            }
            case TEST_FIND:
            {
                int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                         : random_element(&a);
                digi key = digi_init(value);
                list_digi_it aa = list_digi_find(&a, key);
                auto bb = find(b.begin(), b.end(), DIGI{value});
                CHECK_ITER(aa, b, bb);
                digi_free (&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_ALL_OF:
            {
                bool aa = list_digi_all_of(&a, digi_is_odd);
                bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF:
            {
                bool aa = list_digi_any_of(&a, digi_is_odd);
                bool bb = any_of(b.begin(), b.end(), DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd FAIL\n", (int)aa, (int)bb);
                    errors++;
                }
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = list_digi_none_of(&a, digi_is_odd);
                bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                assert(is_a == is_b);
                break;
            }
            case TEST_FIND_RANGE:
            {
                int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                         : random_element(&a);
                digi key = digi_init(vb);
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_it aa = list_digi_find_range(&first_a, &last_a, key);
                auto bb = find(first_b, last_b, vb);
                CHECK_ITER(aa, b, bb);
                digi_free (&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_all_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = all_of(first_b, last_b, DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_any_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = any_of(first_b, last_b, DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_none_of_range(&first_a, &last_a, digi_is_odd);
                bool bb = none_of(first_b, last_b, DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                }
                assert(aa == bb);
                break;
            }
            case TEST_FIND_IF:
            {
                list_digi_it aa = list_digi_find_if(&a, digi_is_odd);
                auto bb = find_if(b.begin(), b.end(), DIGI_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                list_digi_it aa = list_digi_find_if_not(&a, digi_is_odd);
                auto bb = find_if_not(b.begin(), b.end(), DIGI_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_it aa = list_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                auto bb = find_if(first_b, last_b, DIGI_is_odd);
                print_lst(&a);
                print_list(b);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_it aa = list_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto bb = find_if_not(first_b, last_b, DIGI_is_odd);
                CHECK_ITER(aa, b, bb);
                break;
            }
            case TEST_INSERT_COUNT:
            {
                size_t index = TEST_RAND(a.size);
                size_t count = TEST_RAND(10);
                int value = TEST_RAND(TEST_MAX_VALUE);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
                LOG("insert %d (%zux) at %zu\n", value, count, index);
                list_digi_it *aa = list_digi_insert_count(&it, count, digi_init(value));
                // does libstc++ violate its docs?
                std::list<DIGI>::iterator bb = b.insert(iter, count, DIGI{value});
                //print_lst(&a);
                //print_list(b);
                CHECK_ITER(*aa, b, bb);
                CHECK(a, b);
                break;
            }
            case TEST_COUNT:
            {
                int key = TEST_RAND(TEST_MAX_SIZE);
                int aa = list_digi_count(&a, digi_init(key));
                int bb = count(b.begin(), b.end(), DIGI{key});
                assert(aa == bb);
                break;
            }
            case TEST_COUNT_IF:
            {
                size_t count_a = list_digi_count_if(&a, digi_is_odd);
                size_t count_b = count_if(b.begin(), b.end(), DIGI_is_odd);
                assert(count_a == count_b);
                break;
            }
            case TEST_COUNT_RANGE:
            {
                int test_value = 0;
                int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                     : test_value;
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                // used to fail with 0,0 of 0
                size_t numa = list_digi_count_range(&first_a, &last_a, digi_init(v));
                size_t numb = count(first_b, last_b, DIGI{v});
                assert(numa == numb);
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa =
                    list_digi_count_if_range(&first_a, &last_a, digi_is_odd);
                size_t numb = count_if(first_b, last_b, DIGI_is_odd);
                if (numa != numb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d FAIL\n", (int)numa, (int)numb);
                    errors++;
                }
                assert(numa == numb); //fails. off by one, counts one too much
                break;
            }
            case TEST_SPLICE_IT:
            {
                size_t index = TEST_RAND(a.size);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
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
            case TEST_SPLICE_RANGE:
            {
                size_t index = TEST_RAND(a.size);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
                list_digi aa;
                std::list<DIGI> bb;
                size_t bsize = TEST_RAND(TEST_MAX_SIZE);
                setup_lists(&aa, bb, bsize, NULL);
                std::list<DIGI>::iterator bbpos = bb.begin();
                std::advance(bbpos, bsize / 2);
                std::list<DIGI>::iterator bbend = bb.begin();
                std::advance(bbend, bsize - 1);
                list_digi_it aapos = list_digi_begin(&aa);
                list_digi_it_advance(&aapos, bsize / 2);
                list_digi_it aaend = list_digi_begin(&aa);
                list_digi_it_advance(&aaend, bsize - 1);
                if (b.size() && bb.size())
                {
                    b.splice(iter, bb, bbpos, bbend);
                    list_digi_splice_range(&it, &aapos, &aaend);
                    CHECK(a, b);
                }
                list_digi_free(&aa);
                break;
            }
            // algorithms + ranges
            case TEST_INSERT_RANGE:
                if (a.size > 2)
                {
                    print_lst(&a);
                    size_t size2 = TEST_RAND(TEST_MAX_SIZE);
                    list_digi aa = list_digi_init_from(&a);
                    std::list<DIGI> bb;
                    list_digi_it first_a, last_a;
                    std::list<DIGI>::iterator first_b, last_b;
                    for(size_t pushes = 0; pushes < size2; pushes++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        list_digi_push_back(&aa, digi_init(value));
                        bb.push_back(DIGI{value});
                    }
                    print_lst(&aa);
                    get_random_iters (&aa, &first_a, &last_a, bb, first_b, last_b);
                    const size_t index = TEST_RAND(a.size);
                    list_digi_it pos = list_digi_begin(&a);
                    list_digi_it_advance(&pos, index);
                    auto it = b.begin();
                    advance(it, index);
                    b.insert(it, first_b, last_b);
                    list_digi_insert_range(&pos, &first_a, &last_a);
                    print_lst(&a);
                    print_list(b);
                    CHECK(a, b);
                    list_digi_free(&aa);
                }
                break;
            case TEST_ERASE_RANGE:
                if (a.size)
                {
                    print_lst(&a);
                    list_digi_it first_a, last_a;
                    std::list<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    const size_t index = TEST_RAND(a.size);
                    list_digi_it pos = list_digi_begin(&a);
                    list_digi_it_advance(&pos, index);
                    auto it = b.begin();
                    advance(it, index);
                    b.erase(first_b, last_b);
                    list_digi_erase_range(&first_a, &last_a);
                    print_lst(&a);
                    print_list(b);
                    CHECK(a, b);
                }
                break;
            case TEST_GENERATE:
            {
                digi_generate_reset();
                list_digi_generate(&a, digi_generate);
                digi_generate_reset();
                std::generate(b.begin(), b.end(), DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                digi_generate_reset();
                list_digi_generate_range(&first_a, &last_a, digi_generate);
                digi_generate_reset();
                std::generate(first_b, last_b, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM:
            {
                list_digi aa = list_digi_transform(&a, digi_untrans);
                std::list<DIGI> bb;
                bb.resize(b.size());
                std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
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
# ifndef _MSC_VER
                std::list<DIGI> bbb;
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                               std::back_inserter(bbb));
                print_list(b);
                print_list(bb);
                print_list(bbb);
                CHECK(aa, bb);
                CHECK(aaa, bbb);
# endif
                list_digi_free(&aaa);
                list_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION:
            {
                list_digi aa;
                std::list<DIGI> bb;
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_digi_sort(&a);
                list_digi_sort(&aa);
                b.sort();
                bb.sort();
                list_digi aaa = list_digi_intersection(&a, &aa);
# ifndef _MSC_VER
                std::list<DIGI> bbb;
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                      std::back_inserter(bbb));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
# endif
                list_digi_free(&aaa);
                list_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_SYMMETRIC_DIFFERENCE:
            {
                list_digi aa;
                std::list<DIGI> bb;
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_digi_sort(&a);
                list_digi_sort(&aa);
                b.sort();
                bb.sort();
                list_digi aaa = list_digi_symmetric_difference(&a, &aa);
# ifndef _MSC_VER
                std::list<DIGI> bbb;
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                              std::back_inserter(bbb));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
# endif
                list_digi_free(&aaa);
                list_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE:
            {
                list_digi aa;
                std::list<DIGI> bb;
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_digi_sort(&a);
                list_digi_sort(&aa);
                b.sort();
                bb.sort();
                print_lst(&a);
                list_digi aaa = list_digi_difference(&a, &aa);
# ifndef _MSC_VER
                std::list<DIGI> bbb;
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                    std::back_inserter(bbb));
                CHECK(aa, bb);
                CHECK(aaa, bbb);
# endif
                list_digi_free(&aaa);
                list_digi_free(&aa);
                break;
            }
#endif // DEBUG
                case TEST_UNION_RANGE:
                {
                    list_digi aa;
                    std::list<DIGI> bb;
                    setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                    list_digi_sort(&a);
                    list_digi_sort(&aa);
                    b.sort();
                    bb.sort();
                    list_digi_it first_a1, last_a1;
                    std::list<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    list_digi_it first_a2, last_a2;
                    std::list<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

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
# ifndef _MSC_VER
                    std::set_union(first_b1, last_b1, first_b2, last_b2,
                                   std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_list(bbb);
                    CHECK(aa, bb);
                    CHECK(aaa, bbb);
# endif
                    list_digi_free(&aaa);
                    list_digi_free(&aa);
                    break;
                }
                case TEST_INTERSECTION_RANGE:
                {
                    list_digi aa;
                    std::list<DIGI> bb;
                    setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                    list_digi_sort(&a);
                    list_digi_sort(&aa);
                    b.sort();
                    bb.sort();
                    list_digi_it first_a1, last_a1;
                    std::list<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    list_digi_it first_a2, last_a2;
                    std::list<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

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
# ifndef _MSC_VER
                    std::set_intersection(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_list(bbb);
                    CHECK(aa, bb);
                    CHECK(aaa, bbb);
# endif
                    list_digi_free(&aaa);
                    list_digi_free(&aa);
                    break;
                }
#ifdef DEBUG
                case TEST_DIFFERENCE_RANGE:
                {
                    list_digi aa;
                    std::list<DIGI> bb;
                    setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                    list_digi_sort(&a);
                    list_digi_sort(&aa);
                    b.sort();
                    bb.sort();
                    list_digi_it first_a1, last_a1;
                    std::list<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    list_digi_it first_a2, last_a2;
                    std::list<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

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
# ifndef _MSC_VER
                    std::set_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_list(bbb);
                    CHECK(aa, bb);
                    CHECK(aaa, bbb);
# endif
                    list_digi_free(&aaa);
                    list_digi_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE_RANGE:
                {
                    list_digi aa;
                    std::list<DIGI> bb;
                    setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                    list_digi_sort(&a);
                    list_digi_sort(&aa);
                    b.sort();
                    bb.sort();
                    list_digi_it first_a1, last_a1;
                    std::list<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    list_digi_it first_a2, last_a2;
                    std::list<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

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
# ifndef _MSC_VER
                    std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_list(bbb);
                    CHECK(aa, bb);
                    CHECK(aaa, bbb);
# endif
                    list_digi_free(&aaa);
                    list_digi_free(&aa);
                    break;
                }
#if 0
            /*case TEST_EQUAL_RANGE:*/
            {
                /*
                int vb = TEST_RAND(TEST_MAX_VALUE);
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                // FIXME API take iter as third arg, not value
                bool aa = list_digi_equal_range(&first_a, &last_a, digi_init(vb));
                bool bb = equal_range(first_b, last_b, find(b.begin(), b.end(), DIGI{vb}));
                assert(aa == bb);
                */
                break;
            }
#endif
                case TEST_GENERATE_N: // TEST=40
                {
                    size_t count = TEST_RAND(20);
                    digi_generate_reset();
                    list_digi_generate_n(&a, count, digi_generate);
                    digi_generate_reset();
                    std::generate_n(b.begin(), count, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_N_RANGE:
                {
                    list_digi_it first_a, last_a;
                    std::list<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t off = std::distance(b.begin(), first_b);
                    size_t count = TEST_RAND(20 - off);
                    digi_generate_reset();
                    list_digi_generate_n_range(&first_a, count, digi_generate);
                    digi_generate_reset();
                    std::generate_n(first_b, count, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM_IT:
                {
                    list_digi_it pos = list_digi_begin(&a);
                    list_digi_it_advance(&pos, 1);
                    list_digi aa = list_digi_transform_it(&a, &pos, digi_bintrans);
                    std::list<DIGI> bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), b.begin()++, bb.begin(), DIGI_bintrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    list_digi_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_RANGE:
                {
                    list_digi_it first_a, last_a;
                    std::list<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    list_digi aa = list_digi_init();
                    size_t dist = std::distance(first_b, last_b);
                    list_digi_resize(&aa, dist, digi_init(0));
                    list_digi_it dest = list_digi_begin(&aa);
                    list_digi_it it = list_digi_transform_range(&first_a, &last_a, dest, digi_untrans);
                    std::list<DIGI> bb;
                    bb.resize(dist);
                    auto iter = std::transform(first_b, last_b, b.begin()++, bb.begin(), DIGI_bintrans);
                    CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
                    // heap use-after-free
                    CHECK(a, b);
                    list_digi_free(&aa);
                    break;
                }
#endif // DEBUG
#if 0
                case TEST_FIND_END:
                {
                    if(a.size > 0)
                    {
                        list_digi_it first_a, last_a;
                        list_digi_it aa = list_digi_find_end(&a, &s_first, &s_last);
                        auto bb = find_end(b.begin(), b.end(), ...);
                        bool found_a = !list_digi_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*(aa->value) == *bb->value);
                    }
                    break;
                }
                case TEST_FIND_END_RANGE:
                {
                    list_digi_it first_a, last_a, s_first, s_last;
                    std::list<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = list_digi_find_end_range(&first_a, &last_a, &s_first_a, &s_last_a);
                    auto it = find_end(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    CHECK(a, b);
# endif
                    break;
                }
                case TEST_FIND_END_IF_RANGE:
                {
                    list_digi_it first_a, last_a, s_first, s_last;
                    std::list<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = list_digi_find_end_if_range(&first_a, &last_a, &s_first, &s_last, digi_is_odd);
                    auto it = find_end(first_b, last_b, s_first_b, s_last_b, DIGI_is_odd);
                    CHECK_ITER(first_a, b, it);
                    digi_free (&key); // special
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
        CHECK(a, b);
        list_digi_free(&a);
    }
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
