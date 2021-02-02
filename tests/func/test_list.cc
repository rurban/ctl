#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/list.h>

#include <list>
#include <algorithm>

void print_lst(list_digi *a)
{
    int i = 0;
    list_foreach_ref(list_digi, a, it)
        printf ("%d: %d\n", i++, *it.ref->value);
    printf ("\n");
}

void print_list(std::list<DIGI> &b)
{
    int i = 0;
    for(auto& d: b)
        printf ("%d: %d\n", i++, *d.value);
    printf ("\n");
}

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

#define LOG_ITER(_it, b, _iter)                                   \
    if ((_it)->node != NULL)                                      \
    {                                                             \
        if (_iter == b.end())                                     \
            printf("STL iter at end FAIL\n");                     \
        if (*(_it)->ref->value != *(*_iter).value)                \
            printf("iter %d vs %d FAIL\n", *(_it)->ref->value,    \
                *(*_iter).value);                                 \
    } else                                                        \
        assert (_iter == b.end())
#define CHECK_ITER(_it, b, _iter)                                 \
    if ((_it)->node != NULL)                                      \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*(_it)->ref->value == *(*_iter).value);            \
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
        TEST(INSERT) \
        TEST(CLEAR) \
        TEST(RESIZE) \
        TEST(ASSIGN) \
        TEST(SWAP) \
        TEST(COPY) \
        TEST(REVERSE) \
        TEST(REMOVE) \
        TEST(EMPLACE) \
        TEST(EMPLACE_FRONT) \
        TEST(EMPLACE_BACK) \
        TEST(REMOVE_IF) \
        TEST(ERASE_IF) \
        TEST(SPLICE) \
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
        TEST(INSERT_COUNT) \

#define FOREACH_DEBUG(TEST) \
        TEST(SPLICE_IT) \
        TEST(SPLICE_RANGE) \
        TEST(INSERT_RANGE) \
        TEST(EQUAL_RANGE) \

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
                size_t index = TEST_RAND(a.size);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
                list_digi_erase(&it);
                b.erase(iter);
                CHECK(a, b);
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
                // insert libstc++ seems to violate the specs, as insert_range
                LOG_ITER(aa, b, bb);
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
#if __cpp_lib_erase_if > 202002L
                    size_t erased_a = list_digi_remove(&a, digi_init(vb));
                    LOG("removed %zu\n", erased_a);
#else
                    list_digi_remove(&a, digi_init(vb));
#endif
                    print_lst(&a);
#if __cpp_lib_erase_if > 202002L
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
#if __cplusplus >= 201100
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
#if __cplusplus >= 201100
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
#if __cplusplus >= 201100
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
#if __cpp_lib_erase_if > 202002L
                size_t num_a = list_digi_erase_if(&a, digi_is_odd);
                size_t num_b = b.erase_if(DIGI_is_odd);
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
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                b.splice(iter, bb);
                list_digi_splice(&it, &aa);
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
                CHECK_ITER(&aa, b, bb);
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
                CHECK_ITER(&aa, b, bb);
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
                CHECK_ITER(&aa, b, bb);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                list_digi_it aa = list_digi_find_if_not(&a, digi_is_odd);
                auto bb = find_if_not(b.begin(), b.end(), DIGI_is_odd);
                CHECK_ITER(&aa, b, bb);
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
                CHECK_ITER(&aa, b, bb);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                list_digi_it first_a, last_a;
                std::list<DIGI>::iterator first_b, last_b;
                get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_it aa = list_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto bb = find_if_not(first_b, last_b, DIGI_is_odd);
                CHECK_ITER(&aa, b, bb);
                break;
            }
            case TEST_INSERT_COUNT:
            {
                size_t index = TEST_RAND(a.size);
                size_t count = TEST_RAND(a.size - 4) + 1;
                int value = TEST_RAND(TEST_MAX_VALUE);
                std::list<DIGI>::iterator iter = b.begin();
                std::advance(iter, index);
                list_digi_it it = list_digi_begin(&a);
                list_digi_it_advance (&it, index);
                LOG("insert %zu x %d at %zu\n", count, value, index);
                list_digi_it *aa = list_digi_insert_count(&it, count, digi_init(value));
                // libstc++ violates the docs
                std::list<DIGI>::iterator bb = b.insert(iter, count, DIGI{value});
                LOG_ITER(aa, b, bb);
                print_lst(&a);
                print_list(b);
                CHECK(a, b);
                break;
            }
            case TEST_NONE_OF:
            {
                bool is_a = list_digi_none_of(&a, digi_is_odd);
                bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                assert(is_a == is_b);
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
#ifdef DEBUG
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
                std::list<DIGI>::iterator bbpos = bb.begin();
                std::advance(bbpos, bsize / 2);
                list_digi_it aapos = list_digi_begin(&aa);
                list_digi_it_advance(&aapos, bsize / 2);

                b.splice(iter, bb, bbpos);
                list_digi_splice_it(&it, &aapos);
                CHECK(a, b);
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

                b.splice(iter, bb, bbpos, bbend);
                list_digi_splice_range(&it, &aapos, &aaend);
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_RANGE:
            // algorithms + ranges
                break;
            case TEST_ANY_OF:
            {
                bool aa = list_digi_all_of(&a, digi_is_odd);
                bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
                if (aa != bb)
                {
                    print_lst(&a);
                    print_list(b);
                    printf ("%d != %d is_odd FAIL\n", (int)aa, (int)bb);
                    errors++;
                }
                //assert(aa == bb);
                break;
            }
            case TEST_EQUAL_RANGE:
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
        }
        CHECK(a, b);
        list_digi_free(&a);
    }
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
