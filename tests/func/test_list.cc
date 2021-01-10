#include "../test.h"
#include "digi.hh"

#define T digi
#include <ctl/list.h>

#include <list>
#include <algorithm>

void print_lst(list_digi *a)
{
    foreach(list_digi, a, it)
        printf ("%d ", *it.ref->value);
    printf ("\n");
}

void print_list(std::list<DIGI> &b)
{
    for(auto& d: b)
        printf ("%d ", *d.value);
    printf ("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE 1000
#else
#define print_lst(x)
#define print_list(x)
#define TEST_MAX_VALUE INT_MAX
#endif

#define CHECK(_x, _y) {                                           \
    assert(_x.size == _y.size());                                 \
    assert(list_digi_empty(&_x) == _y.empty());                   \
    if(_x.size > 0) {                                             \
        assert(*_y.front().value == *list_digi_front(&_x)->value);\
        assert(*_y.back().value == *list_digi_back(&_x)->value);  \
    }                                                             \
    std::list<DIGI>::iterator _iter = _y.begin();                 \
    foreach(list_digi, &_x, _it) {                                \
        assert(*_it.ref->value == *_iter->value);                 \
        _iter++;                                                  \
    }                                                             \
    list_digi_it _it = list_digi_it_each(&_x);                    \
    for(auto& _d : _y) {                                          \
        assert(*_it.ref->value == *_d.value);                     \
        _it.step(&_it);                                           \
    }                                                             \
}

#define CHECK_ITER(_it, b, _iter)                                 \
    if (_it != NULL)                                              \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*_it->value.value == *(*_iter).value);             \
    } else                                                        \
        assert (_iter == b.end())
#define CHECK_ITER_I(_it, b, _iter)                               \
    if (!_it->done)                                               \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*_it->ref->value == *(*_iter).value);              \
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
get_iters (list_digi *a, list_digi_it *first_a, list_digi_it *last_a,
           std::list<DIGI>& b, std::_List_iterator<DIGI>& first_b,
           std::_List_iterator<DIGI>&last_b)
{
    // TODO random index
    list_digi_it it = list_digi_it_iter (a, a->head);
    if (a->size)
    {
        it.step(&it);
        *first_a = it;
        first_b = b.begin();
        first_b++;
    }
    else
        first_b = b.begin();
    it = list_digi_it_iter (a, a->tail);
    it.done = 1;
    *last_a = it;
    last_b = b.end();
}

int
main(void)
{
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    for(size_t loop = 0; loop < loops; loop++)
    {
        list_digi a;
        std::list<DIGI> b;
        int max_value = 0;
        setup_lists(&a, b, TEST_RAND(TEST_MAX_SIZE), &max_value);
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
        TEST(SPLICE) \
        TEST(MERGE) \
        TEST(EQUAL) \
        TEST(SORT) \
        TEST(UNIQUE) \
        TEST(FIND) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE)
#define FOREACH_DEBUG(TEST) \
        TEST(INSERT_COUNT) \
        TEST(INSERT_RANGE) \
        TEST(EQUAL_RANGE) \
        TEST(FIND_RANGE) \
        TEST(COUNT) \
        TEST(COUNT_IF) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE)
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
                size_t current = 0;
                std::list<DIGI>::iterator iter = b.begin();
                foreach(list_digi, &a, it)
                {
                    if(current == index)
                    {
                        list_digi_erase(&a, it.node);
                        b.erase(iter);
                        break;
                    }
                    iter++;
                    current++;
                }
                CHECK(a, b);
                break;
            }
            case TEST_INSERT:
            {
                size_t index = TEST_RAND(a.size);
                int value = TEST_RAND(TEST_MAX_VALUE);
                size_t current = 0;
                std::list<DIGI>::iterator iter = b.begin();
                foreach(list_digi, &a, it)
                {
                    if(current == index)
                    {
                        list_digi_node *node =
                            list_digi_insert(&a, it.node, digi_init(value));
                        std::list<DIGI>::iterator ii =
                            b.insert(iter, DIGI{value});
                        CHECK_ITER(node, b, ii);
                        break;
                    }
                    iter++;
                    current++;
                }
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
                size_t resize = 3 * TEST_RAND(a.size);
                list_digi_resize(&a, resize, digi_init(0));
                b.resize(resize);
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
#ifdef DEBUG
                    list_digi_resize(&a, 10, digi_init(0));
                    b.resize(10);
#endif
                    int vb = *value->value;
                    LOG("before remove %d\n", vb);
                    print_lst(&a);
                    digi copy = digi_init(vb);
#ifdef DEBUG // only used in logging
                    size_t erased_a =
#endif
                        list_digi_remove(&a, &copy);
                    LOG("removed %zu\n", erased_a);
                    print_lst(&a);
                    digi_free (&copy);
                    // if C++20: size_t only since C++20
                    b.remove(b.front());
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
                list_digi_emplace(&a, a.head->next, &aa);
                LOG("CTL emplace head->next %d\n", *aa.value);
                //print_lst(&a);
                auto iter = b.begin();
                b.emplace(++iter, DIGI{value});
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
                b.emplace_front(DIGI{value});
                CHECK(a, b);
                digi_free(&aa);
                break;
            }
            case TEST_EMPLACE_BACK:
            {
                int value = TEST_RAND(TEST_MAX_VALUE);
                digi aa = digi_init(value);
                list_digi_emplace_back(&a, &aa);
                b.emplace_back(DIGI{value});
                CHECK(a, b);
                digi_free(&aa);
                break;
            }
            case TEST_REMOVE_IF:
            {
                list_digi_remove_if(&a, digi_is_odd);
                b.remove_if(DIGI_is_odd);
                CHECK(a, b);
                break;
            }
            case TEST_SPLICE:
            {
                size_t index = TEST_RAND(a.size);
                size_t current = 0;
                std::list<DIGI>::iterator iter = b.begin();
                list_digi_it it = list_digi_it_each(&a);
                while(!it.done)
                {
                    if(current == index)
                        break;
                    iter++;
                    current++;
                    it.step(&it);
                }
                list_digi aa;
                std::list<DIGI> bb;
                setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                b.splice(iter, bb);
                list_digi_splice(&a, it.node, &aa);
                CHECK(a, b);
                break;
            }
            case TEST_MERGE:
            {
                list_digi aa = list_digi_init();
                std::list<DIGI> bb;
                size_t size = TEST_RAND(TEST_MAX_SIZE);
                int total = 0;
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    int value = TEST_RAND(128);
                    total += value;
                    if(pushes == (size - 1))
                        total = max_value + 1; // MAX + 1 ENSURES MERGE CAN APPEND TO TAIL.
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
                if(a.size > 0)
                {
                    const size_t index = TEST_RAND(a.size);
                    int test_value = 0;
                    size_t current = 0;
                    foreach(list_digi, &a, it)
                    {
                        if(current == index)
                        {
                            test_value = *it.ref->value;
                            break;
                        }
                        current++;
                    }
                    int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                             : test_value;
                    digi key = digi_init(value);
                    list_digi_node* aa = list_digi_find(&a, key);

                    auto bb = std::find(b.begin(), b.end(), DIGI{value});
                    CHECK_ITER(aa, b, bb);
                    digi_free(&key);
                    CHECK(a, b);
                }
                break;
            }
           case TEST_ALL_OF:
            {
                bool aa = list_digi_all_of(&a, digi_is_odd);
                bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF:
            {
                bool aa = list_digi_all_of(&a, digi_is_odd);
                bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF:
            {
                bool aa = list_digi_all_of(&a, digi_is_odd);
                bool bb = all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_ALL_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_all_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = all_of(first_b, last_b, DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_ANY_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_any_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = any_of(first_b, last_b, DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_NONE_OF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_none_of_range(&first_a, &last_a,
                                                 digi_is_odd);
                bool bb = none_of(first_b, last_b, DIGI_is_odd);
                assert(aa == bb);
                break;
            }
            case TEST_FIND_IF:
            {
                list_digi_node *n = list_digi_find_if(&a, digi_is_odd);
                auto it = find_if(b.begin(), b.end(), DIGI_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_IF_NOT:
            {
                list_digi_node *n = list_digi_find_if_not(&a, digi_is_odd);
                auto it = find_if_not(b.begin(), b.end(), DIGI_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_IF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_node *n =
                    list_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                auto it = find_if(first_b, last_b, DIGI_is_odd);
                print_lst(&a);
                print_list(b);
                CHECK_ITER(n, b, it);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                list_digi_node *n =
                    list_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                auto it = find_if_not(first_b, last_b, DIGI_is_odd);
                CHECK_ITER(n, b, it);
                break;
            }
#ifdef DEBUG
            case TEST_EQUAL_RANGE:
            {
                /*
                int vb = TEST_RAND(TEST_MAX_VALUE);
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                LOG("EQUAL_RANGE\n");
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                bool aa = list_digi_equal_range(&first_a, &last_a,
                                                digi_init(vb));
                bool bb = equal_range(first_b, last_b, vb);
                assert(aa == bb);
                */
                break;
            }
            case TEST_COUNT:
            {
                int test_value = 0;
                int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                     : test_value;
                LOG("COUNT\n");
                size_t numa = list_digi_count(&a, digi_init(v));
                size_t numb = count(b.begin(), b.end(), DIGI{v});
                assert(numa == numb);
                break;
            }
            case TEST_COUNT_IF:
            {
                LOG("COUNT_IF\n");
                size_t numa = list_digi_count_if(&a, digi_is_odd);
                size_t numb = count_if(b.begin(), b.end(), DIGI_is_odd);
                assert(numa == numb);
                break;
            }
            case TEST_COUNT_RANGE:
            {
                int test_value = 0;
                int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                     : test_value;
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                LOG("COUNT_IF_RANGE\n");
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = list_digi_count_range(&first_a, &last_a,
                                                    digi_init(v));
                size_t numb = count(first_b, last_b, DIGI{v});
                assert(numa == numb);
                break;
            }
            case TEST_COUNT_IF_RANGE:
            {
                list_digi_it first_a, last_a;
                std::_List_iterator<DIGI> first_b, last_b;
                LOG("COUNT_IF_RANGE\n");
                get_iters (&a, &first_a, &last_a, b, first_b, last_b);
                size_t numa = list_digi_count_if_range(&first_a, &last_a,
                                                        digi_is_odd);
                size_t numb = count_if(first_b, last_b, DIGI_is_odd);
                assert(numa == numb);
                break;
            }
#endif
        }
        CHECK(a, b);
        list_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
