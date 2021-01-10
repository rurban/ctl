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

int
main(void)
{
    INIT_SRAND;
    int test = -1;
    char *env = getenv ("TEST");
    if (env)
        sscanf(env, "%d", &test);
    size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    if (test >= 0)
        loops = 10;
    for(size_t loop = 0; loop < loops; loop++)
    {
        list_digi a;
        std::list<DIGI> b;
        int max_value = 0;
        setup_lists(&a, b, TEST_RAND(TEST_MAX_SIZE), &max_value);
        enum
        {
            TEST_PUSH_BACK,
            TEST_PUSH_FRONT,
            TEST_POP_BACK,
            TEST_POP_FRONT,
            TEST_ERASE,
            TEST_INSERT,
            TEST_CLEAR,
            TEST_RESIZE,
            TEST_ASSIGN,
            TEST_SWAP,
            TEST_COPY,
            TEST_REVERSE,
            TEST_REMOVE, // 12
#ifdef DEBUG
            TEST_INSERT_COUNT,
            TEST_INSERT_RANGE,
#endif
            TEST_EMPLACE,
            TEST_EMPLACE_FRONT,
            TEST_EMPLACE_BACK,
            TEST_REMOVE_IF,
            TEST_SPLICE,
            TEST_MERGE,
            TEST_EQUAL,
            TEST_SORT,
            TEST_UNIQUE,
            TEST_FIND,
            TEST_TOTAL
        };
        int which = TEST_RAND(TEST_TOTAL);
        if (test >= 0 && test < (int)TEST_TOTAL)
            which = test;
        LOG ("TEST %d\n", which);
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
#ifdef DEBUG
                list_digi_resize(&a, 10, digi_init(0));
                b.resize(10);
#endif
                int vb = *value->value;
                LOG("before remove %d\n", vb);
                print_lst(&a);
                digi copy = digi_init(vb);
                size_t erased_a = list_digi_remove(&a, &copy);
                LOG("removed %zu\n", erased_a);
                print_lst(&a);
                digi_free (&copy);
                // if C++20: size_t only since C++20
                b.remove(b.front());
                LOG("removed STL\n");
                print_list(b);
                CHECK(a, b);
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
#ifdef DEBUG
            case TEST_INSERT_COUNT:
            case TEST_INSERT_RANGE:
            break;
#endif
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
                    int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : test_value;
                    digi key = digi_init(value);
                    list_digi_node* aa = list_digi_find(&a, key);

                    auto bb = std::find(b.begin(), b.end(), DIGI{value});
                    CHECK_ITER(aa, b, bb);
                    digi_free(&key);
                    CHECK(a, b);
                }
                break;
            }
        }
        CHECK(a, b);
        list_digi_free(&a);
    }
    TEST_PASS(__FILE__);
}
