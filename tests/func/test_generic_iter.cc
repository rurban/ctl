#include "../test.h"

/* generate lists out of various containers */
// pick one to be the target container
// pick another to be the 2nd range

#define POD
#define T int
#include <ctl/list.h>
#define POD
#define T int
#define N 25
#include <ctl/array.h>
#define POD
#define T int
#include <ctl/deque.h>
#define POD
#define T int
#include <ctl/set.h>
#define POD
#define T int
#include <ctl/vector.h>
#define POD
#define T int
#include <ctl/unordered_set.h>

typedef enum types_t
{
    CTL_VECTOR,
    CTL_ARRAY,
    CTL_DEQUE,
    CTL_LIST,
    CTL_SET,
    CTL_USET /* 5 */
} types_t;
static const types_t types[] = {CTL_VECTOR, CTL_ARRAY, CTL_DEQUE, CTL_LIST, CTL_SET, CTL_USET};

#include <vector>
#include <array>
#include <deque>
#include <list>
#include <set>
#include <unordered_set>
#include <algorithm>

types_t pick_type(void) {
    const int LEN = len(types);
    return types[TEST_RAND(LEN)];
}

void print_lst(list_int *a)
{
    list_foreach_ref(list_int, a, it) printf("%d, ", *it.ref);
    printf("\n====\n");
}

void print_list(std::list<int> &b)
{
    for (auto &d : b)
        printf("%d, ", d);
    printf("\n----\n");
}

#define print_vec(x)
#define print_lst_range(x)
#define print_set(x)
#define print_uset(x)

#ifdef DEBUG
#define TEST_MAX_VALUE 15
#ifndef LONG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 10
#endif
#else
#define print_lst(x)
#define print_list(x)
#define TEST_MAX_VALUE 1500
#endif

#define CHECK(ty1, cppty, _x, _y)                                                                                      \
    {                                                                                                                  \
        assert(_x.size == _y.size());                                                                                  \
        assert(ty1##_int_empty(&_x) == _y.empty());                                                                    \
        std::cppty::iterator _iter = _y.begin();                                                                       \
        int i = 0;                                                                                                     \
        foreach(ty1##_int, &_x, _it)                                                                                   \
        {                                                                                                              \
            LOG("%d: %d, ", i, *_it.ref);                                                                              \
            assert(*_it.ref == *_iter);                                                                                \
            i++;                                                                                                       \
            _iter++;                                                                                                   \
        }                                                                                                              \
        LOG("\n");                                                                                                     \
        ty1##_int_it _it = ty1##_int_begin(&_x);                                                                       \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_it.ref == _d);                                                                                    \
            ty1##_int_it_next(&_it);                                                                                   \
        }                                                                                                              \
    }

#define LOG_ITER(_it, b, _iter, line)                                                                                  \
    if ((_it)->node != NULL)                                                                                           \
    {                                                                                                                  \
        if (_iter == b.end())                                                                                          \
            printf("STL iter at end, line %u FAIL\n", line);                                                           \
        if (*((_it)->ref) != *(*_iter).value)                                                                          \
            printf("iter %d vs %d, line %u FAIL\n", *((_it)->ref), *(*_iter).value, line);                             \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if (!list_int_it_done(&_it))                                                                                       \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!list_int_it_done(&_it))                                                                                       \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

#define SETUP_LIST1                                                                                                    \
    list_int a = list_int_init();                                                                                      \
    std::list<int> b;                                                                                                  \
    for (int i = 0; i < (int)TEST_RAND(TEST_MAX_SIZE); i++)             \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        list_int_push_back(&a, vb);                                                                                    \
        b.push_back(vb);                                                                                               \
    }                                                                                                                  \
    print_lst(&a)

#define SETUP_LIST2                                                                                                    \
    list_int aa = list_int_init();                                                                                     \
    std::list<int> bb;                                                                                                 \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        list_int_push_back(&aa, vb);                                                                                   \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    list_int_it range2 = list_int_begin(&aa);                                                                          \
    print_lst(&aa)

#define SETUP_VEC1                                                                                                     \
    vec_int a = vec_int_init();                                                                                        \
    std::vector<int> b;                                                                                                \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        vec_int_push_back(&a, vb);                                                                                     \
        b.push_back(vb);                                                                                               \
    }
#define SETUP_VEC2                                                                                                     \
    vec_int aa = vec_int_init();                                                                                       \
    std::vector<int> bb;                                                                                               \
    for (int i = 0; i < TEST_RAND(a.size); i++)                                                                        \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        vec_int_push_back(&aa, vb);                                                                                    \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    vec_int_it range2 = vec_int_begin(&aa)

#define SETUP_ARR1                                                                                                     \
    arr25_int a = arr25_int_init();                                                                                    \
    std::array<int, 25> b;                                                                                             \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        a.vector[i] = vb;                                                                                              \
        b[i] = vb;                                                                                                     \
    }
#define SETUP_ARR2                                                                                                     \
    arr25_int aa = arr25_int_init();                                                                                   \
    std::array<int, 25> bb;                                                                                            \
    for (int i = 0; i < TEST_RAND(a.size); i++)                                                                        \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        aa.vector[i] = vb;                                                                                             \
        bb[i] = vb;                                                                                                    \
    }                                                                                                                  \
    arr25_int_it range2 = arr25_int_begin(&aa)

#define SETUP_DEQ1                                                                                                     \
    deq_int a = deq_int_init();                                                                                        \
    std::deque<int> b;                                                                                                \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        deq_int_push_back(&a, vb);                                                                                      \
        b.push_back(vb);                                                                                               \
    }
#define SETUP_DEQ2                                                                                                     \
    deq_int aa = deq_int_init();                                                                                       \
    std::deque<int> bb;                                                                                               \
    for (int i = 0; i < TEST_RAND(a.size); i++)                                                                        \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        deq_int_push_back(&aa, vb);                                                                                     \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    deq_int_it range2 = deq_int_begin(&aa)

#define SETUP_SET1                                                                                                     \
    set_int a = set_int_init(NULL);                                                                                    \
    std::set<int> b;                                                                                                   \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        set_int_insert(&a, vb);                                                                                        \
        b.insert(vb);                                                                                                  \
    }                                                                                                                  \
    print_set(&a)
#define SETUP_SET2                                                                                                     \
    set_int aa = set_int_init(NULL);                                                                                   \
    std::set<int> bb;                                                                                                  \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        set_int_insert(&aa, vb);                                                                                       \
        bb.insert(vb);                                                                                                 \
    }                                                                                                                  \
    set_int_it range2 = set_int_begin(&aa);                                                                            \
    print_set(&aa)

#define SETUP_USET1                                                                                                    \
    uset_int a = uset_int_init(NULL, NULL);                                                                            \
    std::unordered_set<int> b;                                                                                         \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        uset_int_insert(&a, vb);                                                                                       \
        b.insert(vb);                                                                                                  \
    }                                                                                                                  \
    print_uset(&a)
#define SETUP_USET2                                                                                                    \
    uset_int aa = uset_int_init(NULL, NULL);                                                                           \
    std::unordered_set<int> bb;                                                                                        \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        const int vb = TEST_RAND(TEST_MAX_VALUE);                                                                      \
        uset_int_insert(&aa, vb);                                                                                      \
        bb.insert(vb);                                                                                                 \
    }                                                                                                                  \
    uset_int_it range2 = uset_int_begin(&aa);                                                                          \
    print_uset(&aa)

int main(void)
    {
        int errors = 0;
        INIT_SRAND;
        INIT_TEST_LOOPS(10);
        for (size_t loop = 0; loop < loops; loop++)
        {
            const types_t t1 = pick_type();
            LOG("main type: %d, ", t1);
            const types_t t2 = pick_type();
            LOG("2nd type: %d\n", t2);

#define FOREACH_METH(TEST)                                                                                             \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(DIFFERENCE_RANGE)                                                                                             \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(MISMATCH)                                                                                                     \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(SEARCH_N_RANGE)                                                                                               \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END_RANGE)                                                                                               \
    TEST(MERGE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(ERASE_GENERIC)                                                                                                \

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

        enum
        {
            FOREACH_METH(GENERATE_ENUM)
#ifdef DEBUG
            FOREACH_DEBUG(GENERATE_ENUM)
#endif
            TEST_TOTAL
        };
#ifdef DEBUG
        static const char *test_names[] = {FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif
        int which = TEST_RAND(TEST_TOTAL);
        if (test >= 0 && test < (int)TEST_TOTAL)
            which = test;
        LOG("TEST %s %d (size %zu)\n", test_names[which], which, a.size);
        switch (which)
        {
#ifdef DEBUG
        case TEST_INSERT_GENERIC:

#define INSERT_INTO(ty2, ty1, cppty)                                                                                   \
    LOG("insert " #ty2 " into " #ty1 "\n");                                                                            \
    b.insert(b.begin(), bb.begin(), bb.end());                                                                         \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int_insert_generic(&begin, (ty1##_int_it *)&range2);                                                         \
    CHECK(ty1, cppty, a, b);                                                                                           \
    ty2##_int_free(&aa)

            switch (t1)
            {
            case CTL_VECTOR : {
                SETUP_VEC1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, vec, vector<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, vec, vector<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, vec, vector<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, vec, vector<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, vec, vector<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, vec, vector<int>); break;
                }
                } // switch t2
                vec_int_free(&a); break;
            }
            case CTL_ARRAY : {
                SETUP_ARR1;
                switch (t2)
                {
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, arr25, array<int,25>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, arr25, array<int,25>); break;
                }
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, arr25, array<int,25>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, arr25, array<int,25>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, arr25, array<int,25>); break;
                }
                } // switch t2
                arr25_int_free(&a); break;
            }
            case CTL_DEQUE : {
                SETUP_DEQ1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, deq, deque<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, deq, deque<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, deq, deque<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, deq, deque<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, deq, deque<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, deq, deque<int>); break;
                }
                } // switch t2
                deq_int_free(&a); break;
            }
            case CTL_LIST : {
                SETUP_LIST1;
                switch (t2)
                {
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, list, list<int>); break;
                }
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, list, list<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, list, list<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, list, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, list, list<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, list, list<int>); break;
                }
                } // switch t2
                list_int_free(&a); break;
            }
            case CTL_SET : {
                SETUP_SET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, set, set<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, set, set<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, set, set<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, set, set<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, set, set<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, set, set<int>); break;
                }
                } // switch t2
                list_int_free(&a); break;
            }
            case CTL_USET : {
                SETUP_USET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, uset); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; INSERT_INTO(arr25, uset); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, uset); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, uset); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, uset); break;
                }
                case CTL_USET : {
                    SETUP_USET2; INSERT_INTO(uset, uset); break;
                }
                } // switch t2
                uset_int_free(&a); break;
            }
            } // switch t1
            break;

        case TEST_ERASE_GENERIC:

#define ERASE_FROM(ty2, ty1, cppty)                                                                                    \
    LOG("erase " #ty2 " from " #ty1 "\n");                                                                             \
    b.erase(bb.begin(), bb.end());                                                                                     \
    ty1##_int_erase_generic(&a, (ty1##_int_it *)&range2);                                                              \
    CHECK(ty1, cppty, a, b);                                                                                           \
    ty2##_int_free(&aa)

            switch (t1)
            {
            case CTL_VECTOR : {
                SETUP_VEC1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ERASE_FROM(vec, vec, vector<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ERASE_FROM(arr25, vec, vector<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ERASE_FROM(deq, vec, vector<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ERASE_FROM(vec, vector, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ERASE_FROM(set, vec, vector<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; ERASE_FROM(uset, vec, vector<int>); break;
                }
                } // switch t2
                vec_int_free(&a); break;
            }
            // cannot erase from array
            case CTL_ARRAY : break;
            case CTL_DEQUE : {
                SETUP_DEQ1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ERASE_FROM(vec, deq, deque<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ERASE_FROM(arr25, deq, deque<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ERASE_FROM(deq, deq, deque<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ERASE_FROM(deq, deque, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ERASE_FROM(set, deq, deque<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; ERASE_FROM(uset, deq, deque<int>); break;
                }
                } // switch t2
                deq_int_free(&a); break;
            }
            case CTL_LIST : {
                SETUP_LIST1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ERASE_FROM(vec, list, list<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ERASE_FROM(arr25, list, list<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ERASE_FROM(deq, list, list<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ERASE_FROM(list, list, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ERASE_FROM(set, list, list<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; ERASE_FROM(uset, list, list<int>); break;
                }
                } // switch t2
                list_int_free(&a); break;
            }     // LIST
            case CTL_SET : {
                SETUP_SET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ERASE_FROM(vec, set, set<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ERASE_FROM(arr25, set, set<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ERASE_FROM(deq, set, set<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ERASE_FROM(set, set, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ERASE_FROM(set, set, set<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; ERASE_FROM(uset, set, set<int>); break;
                }
                } // switch t2
                set_int_free(&a); break;
            }
            case CTL_USET : {
                SETUP_USET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ERASE_FROM(vec, uset, unordered_set<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ERASE_FROM(arr25, uset, unordered_set<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ERASE_FROM(deq, uset, unordered_set<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ERASE_FROM(uset, unordered_set, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ERASE_FROM(set, uset, unordered_set<int>); break;
                }
                case CTL_USET : {
                    SETUP_USET2; ERASE_FROM(uset, uset, unordered_set<int>); break;
                }
                } // switch t2
                uset_int_free(&a); break;
            }
            }
            break;
#endif
            case TEST_MERGE_RANGE:

#ifndef _MSC_VER
#define MERGE_INTO(ty2, ty1, cppty)                                                                                    \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    std::cppty bbb;                                                                                                    \
    merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                                          \
    CHECK(ty1, cppty, aaa, bbb);                                                                                       \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define MERGE_INTO_SET(ty2, ty1, cppty)                                                                                \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    std::cppty bbb;                                                                                                    \
    merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));                                  \
    CHECK(ty1, cppty, aaa, bbb);                                                                                       \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define MERGE_INTO(ty2, ty1, cppty)                                                                                    \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define MERGE_INTO_SET(ty2, ty1, cppty)  MERGE_INTO(ty2, ty1, cppty)
#endif

                switch (t1)
                {
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_LIST : {
                        SETUP_LIST2;
                        LOG("merge list into list\n");
                        list_int_it begin = list_int_begin(&a);
                        list_int aaa = list_int_merge_range(&begin, &range2);
                        b.merge(bb);
                        CHECK(list, list<int>, aaa, b);
                        list_int_free(&aa);
                        list_int_free(&aaa);
                        break;
                    }
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO(deq, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SET(set, list, list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO_SET(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                } // LIST
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MERGE_INTO(list, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO(set, vec, vector<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a);
                } // VECTOR
                // cannot merge into array
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO(arr25, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MERGE_INTO(list, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO(deq, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO(set, deq, deque<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO(uset, deq, deque<int>); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO_SET(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO_SET(arr25, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MERGE_INTO_SET(list, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO_SET(deq, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
                // uset_merge_range not yet implemented
                case CTL_USET : break;
/* TODO
                case CTL_USET : {
                    SETUP_USET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO_SET(vec, uset, unordered_set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO_SET(arr25, uset, unordered_set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MERGE_INTO_SET(list, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a);
                }
*/
                } // switch t1
                break;

#if 0
            case TEST_INCLUDES_RANGE: {
                SETUP_LIST1;
                SETUP_LIST2;
                list_int_it begin = list_int_begin(&a);
                bool a_found = list_int_includes_range(&begin, &range2);
                bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                assert(a_found == b_found);
                CHECK(aa, bb);
                list_int_free(&aa);
                list_int_free(&a);
                break;
            }
            case TEST_UNION_RANGE: {
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_int_sort(&a);
                list_int_sort(&aa);
                b.sort();
                bb.sort();
                list_int_it first_a1;
                std::list<int>::iterator first_b1, last_b1;
                list_int_it first_a2;
                std::list<int>::iterator first_b2, last_b2;

                LOG("CTL a + aa\n");
                print_lst_range(first_a1);
                print_lst_range(first_a2);
                list_int aaa = list_int_union_range(&first_a1, &first_a2);
                LOG("CTL => aaa\n");
                print_lst(&aaa);

                std::list<int> bbb;
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
                list_int_free(&aaa);
                list_int_free(&aa);
                break;
            }
            case TEST_INTERSECTION_RANGE: {
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_int_sort(&a);
                list_int_sort(&aa);
                b.sort();
                bb.sort();
                list_int_it first_a1;
                std::list<int>::iterator first_b1, last_b1;
                list_int_it first_a2;
                std::list<int>::iterator first_b2, last_b2;

                LOG("CTL a + aa\n");
                print_lst_range(first_a1);
                print_lst_range(first_a2);
                list_int aaa = list_int_intersection_range(&first_a1, &first_a2);
                LOG("CTL => aaa\n");
                print_lst(&aaa);

                std::list<int> bbb;
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
                list_int_free(&aaa);
                list_int_free(&aa);
                break;
            }
            case TEST_DIFFERENCE_RANGE: {
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_int_sort(&a);
                list_int_sort(&aa);
                b.sort();
                bb.sort();
                list_int_it first_a1;
                std::list<int>::iterator first_b1, last_b1;
                list_int_it first_a2;
                std::list<int>::iterator first_b2, last_b2;

                LOG("CTL a + aa\n");
                print_lst_range(first_a1);
                print_lst_range(first_a2);
                list_int aaa = list_int_difference_range(&first_a1, &first_a2);
                LOG("CTL => aaa\n");
                print_lst(&aaa);

                std::list<int> bbb;
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
                list_int_free(&aaa);
                list_int_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(TEST_MAX_SIZE), NULL);
                list_int_sort(&a);
                list_int_sort(&aa);
                b.sort();
                bb.sort();
                list_int_it first_a1;
                std::list<int>::iterator first_b1, last_b1;
                list_int_it first_a2;
                std::list<int>::iterator first_b2, last_b2;

                LOG("CTL a + aa\n");
                print_lst_range(first_a1);
                print_lst_range(first_a2);
                list_int aaa = list_int_symmetric_difference_range(&first_a1, &first_a2);
                LOG("CTL => aaa\n");
                print_lst(&aaa);

                std::list<int> bbb;
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
                list_int_free(&aaa);
                list_int_free(&aa);
                break;
            }
            case TEST_EQUAL_RANGE: {
                list_int aa = list_int_copy(&a);
                std::list<int> bb = b;
                list_int_it r1a, r2a;
                std::list<int>::iterator r1b, last1_b, r2b, last2_b;
                bool same_a = list_int_equal_range(&r1a, &r2a);
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
                list_int_free(&aa);
                break;
            }
            case TEST_MISMATCH: {
                if (a.size < 2)
                    break;
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(a.size), NULL);
                list_int_it b1, b2;
                b1 = list_int_begin(&a);
                b2 = list_int_begin(&aa);
                list_int_it r1a, r2a;
                std::list<int>::iterator r1b, last1_b, r2b, last2_b;
                /*bool found_a = */ list_int_mismatch(&r1a, &r2a);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
#else
                if (!bb.size() || !distance(r2b, last2_b))
                {
                    printf("skip std::mismatch with empty 2nd range. use C++14\n");
                    list_int_free(&aa);
                    break;
                }
                auto pair = std::mismatch(r1b, last1_b, r2b);
#endif
                int d1a = list_int_it_distance(&b1, &r1a);
                int d2a = list_int_it_distance(&b2, &r2a);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                // TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                list_int_free(&aa);
                break;
            }
            case TEST_SEARCH_RANGE: {
                list_int aa = list_int_copy(&a);
                std::list<int> bb = b;
                list_int_it needle, range;
                std::list<int>::iterator first_b, last_b;
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    if (needle.node)
                        needle.node = 0;
                    *first_b = 0;
                }
                // print_list_range(needle);
                range = list_int_begin(&a);
                bool found = list_int_search_range(&range, &needle);
                auto iter = search(b.begin(), b.end(), first_b, last_b);
                LOG("found a: %s\n", found ? "yes" : "no");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                assert(found == !list_int_it_done(&range));
                CHECK_RANGE(range, iter, b.end());
                list_int_free(&aa);
                break;
            }
            case TEST_FIND_FIRST_OF_RANGE: {
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(5), NULL);
                list_int_it first_a, s_first;
                std::list<int>::iterator first_b, last_b, s_first_b, s_last_b;

                bool found_a = list_int_find_first_of_range(&first_a, &s_first);
                auto it = std::find_first_of(first_b, last_b, s_first_b, s_last_b);
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", it != last_b ? "yes" : "no",
                    list_int_it_index(&first_a), distance(b.begin(), it));
                if (found_a)
                    assert(it != last_b);
                else
                    assert(it == last_b);
                // CHECK_RANGE(first_a, it, last_b);
                list_int_free(&aa);
                break;
            }
            case TEST_FIND_END_RANGE: {
                list_int_it first_a, s_first;
                std::list<int>::iterator first_b, last_b;
                list_int aa;
                std::list<int> bb;
                //setup_lists(&aa, bb, TEST_RAND(4), NULL);
                print_lst(&aa);
                s_first = list_int_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
            first_a = list_int_find_end_range(&first_a, &s_first);
            auto it = std::find_end(first_b, last_b, bb.begin(), bb.end());
            CHECK_RANGE(first_a, it, last_b);
#endif
            list_int_free(&aa);
            break;
        }
#endif

        default:
#ifdef DEBUG
            printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
    }
    if (errors)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
