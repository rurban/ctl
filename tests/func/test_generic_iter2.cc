#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

/* generate lists out of various containers */
// pick one to be the target container
// pick another to be the 2nd range

#define POD
#define T int
#include <ctl/list.h>
#define POD
#define T int
#include <ctl/forward_list.h>
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

#define FOREACH_METH(TEST)                                                                                             \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END_RANGE)
#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(DIFFERENCE_RANGE)

// over in iter
#define FOREACH_METH1(TEST)                                                                                            \
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(MISMATCH)                                                                                                     \
    TEST(LEXICOGRAPHICAL_COMPARE)
#define FOREACH_DEBUG1(TEST)                                                                                           \
    //TEST(REMOVE_GENERIC)
    //TEST(COPY_GENERIC)

#include "./test_generic_iter.h"

int main(void)
{
    int fail = 0;
    const union gen_cov_u max_w = { .u = { .w1 = TEST_TOTAL, .t1 = CTL_USET, .t2 = CTL_USET } };
    INIT_SRAND;
    INIT_TEST_LOOPS(10, true);
    vec_u16_resize(&covvec, max_w.w, 0); // 5 types, ff methods
    for (unsigned loop = 0; loop < loops; loop++)
    {
        types_t t1, t2;
        int which;
        union gen_cov_u wu;
        if (!tests.size) // random testing
        {
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
            t1 = pick_type();
            t2 = pick_type();
            LOG("main type: %d, 2nd type: %d\n", t1, t2);
            wu.u.w1 = which;
            wu.u.t1 = t1;
            wu.u.t2 = t2;
        }
        else // or work the test queue
        {
            which = *queue_int_front(&tests);
            queue_int_pop(&tests);
            wu.w = which;
            t1 = (types_t)wu.u.t1;
            t2 = (types_t)wu.u.t2;
            //if (!t1 && !t2)
            //{
            //    wu.u.t1 = t1 = pick_type();
            //    wu.u.t2 = t2 = pick_type();
            //}
            which = wu.u.w1;
        }
        LOG("TEST %s %d (0x%x)\n", test_names[which], which, (unsigned)wu.w);
        assert(wu.w < covvec.size);
        covvec.vector[wu.w]++;
        switch (which)
        {
            
        case TEST_UNION_RANGE:

#ifndef _MSC_VER
#define UNION_RANGE_SET(ty2, ty1, cppty)                                                                               \
    LOG("union " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_union_range(&begin, (ty1##_int_it *)&range2);                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));                         \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define UNION_RANGE_SLIST(ty2, ty1, cppty)                                                                             \
    LOG("union " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_union_range(&begin, (ty1##_int_it *)&range2);                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));                                \
    CHECK_SLIST(ty1, ty2, cppty, aaa, bbb);                                                                            \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define UNION_RANGE(ty2, ty1, cppty)                                                                                   \
    LOG("union " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_union_range(&begin, (ty1##_int_it *)&range2);                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                                 \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define UNION_RANGE(ty2, ty1, cppty)                                                                                   \
    LOG("union " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_union_range(&begin, (ty1##_int_it *)&range2);                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define UNION_RANGE_SET(ty2, ty1, cppty) UNION_RANGE(ty2, ty1, cppty)
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE(uset, deq, deque<int>); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE_SLIST(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE_SLIST(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE_SLIST(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE_SLIST(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE_SLIST(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE_SLIST(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE_SLIST(uset, slist, forward_list<int>); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE_SET(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE_SET(arr25, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE_SET(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE_SET(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE_SET(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : {
                    SETUP_USET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; UNION_RANGE_SET(vec, uset, unordered_set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; UNION_RANGE_SET(arr25, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; UNION_RANGE_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; UNION_RANGE_SET(list, uset, unordered_set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; UNION_RANGE_SET(slist, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; UNION_RANGE_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; UNION_RANGE_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a); break;
                }
                } // switch t1
                break;

            case TEST_INTERSECTION_RANGE:

#ifndef _MSC_VER
#define INTERSECTION_RANGE_SET(ty2, ty1, cppty)                                                                        \
    LOG("intersection " #ty2 " with " #ty1 "\n");                                                                      \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_intersection_range(&begin, (ty1##_int_it *)&range2);                                     \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));                  \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define INTERSECTION_RANGE_SLIST(ty2, ty1, cppty)                                                                      \
    LOG("intersection " #ty2 " with " #ty1 "\n");                                                                      \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_intersection_range(&begin, (ty1##_int_it *)&range2);                                     \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));                         \
    CHECK_SLIST(ty1, ty2, cppty, aaa, bbb);                                                                            \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define INTERSECTION_RANGE(ty2, ty1, cppty)                                                                            \
    LOG("intersection " #ty2 " with " #ty1 "\n");                                                                      \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_intersection_range(&begin, (ty1##_int_it *)&range2);                                     \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                          \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define INTERSECTION_RANGE(ty2, ty1, cppty)                                                                            \
    LOG("intersection " #ty2 " with " #ty1 "\n");                                                                      \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_intersection_range(&begin, (ty1##_int_it *)&range2);                                     \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define INTERSECTION_RANGE_SET(ty2, ty1, cppty) INTERSECTION_RANGE(ty2, ty1, cppty)
#define INTERSECTION_RANGE_SLIST(ty2, ty1, cppty) INTERSECTION_RANGE(ty2, ty1, cppty)
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INTERSECTION_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INTERSECTION_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE(uset, deq, deque<int>); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INTERSECTION_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE_SLIST(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INTERSECTION_RANGE_SLIST(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE_SLIST(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE_SLIST(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE_SLIST(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE_SLIST(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE_SLIST(uset, slist, forward_list<int>); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE_SET(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
#ifdef DEBUG
                        SETUP_ARR2; INTERSECTION_RANGE_SET(arr25, set, set<int>);
#endif
                        break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE_SET(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE_SET(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE_SET(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : {
                    SETUP_USET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INTERSECTION_RANGE_SET(vec, uset, unordered_set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INTERSECTION_RANGE_SET(arr25, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INTERSECTION_RANGE_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INTERSECTION_RANGE_SET(list, uset, unordered_set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INTERSECTION_RANGE_SET(slist, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INTERSECTION_RANGE_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INTERSECTION_RANGE_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a); break;
                }
                } // switch t1
                break;

            case TEST_SYMMETRIC_DIFFERENCE_RANGE:

#define SYMMETRIC_DIFFERENCE_RANGE_SET(ty2, ty1, cppty)                                                                \
    LOG("symmetric_difference " #ty2 " with " #ty1 "\n");                                                              \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_symmetric_difference_range(&begin, (ty1##_int_it *)&range2);                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));          \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define SYMMETRIC_DIFFERENCE_RANGE_SLIST(ty2, ty1, cppty)                                                              \
    LOG("symmetric_difference " #ty2 " with " #ty1 "\n");                                                              \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_symmetric_difference_range(&begin, (ty1##_int_it *)&range2);                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));                 \
    CHECK_SLIST(ty1, ty2, cppty, aaa, bbb);                                                                            \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#ifndef _MSC_VER
#define SYMMETRIC_DIFFERENCE_RANGE(ty2, ty1, cppty)                                                                    \
    LOG("symmetric_difference " #ty2 " with " #ty1 "\n");                                                              \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_symmetric_difference_range(&begin, (ty1##_int_it *)&range2);                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                  \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define SYMMETRIC_DIFFERENCE_RANGE(ty2, ty1, cppty)                                                                    \
    LOG("symmetric_difference " #ty2 " with " #ty1 "\n");                                                              \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_symmetric_difference_range(&begin, (ty1##_int_it *)&range2);                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
//#define SYMMETRIC_DIFFERENCE_RANGE_SET(ty2, ty1, cppty) SYMMETRIC_DIFFERENCE_RANGE(ty2, ty1, cpp
//#define SYMMETRIC_DIFFERENCE_RANGE_SLIST(ty2, ty1, cppty) SYMMETRIC_DIFFERENCE_RANGE(ty2, ty1, cpp
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SYMMETRIC_DIFFERENCE_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SYMMETRIC_DIFFERENCE_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SYMMETRIC_DIFFERENCE_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SYMMETRIC_DIFFERENCE_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE(uset, deq, deque<int>); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2;  SYMMETRIC_DIFFERENCE_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2;  SYMMETRIC_DIFFERENCE_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE_SLIST(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE_SLIST(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE_SLIST(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2;  SYMMETRIC_DIFFERENCE_RANGE_SLIST(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2;  SYMMETRIC_DIFFERENCE_RANGE_SLIST(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE_SLIST(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE_SLIST(uset, slist, forward_list<int>); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE_SET(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE_SET(arr25, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE_SET(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SYMMETRIC_DIFFERENCE_RANGE_SET(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SYMMETRIC_DIFFERENCE_RANGE_SET(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break; // nyi
#if 0
                {
                    SETUP_USET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SYMMETRIC_DIFFERENCE_RANGE_SET(vec, uset, unordered_set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SYMMETRIC_DIFFERENCE_RANGE_SET(arr25, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SYMMETRIC_DIFFERENCE_RANGE_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SYMMETRIC_DIFFERENCE_RANGE_SET(list, uset, unordered_set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SYMMETRIC_DIFFERENCE_RANGE_SET(slist, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SYMMETRIC_DIFFERENCE_RANGE_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; SYMMETRIC_DIFFERENCE_RANGE_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a); break;
                }
#endif
                } // switch t1
                break;

#ifdef DEBUG
            case TEST_DIFFERENCE_RANGE:

#ifndef _MSC_VER
#define DIFFERENCE_RANGE_SET(ty2, ty1, cppty)                                                                          \
    LOG("difference " #ty2 " from " #ty1 "\n");                                                                        \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_difference_range(&begin, (ty1##_int_it *)&range2);                                       \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));                    \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define DIFFERENCE_RANGE_SLIST(ty2, ty1, cppty)                                                                        \
    LOG("difference " #ty2 " from " #ty1 "\n");                                                                        \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_difference_range(&begin, (ty1##_int_it *)&range2);                                       \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));                           \
    CHECK_SLIST(ty1, ty2, cppty, aaa, bbb);                                                                            \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define DIFFERENCE_RANGE(ty2, ty1, cppty)                                                                              \
    LOG("difference " #ty2 " from " #ty1 "\n");                                                                        \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_difference_range(&begin, (ty1##_int_it *)&range2);                                       \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    std::cppty bbb;                                                                                                    \
    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                            \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define DIFFERENCE_RANGE(ty2, ty1, cppty)                                                                              \
    LOG("difference " #ty2 " from " #ty1 "\n");                                                                        \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_difference_range(&begin, (ty1##_int_it *)&range2);                                       \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define DIFFERENCE_RANGE_SET(ty2, ty1, cppty) DIFFERENCE_RANGE(ty2, ty1, cppty)
#define DIFFERENCE_RANGE_SLIST(ty2, ty1, cppty) DIFFERENCE_RANGE(ty2, ty1, cppty)
#endif

                switch (t1)
                {
                case CTL_VECTOR: {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR: {
                        SETUP_VEC2; DIFFERENCE_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY: {
                        SETUP_ARR2; DIFFERENCE_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE: {
                        SETUP_DEQ2; DIFFERENCE_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST: {
                        SETUP_LIST2; DIFFERENCE_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST: {
                        SETUP_SLIST2; DIFFERENCE_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET: {
                        SETUP_SET2; DIFFERENCE_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET: {
                        SETUP_USET2; DIFFERENCE_RANGE(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
                    break;
                }
                case CTL_ARRAY:
                    break;
                case CTL_DEQUE: {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR: {
                        SETUP_VEC2; DIFFERENCE_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY: {
                        SETUP_ARR2; DIFFERENCE_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE: {
                        SETUP_DEQ2; DIFFERENCE_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST: {
                        SETUP_LIST2; DIFFERENCE_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST: {
                        SETUP_SLIST2; DIFFERENCE_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET: {
                        SETUP_SET2; DIFFERENCE_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET: {
                        SETUP_USET2; DIFFERENCE_RANGE(uset, deq, deque<int>); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST: {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR: {
                        SETUP_VEC2; DIFFERENCE_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY: {
                        SETUP_ARR2; DIFFERENCE_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE: {
                        SETUP_DEQ2; DIFFERENCE_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST: {
                        SETUP_LIST2; DIFFERENCE_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST: {
                        SETUP_SLIST2; DIFFERENCE_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET: {
                        SETUP_SET2; DIFFERENCE_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET: {
                        SETUP_USET2; DIFFERENCE_RANGE(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST: {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR: {
                        SETUP_VEC2; DIFFERENCE_RANGE_SLIST(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY: {
                        SETUP_ARR2; DIFFERENCE_RANGE_SLIST(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE: {
                        SETUP_DEQ2; DIFFERENCE_RANGE_SLIST(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST: {
                        SETUP_LIST2; DIFFERENCE_RANGE_SLIST(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST: {
                        SETUP_SLIST2; DIFFERENCE_RANGE_SLIST(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET: {
                        SETUP_SET2; DIFFERENCE_RANGE_SLIST(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET: {
                        SETUP_USET2; DIFFERENCE_RANGE_SLIST(uset, slist, forward_list<int>); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET:
                    break; // nyi
#if 0
                {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; DIFFERENCE_RANGE_SET(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; DIFFERENCE_RANGE_SET(arr25, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; DIFFERENCE_RANGE_SET(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; DIFFERENCE_RANGE_SET(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; DIFFERENCE_RANGE_SET(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; DIFFERENCE_RANGE_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; DIFFERENCE_RANGE_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
#endif
                case CTL_USET:
                    break; // nyi
#if 0
                {
                    SETUP_USET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; DIFFERENCE_RANGE_SET(vec, uset, unordered_set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; DIFFERENCE_RANGE_SET(arr25, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; DIFFERENCE_RANGE_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; DIFFERENCE_RANGE_SET(list, uset, unordered_set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; DIFFERENCE_RANGE_SET(slist, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; DIFFERENCE_RANGE_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; DIFFERENCE_RANGE_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a); break;
                }
#endif
                } // switch t1
                break;
#endif // DEBUG

            case TEST_SEARCH_RANGE:

#define SEARCH_RANGE(ty2, ty1, cppty)                                                                                  \
    LOG("search_range " #ty2 " in " #ty1 "\n");                                                                        \
    ty1##_int_it pos = ty1##_int_begin(&a);                                                                            \
    bool found_a = ty1##_int_search_range(&pos, (ty1##_int_it *)&range2);                                              \
    auto iter = std::search(b.begin(), b.end(), bb.begin(), bb.end());                                                 \
    bool found_b = iter != b.end();                                                                                    \
    LOG("found a: %s, ", found_a ? "yes" : "no");                                                                      \
    LOG("found b: %s\n", found_b ? "yes" : "no");                                                                      \
    assert(found_a == found_b);                                                                                        \
    if (found_a)                                                                                                       \
        assert(*pos.ref == *iter);                                                                                     \
    ty2##_int_free(&aa)

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SEARCH_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, arr25, arrint<25>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, arr25, arrint<25>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, arr25, arrint<25>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, arr25, arrint<25>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, arr25, arrint<25>); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    arr25_int_free(&a); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SEARCH_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SEARCH_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SEARCH_RANGE(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; SEARCH_RANGE(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; SEARCH_RANGE(arr25, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; SEARCH_RANGE(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; SEARCH_RANGE(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; SEARCH_RANGE(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; SEARCH_RANGE(set, set, set<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break;
                } // switch t1
                break;

        case TEST_FIND_FIRST_OF_RANGE:

#define FIND_FIRST_OF_RANGE(ty2, ty1, cppty)                                                                           \
    LOG("find_first_of_range " #ty2 " in " #ty1 "\n");                                                               \
    ty1##_int_it pos = ty1##_int_begin(&a);                                                                            \
    bool found_a = ty1##_int_find_first_of_range(&pos, (ty1##_int_it *)&range2);                                       \
    auto iter = std::find_first_of(b.begin(), b.end(), bb.begin(), bb.end());                                          \
    bool found_b = iter != b.end();                                                                                    \
    LOG("found a: %s at %lu, ", found_a ? "yes" : "no", ty1##_int_it_index(&pos));                                     \
    LOG("found b: %s at %ld\n", found_b ? "yes" : "no", std::distance(b.begin(), iter));                               \
    assert(found_a == found_b);                                                                                        \
    if (found_a)                                                                                                       \
        assert(*pos.ref == *iter);                                                                                     \
    ty2##_int_free(&aa)

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_FIRST_OF_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, arr25, arrint<25>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, arr25, arrint<25>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, arr25, arrint<25>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, arr25, arrint<25>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, arr25, arrint<25>); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    arr25_int_free(&a); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_FIRST_OF_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_FIRST_OF_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_FIRST_OF_RANGE(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_FIRST_OF_RANGE(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
#ifdef DEBUG
                        SETUP_ARR2; FIND_FIRST_OF_RANGE(arr25, set, set<int>);
#endif
                        break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_FIRST_OF_RANGE(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_FIRST_OF_RANGE(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_FIRST_OF_RANGE(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_FIRST_OF_RANGE(set, set, set<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break;
                } // switch t1
                break;
                
            case TEST_FIND_END_RANGE:

#if __cpp_lib_erase_if >= 202002L
#define FIND_END_RANGE(ty2, ty1, cppty)                                                                                \
    LOG("find_end_range " #ty2 " in " #ty1 "\n");                                                                    \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int_it it = ty1##_int_find_end_range(&begin, (ty1##_int_it *)&range2);                                       \
    auto iter = std::find_end(b.begin(), b.end(), bb.begin(), bb.end());                                               \
    bool found_a = !ty1##_int_it_done(&it);                                                                            \
    bool found_b = iter != b.end();                                                                                    \
    LOG("found a: %s at %lu, ", found_a ? "yes" : "no", ty1##_int_it_index(&it));                                      \
    LOG("found b: %s at %ld\n", found_b ? "yes" : "no", std::distance(b.begin(), iter));                               \
    assert(found_a == found_b);                                                                                        \
    if (found_a)                                                                                                       \
        assert(*it.ref == *iter);                                                                                      \
    ty2##_int_free(&aa)
#else
#define FIND_END_RANGE(ty2, ty1, cppty)                                                                                \
    LOG("find_end_range " #ty2 " in " #ty1 "\n");                                                                      \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int_find_end_range(&begin, (ty1##_int_it *)&range2);                                                         \
    ty2##_int_free(&aa)
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, vec, vector<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, vec, vector<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, vec, vector<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, vec, vector<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_END_RANGE(set, vec, vector<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, arr25, arrint<25>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, arr25, arrint<25>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, arr25, arrint<25>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, arr25, arrint<25>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, arr25, arrint<25>); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    arr25_int_free(&a); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, deq, deque<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, deq, deque<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, deq, deque<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_END_RANGE(set, deq, deque<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, list, list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, list, list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, list, list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, list, list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, list, list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_END_RANGE(set, list, list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, slist, forward_list<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, slist, forward_list<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_END_RANGE(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; FIND_END_RANGE(vec, set, set<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; FIND_END_RANGE(arr25, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; FIND_END_RANGE(deq, set, set<int>); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; FIND_END_RANGE(list, set, set<int>); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; FIND_END_RANGE(slist, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; FIND_END_RANGE(set, set, set<int>); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break;
                } // switch t1
                break;
                
        default:
#ifdef DEBUG
            printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
