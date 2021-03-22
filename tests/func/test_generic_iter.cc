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
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(ASSIGN_GENERIC)                                                                                               \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(MISMATCH)                                                                                                     \
    TEST(LEXICOGRAPHICAL_COMPARE)

#define FOREACH_DEBUG(TEST)
    //TEST(COPY_GENERIC)
    //TEST(REMOVE_RANGE) /* 14. max 16? (5 bits) */

// over in iter2:
#define FOREACH_METH2(TEST)                                                                                            \
    TEST(UNION_RANGE)                                                                                                  \
    TEST(INTERSECTION_RANGE)                                                                                           \
    TEST(SYMMETRIC_DIFFERENCE_RANGE)                                                                                   \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_END_RANGE)
#define FOREACH_DEBUG2(TEST)                                                                                           \
    TEST(DIFFERENCE_RANGE)

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
        int vb;
        types_t t1, t2;
        int which;
        union gen_cov_u wu;
        if (!tests.size) // random testing
        {
            which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
            if (test >= 0x1000)
            {
                wu.w = test;
                t1 = (types_t)wu.u.t1;
                t2 = (types_t)wu.u.t2;
            }
            else
            {
                t1 = pick_type();
                t2 = pick_type();
            }
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
        assert(wu.w < covvec.size);
#ifdef DEBUG
        assert(wu.u.w1 < len(test_names));
#endif
        LOG("TEST %s %d (0x%x)\n", test_names[wu.u.w1], which, (unsigned)wu.w);
        covvec.vector[wu.w]++;
        switch (wu.u.w1)
        {

        case TEST_INSERT_GENERIC:

// TODO std::inserter
#define INSERT_INTO_SET(ty2, ty1, cppty)                                                                               \
    LOG("insert " #ty2 " into " #ty1 "\n");                                                                            \
    /* C++ cannot insert generic iters into set/uset */                                                                \
    ty1##_int_insert_generic(&a, (ty1##_int_it *)&range2);                                                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    ty2##_int_free(&aa)
#define INSERT_INTO_SLIST(ty2, ty1, cppty)                                                                             \
    LOG("insert " #ty2 " into " #ty1 "\n");                                                                            \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    begin.node = NULL; /* == b.before_begin() */                                                                       \
    ty1##_int_insert_generic(&begin, (ty1##_int_it *)&range2);                                                         \
    b.insert_after(b.before_begin(), bb.begin(), bb.end());                                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    CHECK_SLIST(ty1, ty2, cppty, a, b);                                                                                \
    ty2##_int_free(&aa)
#define INSERT_INTO(ty2, ty1, cppty)                                                                                   \
    LOG("insert " #ty2 " into " #ty1 "\n");                                                                            \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int_insert_generic(&begin, (ty1##_int_it *)&range2);                                                         \
    b.insert(b.begin(), bb.begin(), bb.end());                                                                         \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    CHECK(ty1, ty2, cppty, a, b);                                                                                      \
    ty2##_int_free(&aa)

            switch (t1)
            {
            // cannot insert into array
            case CTL_ARRAY : break;
            case CTL_VECTOR : {
                SETUP_VEC1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, vec, vector<int>); break;
                }
                case CTL_ARRAY : {
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO(arr25, vec, vector<int>);
#endif
                    break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, vec, vector<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, vec, vector<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO(slist, vec, vector<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, vec, vector<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; INSERT_INTO(uset, vec, vector<int>); break;
                }
                } // switch t2
                vec_int_free(&a); break;
            }
            case CTL_DEQUE : {
                SETUP_DEQ1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO(vec, deq, deque<int>); break;
                }
                case CTL_ARRAY : {
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO(arr25, deq, deque<int>);
#endif
                    break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO(deq, deq, deque<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO(list, deq, deque<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO(slist, deq, deque<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, deq, deque<int>); break;
                }
                case CTL_USET : { // random order!
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
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO(arr25, list, list<int>);
#endif
                    break;
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
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO(slist, list, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO(set, list, list<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; INSERT_INTO(uset, list, list<int>); break;
                }
                } // switch t2
                list_int_free(&a); break;
            }
            case CTL_SLIST : {
                SETUP_SLIST1;
                switch (t2)
                {
                case CTL_ARRAY : {
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO_SLIST(arr25, slist, forward_list<int>);
#endif
                    break;
                }
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO_SLIST(vec, slist, forward_list<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO_SLIST(deq, slist, forward_list<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO_SLIST(list, slist, forward_list<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO_SLIST(slist, slist, forward_list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO_SLIST(set, slist, forward_list<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; INSERT_INTO_SLIST(uset, slist, forward_list<int>); break;
                }
                } // switch t2
                slist_int_free(&a); break;
            }
            // C++ cannot insert into set. CTL can
            case CTL_SET : {
                SETUP_SET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO_SET(vec, set, set<int>); break;
                }
                case CTL_ARRAY : {
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO_SET(arr25, set, set<int>);
#endif
                    break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO_SET(deq, set, set<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO_SET(list, set, set<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO_SET(slist, set, set<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO_SET(set, set, set<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; INSERT_INTO_SET(uset, set, set<int>); break;
                }
                } // switch t2
                set_int_free(&a); break;
            }
//#ifdef DEBUG
            // C++ cannot insert into unordered_set. CTL can
            case CTL_USET: {
                SETUP_USET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; INSERT_INTO_SET(vec, uset, unordered_set<int>); break;
                }
                case CTL_ARRAY : {
#ifdef DEBUG
                    SETUP_ARR2; INSERT_INTO_SET(arr25, uset, unordered_set<int>);
#endif
                    break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; INSERT_INTO_SET(list, uset, unordered_set<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; INSERT_INTO_SET(slist, uset, unordered_set<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; INSERT_INTO_SET(deq, uset, unordered_set<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; INSERT_INTO_SET(set, uset, unordered_set<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; INSERT_INTO_SET(uset, uset, unordered_set<int>); break;
                }
                } // switch t2
                uset_int_free(&a); break;
            }
//#endif // DEBUG
            } // switch t1
            break;

        case TEST_ASSIGN_GENERIC:

// STL has no array.assign, only we have
#define ASSIGN_GENERIC_ARRAY(ty2, ty1)                                                                                 \
    LOG("assign " #ty2 " into " #ty1 "\n");                                                                            \
    ty1##_int_assign_generic(&a, (ty1##_int_it *)&range2);                                                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    ty2##_int_free(&aa)
// slist has no size
#define ASSIGN_GENERIC_SLIST(ty2, ty1, cppty)                                                                          \
    LOG("assign " #ty2 " into " #ty1 "\n");                                                                            \
    ty1##_int_assign_generic(&a, (ty1##_int_it *)&range2);                                                             \
    b.assign(bb.begin(), bb.end());                                                                                    \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    CHECK_SLIST(ty1, ty2, cppty, a, b)                                                                                 \
    ty2##_int_free(&aa)
#define ASSIGN_GENERIC(ty2, ty1, cppty)                                                                                \
    LOG("assign " #ty2 " into " #ty1 "\n");                                                                            \
    ty1##_int_assign_generic(&a, (ty1##_int_it *)&range2);                                                             \
    b.assign(bb.begin(), bb.end());                                                                                    \
    LOG("=> ");                                                                                                        \
    print_##ty1(&a);                                                                                                   \
    CHECK(ty1, ty2, cppty, a, b)                                                                                       \
    ty2##_int_free(&aa)

            switch (t1)
            {
            case CTL_ARRAY : {
                SETUP_ARR1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC_ARRAY(vec, arr25); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC_ARRAY(arr25, arr25); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC_ARRAY(deq, arr25); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC_ARRAY(list, arr25); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC_ARRAY(slist, arr25); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC_ARRAY(set, arr25); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC_ARRAY(uset, arr25); break;
                }
                } // switch t2
                arr25_int_free(&a); break;
            }
            case CTL_VECTOR : {
                SETUP_VEC1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC(vec, vec, vector<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC(arr25, vec, vector<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC(deq, vec, vector<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC(list, vec, vector<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC(slist, vec, vector<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC(set, vec, vector<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC(uset, vec, vector<int>); break;
                }
                } // switch t2
                vec_int_free(&a); break;
            }
            case CTL_DEQUE : {
                SETUP_DEQ1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC(vec, deq, deque<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC(arr25, deq, deque<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC(deq, deq, deque<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC(list, deq, deque<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC(slist, deq, deque<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC(set, deq, deque<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC(uset, deq, deque<int>); break;
                }
                } // switch t2
                deq_int_free(&a); break;
            }
            case CTL_LIST : {
                SETUP_LIST1;
                switch (t2)
                {
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC(arr25, list, list<int>); break;
                }
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC(vec, list, list<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC(deq, list, list<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC(list, list, list<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC(slist, list, list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC(set, list, list<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC(uset, list, list<int>); break;
                }
                } // switch t2
                list_int_free(&a); break;
            }
            case CTL_SLIST : {
                SETUP_SLIST1;
                switch (t2)
                {
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC_SLIST(arr25, slist, forward_list<int>); break;
                }
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC_SLIST(vec, slist, forward_list<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC_SLIST(deq, slist, forward_list<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC_SLIST(list, slist, forward_list<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC_SLIST(slist, slist, forward_list<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC_SLIST(set, slist, forward_list<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC_SLIST(uset, slist, forward_list<int>); break;
                }
                } // switch t2
                slist_int_free(&a); break;
            }
            // cannot mass-assign unordered_set yet. STL cannot
            case CTL_SET : break;
#if 0
            {
                SETUP_SET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC_SET(vec, set, set<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC_SET(arr25, set, set<int>);
                    break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC_SET(deq, set, set<int>); break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC_SET(list, set, set<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC_SET(slist, set, set<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC_SET(set, set, set<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC_SET(uset, set, set<int>); break;
                }
                } // switch t2
                set_int_free(&a); break;
            }
#endif // 0
            // cannot mass-assign unordered_set yet. STL cannot
            case CTL_USET: break;
#if 0
            {
                SETUP_USET1;
                switch (t2)
                {
                case CTL_VECTOR : {
                    SETUP_VEC2; ASSIGN_GENERIC_SET(vec, uset, unordered_set<int>); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR2; ASSIGN_GENERIC_SET(arr25, uset, unordered_set<int>);
                    break;
                }
                case CTL_LIST : {
                    SETUP_LIST2; ASSIGN_GENERIC_SET(list, uset, unordered_set<int>); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST2; ASSIGN_GENERIC_SET(slist, uset, unordered_set<int>); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ2; ASSIGN_GENERIC_SET(deq, uset, unordered_set<int>); break;
                }
                case CTL_SET : {
                    SETUP_SET2; ASSIGN_GENERIC_SET(set, uset, unordered_set<int>); break;
                }
                case CTL_USET : { // random order!
                    SETUP_USET2; ASSIGN_GENERIC_SET(uset, uset, unordered_set<int>); break;
                }
                } // switch t2
                uset_int_free(&a); break;
            }
#endif // 0
            } // switch t1
            break;

            case TEST_MERGE_RANGE:

#ifndef _MSC_VER
#define MERGE_INTO(ty2, ty1, cppty)                                                                                    \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    std::cppty bbb;                                                                                                    \
    std::merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));                                     \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define MERGE_INTO_SLIST(ty2, ty1, cppty)                                                                              \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    std::cppty bbb;                                                                                                    \
    std::merge(b.begin(), b.end(), bb.begin(), bb.end(), std::front_inserter(bbb));                                    \
    bbb.reverse();                                                                                                     \
    CHECK_SLIST(ty1, ty2, cppty, aaa, bbb);                                                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define MERGE_INTO_SET(ty2, ty1, cppty)                                                                                \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    std::cppty bbb;                                                                                                    \
    std::merge(b.begin(), b.end(), bb.begin(), bb.end(), std::inserter(bbb, bbb.begin()));                             \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    CHECK(ty1, ty2, cppty, aaa, bbb);                                                                                  \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#else
#define MERGE_INTO(ty2, ty1, cppty)                                                                                    \
    LOG("merge " #ty2 " into " #ty1 "\n");                                                                             \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    ty1##_int aaa = ty1##_int_merge_range(&begin, (ty1##_int_it *)&range2);                                            \
    LOG("=> ");                                                                                                        \
    print_##ty1(&aaa);                                                                                                 \
    ty1##_int_free(&aaa);                                                                                              \
    ty2##_int_free(&aa)
#define MERGE_INTO_SET(ty2, ty1, cppty)  MERGE_INTO(ty2, ty1, cppty)
#define MERGE_INTO_SLIST(ty2, ty1, cppty, ok)  MERGE_INTO(ty2, ty1, cppty)
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
                        b.merge(bb); // test the native destructive merge
                        CHECK(list, list, list<int>, aaa, b);
                        list_int_free(&aa);
                        list_int_free(&aaa);
                        break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MERGE_INTO(slist, list, list<int>); break;
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
                        SETUP_SET2; MERGE_INTO(set, list, list<int>); break;
                    }
                    case CTL_USET : { // random order!
                        SETUP_USET2; MERGE_INTO(uset, list, list<int>); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                } // LIST
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_SLIST : {
                        SETUP_SLIST2;
                        LOG("merge slist into slist\n");
                        slist_int_it begin = slist_int_begin(&a);
                        slist_int aaa = slist_int_merge_range(&begin, &range2);
                        print_slist(&aaa);
                        b.merge(bb); // test the native destructive merge
                        CHECK_SLIST(slist, slist, forward_list<int>, aaa, b);
                        slist_int_free(&aa);
                        slist_int_free(&aaa);
                        break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MERGE_INTO_SLIST(list, slist, forward_list<int>); break;
                    }
                    case CTL_VECTOR : {
                        SETUP_VEC2; MERGE_INTO_SLIST(vec, slist, forward_list<int>); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MERGE_INTO_SLIST(arr25, slist, forward_list<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO_SLIST(deq, slist, forward_list<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SLIST(set, slist, forward_list<int>); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; MERGE_INTO_SLIST(uset, slist, forward_list<int>); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                } // SLIST
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
                    case CTL_SLIST : {
                        SETUP_SLIST2; MERGE_INTO(slist, vec, vector<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO(set, vec, vector<int>); break;
                    }
                    case CTL_USET : { // random order!
                        SETUP_USET2; MERGE_INTO(uset, vec, vector<int>); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
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
                    case CTL_SLIST : {
                        SETUP_SLIST2; MERGE_INTO(slist, deq, deque<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO(deq, deq, deque<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO(set, deq, deque<int>); break;
                    }
                    case CTL_USET : { // random order!
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
                    case CTL_SLIST : {
                        SETUP_SLIST2; MERGE_INTO_SET(slist, set, set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO_SET(deq, set, set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SET(set, set, set<int>); break;
                    }
                    case CTL_USET : { // random order!
                        SETUP_USET2; MERGE_INTO_SET(uset, set, set<int>); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
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
                    case CTL_SLIST : {
                        SETUP_SLIST2; MERGE_INTO_SET(slist, uset, unordered_set<int>); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MERGE_INTO_SET(deq, uset, unordered_set<int>); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MERGE_INTO_SET(set, uset, unordered_set<int>); break;
                    }
                    case CTL_USET : { // random order!
                        SETUP_USET2; MERGE_INTO_SET(uset, uset, unordered_set<int>); break;
                    }
                    } // switch t2
                    uset_int_free(&a); break;
                }
                } // switch t1
                break;

            case TEST_INCLUDES_RANGE:

#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
#define INCLUDES_RANGE(ty2, ty1)                                                                                       \
    LOG("includes " #ty2 " from " #ty1 "\n");                                                                          \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    bool a_found = ty1##_int_includes_range(&begin, (ty1##_int_it *)&range2);                                          \
    bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());                                            \
    LOG("a_found %d == b_found %d\n", (int)a_found, (int)b_found);                                                     \
    if (!strcmp(#ty1, "uset") || !strcmp(#ty2, "uset"))                                                                \
        ;                                                                                                              \
    else                                                                                                               \
        assert(a_found == b_found);                                                                                    \
    ty2##_int_free(&aa)
#else
#define INCLUDES_RANGE(ty2, ty1)                                                                                       \
    LOG("includes " #ty2 " from " #ty1 "\n");                                                                          \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    bool a_found = ty1##_int_includes_range(&begin, (ty1##_int_it *)&range2);                                          \
    bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());                                            \
    LOG("a_found %d == b_found %d\n", (int)a_found, (int)b_found);                                                     \
    if (a_found != b_found)                                                                                            \
        printf("a_found %d != b_found %d FAIL (C++11 without robust_nonmodifying_seq_ops)\n", (int)a_found,            \
               (int)b_found);                                                                                          \
    ty2##_int_free(&aa)
#endif
                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, vec); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, vec); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, vec); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, vec); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, vec); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, vec); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, vec); break;
                    }
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, arr25); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, arr25); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, arr25); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, arr25); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, arr25); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, arr25); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, arr25); break;
                    }
                    } // switch t2
                    arr25_int_free(&a); break;
                }
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, deq); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, deq); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, deq); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, deq); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, deq); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, deq); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, deq); break;
                    }
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, list); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, list); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, list); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, list); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, list); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, list); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, list); break;
                    }
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, slist); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, slist); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, slist); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, slist); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, slist); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, slist); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, slist); break;
                    }
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : {
                    SETUP_SET1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; INCLUDES_RANGE(vec, set); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; INCLUDES_RANGE(arr25, set); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; INCLUDES_RANGE(deq, set); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; INCLUDES_RANGE(list, set); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; INCLUDES_RANGE(slist, set); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; INCLUDES_RANGE(set, set); break;
                    }
                    case CTL_USET : {
                        SETUP_USET2; INCLUDES_RANGE(uset, set); break;
                    }
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break;
                } // switch t1
                break;

            case TEST_EQUAL_RANGE:

#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
#define EQUAL_RANGE(ty2, ty1)                                                                                          \
    LOG("equal_range " #ty2 " with " #ty1 "\n");                                                                       \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    bool same_a = ty1##_int_equal_range(&begin, (ty1##_int_it *)&range2);                                              \
    bool same_b = std::equal(b.begin(), b.end(), bb.begin(), bb.end());                                                \
    LOG("same_a %d == same_b %d\n", (int)same_a, (int)same_b);                                                         \
    assert(same_a == same_b);                                                                                          \
    ty2##_int_free(&aa)
#else
#define EQUAL_RANGE(ty2, ty1)                                                                                          \
    LOG("equal_range " #ty2 " with " #ty1 "\n");                                                                       \
    ty1##_int_it begin = ty1##_int_begin(&a);                                                                          \
    bool same_a = ty1##_int_equal_range(&begin, (ty1##_int_it *)&range2);                                              \
    if (!b.size() || !bb.size() || !std::distance(bb.begin(), bb.end()))                                               \
    {                                                                                                                  \
        printf("skip std::equal with empty range. use C++14\n");                                                       \
        ty2##_int_free(&aa);                                                                                           \
        break;                                                                                                         \
    }                                                                                                                  \
    bool same_b = std::equal(b.begin(), b.end(), bb.begin());                                                          \
    if (same_a != same_b)                                                                                              \
        printf("std::equal broken with C++11, same_a %d != same_b %d FAIL. Use C++14\n", (int)same_a, (int)same_b);    \
    ty2##_int_free(&aa)
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; EQUAL_RANGE(vec, vec); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; EQUAL_RANGE(arr25, vec); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; EQUAL_RANGE(deq, vec); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; EQUAL_RANGE(list, vec); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; EQUAL_RANGE(slist, vec); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : {
                    SETUP_ARR1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; EQUAL_RANGE(vec, arr25); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; EQUAL_RANGE(arr25, arr25); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; EQUAL_RANGE(deq, arr25); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; EQUAL_RANGE(list, arr25); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; EQUAL_RANGE(slist, arr25); break;
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
                        SETUP_VEC2; EQUAL_RANGE(vec, deq); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; EQUAL_RANGE(arr25, deq); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; EQUAL_RANGE(deq, deq); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; EQUAL_RANGE(list, deq); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; EQUAL_RANGE(slist, deq); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    deq_int_free(&a); break;
                }
                case CTL_LIST : {
                    SETUP_LIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; EQUAL_RANGE(vec, list); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; EQUAL_RANGE(arr25, list); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; EQUAL_RANGE(deq, list); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; EQUAL_RANGE(list, list); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; EQUAL_RANGE(slist, list); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    list_int_free(&a); break;
                }
                case CTL_SLIST : {
                    SETUP_SLIST1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; EQUAL_RANGE(vec, slist); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; EQUAL_RANGE(arr25, slist); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; EQUAL_RANGE(deq, slist); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; EQUAL_RANGE(list, slist); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; EQUAL_RANGE(slist, slist); break;
                    }
                    case CTL_SET : break;
                    case CTL_USET : break;
                    } // switch t2
                    slist_int_free(&a); break;
                }
                case CTL_SET : break;
                case CTL_USET : break;
                } // switch t1
                break;

        case TEST_MISMATCH:

#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
#define MISMATCH(ty2, ty1)                                                                                             \
    LOG("mismatch " #ty2 " with " #ty1 "\n");                                                                          \
    ty1##_int_it b1 = ty1##_int_begin(&a);                                                                             \
    ty2##_int_it b2 = ty2##_int_begin(&aa);                                                                            \
    ty1##_int_it r1a = ty1##_int_begin(&a);                                                                            \
    ty1##_int_mismatch(&r1a, (ty1##_int_it *)&range2);                                                                 \
    auto pair = std::mismatch(b.begin(), b.end(), bb.begin(), bb.end());                                               \
    int d1a = ty1##_int_it_distance(&b1, &r1a);                                                                        \
    int d2a = ty2##_int_it_distance(&b2, &range2);                                                                     \
    assert(d1a == std::distance(b.begin(), pair.first));                                                               \
    assert(d2a == std::distance(bb.begin(), pair.second));                                                             \
    ty2##_int_free(&aa)
#else
#define MISMATCH(ty2, ty1)                                                                                             \
    LOG("mismatch " #ty2 " with " #ty1 "\n");                                                                          \
    ty1##_int_it b1 = ty1##_int_begin(&a);                                                                             \
    ty2##_int_it b2 = ty2##_int_begin(&aa);                                                                            \
    ty1##_int_it r1a = ty1##_int_begin(&a);                                                                            \
    /*bool same_a = */ ty1##_int_mismatch(&r1a, (ty1##_int_it *)&range2);                                              \
    if (!bb.size() || !std::distance(bb.begin(), bb.end()))                                                            \
    {                                                                                                                  \
        printf("skip std::mismatch with empty 2nd range. use C++14\n");                                                \
        ty2##_int_free(&aa);                                                                                           \
        break;                                                                                                         \
    }                                                                                                                  \
    auto pair = std::mismatch(b.begin(), b.end(), bb.begin());                                                         \
    int d1a = ty1##_int_it_distance(&b1, &r1a);                                                                        \
    int d2a = ty2##_int_it_distance(&b2, &range2);                                                                     \
    if (d1a != std::distance(b.begin(), pair.first) || d2a != std::distance(bb.begin(), pair.second))                  \
        printf("std::mismatch broken with C++11\n");                                                                   \
    ty2##_int_free(&aa)
#endif

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MISMATCH(vec, vec); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MISMATCH(arr25, vec); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MISMATCH(deq, vec); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MISMATCH(list, vec); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MISMATCH(slist, vec); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MISMATCH(set, vec); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; MISMATCH(vec, deq); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MISMATCH(arr25, deq); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MISMATCH(deq, deq); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MISMATCH(list, deq); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MISMATCH(slist, deq); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MISMATCH(set, deq); break;
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
                        SETUP_VEC2; MISMATCH(vec, list); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MISMATCH(arr25, list); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MISMATCH(deq, list); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MISMATCH(list, list); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MISMATCH(slist, list); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MISMATCH(set, list); break;
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
                        SETUP_VEC2; MISMATCH(vec, slist); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MISMATCH(arr25, slist); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MISMATCH(deq, slist); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MISMATCH(list, slist); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MISMATCH(slist, slist); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MISMATCH(set, slist); break;
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
                        SETUP_VEC2; MISMATCH(vec, set); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; MISMATCH(arr25, set); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; MISMATCH(deq, set); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; MISMATCH(list, set); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; MISMATCH(slist, set); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; MISMATCH(set, set); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    set_int_free(&a); break;
                }
                case CTL_USET : break;
                } // switch t1
                break;

        case TEST_LEXICOGRAPHICAL_COMPARE:

#define LEX_COMPARE(ty2, ty1)                                                                                          \
    LOG("mismatch " #ty2 " with " #ty1 "\n");                                                                          \
    ty1##_int_it r1a = ty1##_int_begin(&a);                                                                            \
    bool same_a = ty1##_int_lexicographical_compare(&r1a, (ty1##_int_it *)&range2);                                    \
    bool same_b = std::lexicographical_compare(b.begin(), b.end(), bb.begin(), bb.end());                              \
    assert(same_a == same_b);                                                                                          \
    ty2##_int_free(&aa)

                switch (t1)
                {
                case CTL_VECTOR : {
                    SETUP_VEC1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; LEX_COMPARE(vec, vec); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; LEX_COMPARE(arr25, vec); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; LEX_COMPARE(deq, vec); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; LEX_COMPARE(list, vec); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; LEX_COMPARE(slist, vec); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; LEX_COMPARE(set, vec); break;
                    }
                    case CTL_USET : break;
                    } // switch t2
                    vec_int_free(&a); break;
                }
                case CTL_ARRAY : break;
                case CTL_DEQUE : {
                    SETUP_DEQ1;
                    switch (t2)
                    {
                    case CTL_VECTOR : {
                        SETUP_VEC2; LEX_COMPARE(vec, deq); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; LEX_COMPARE(arr25, deq); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; LEX_COMPARE(deq, deq); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; LEX_COMPARE(list, deq); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; LEX_COMPARE(slist, deq); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; LEX_COMPARE(set, deq); break;
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
                        SETUP_VEC2; LEX_COMPARE(vec, list); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; LEX_COMPARE(arr25, list); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; LEX_COMPARE(deq, list); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; LEX_COMPARE(list, list); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; LEX_COMPARE(slist, list); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; LEX_COMPARE(set, list); break;
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
                        SETUP_VEC2; LEX_COMPARE(vec, slist); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; LEX_COMPARE(arr25, slist); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; LEX_COMPARE(deq, slist); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; LEX_COMPARE(list, slist); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; LEX_COMPARE(slist, slist); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; LEX_COMPARE(set, slist); break;
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
                        SETUP_VEC2; LEX_COMPARE(vec, set); break;
                    }
                    case CTL_ARRAY : {
                        SETUP_ARR2; LEX_COMPARE(arr25, set); break;
                    }
                    case CTL_DEQUE : {
                        SETUP_DEQ2; LEX_COMPARE(deq, set); break;
                    }
                    case CTL_LIST : {
                        SETUP_LIST2; LEX_COMPARE(list, set); break;
                    }
                    case CTL_SLIST : {
                        SETUP_SLIST2; LEX_COMPARE(slist, set); break;
                    }
                    case CTL_SET : {
                        SETUP_SET2; LEX_COMPARE(set, set); break;
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
            printf("unhandled testcase %d %s\n", which, test_names[wu.u.w1]);
#else
            printf("unhandled testcase %d\n", which);
#endif
            break;
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
