#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#include <ctl/vector.h>

#include <algorithm>
#include <numeric>
#include <vector>

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH_BACK)                                                                                                    \
    TEST(POP_BACK)                                                                                                     \
    TEST(CLEAR)                                                                                                        \
    TEST(ERASE)                                                                                                        \
    TEST(ERASE_INDEX)                                                                                                  \
    TEST(ERASE_RANGE)                                                                                                  \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_INDEX)                                                                                                 \
    TEST(INSERT_COUNT)                                                                                                 \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(RESIZE)                                                                                                       \
    TEST(RESERVE)                                                                                                      \
    TEST(SHRINK_TO_FIT)                                                                                                \
    TEST(SORT)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(SWAP)                                                                                                         \
    TEST(ASSIGN)                                                                                                       \
    TEST(ASSIGN_RANGE)                                                                                                 \
    TEST(ASSIGN_GENERIC)                                                                                               \
    TEST(REMOVE_IF)                                                                                                    \
    TEST(ERASE_IF)                                                                                                     \
    TEST(EQUAL)                                                                                                        \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(FIND)                                                                                                         \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(COUNT_RANGE)                                                                                                  \
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
    TEST(TRANSFORM_IT)                                                                                                 \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
    TEST(EMPLACE_BACK)                                                                                                 \
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
    TEST(UNIQUE)                                                                                                       \
    TEST(UNIQUE_RANGE)                                                                                                 \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)                                                                                          \
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)                                                                                                \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(REVERSE)                                                                                                      \
    TEST(REVERSE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EMPLACE) /* 85 */                                                                                             \
    TEST(INSERT_GENERIC)                                                                                               \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM_IT_RANGE)

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
static const char *test_names[] = { FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif
// clang-format on

void print_vec(vec_digi *a)
{
    vec_foreach(digi, a, ref) printf("%d ", *ref->value);
    printf("\n");
}

void print_vec_range(vec_digi_it it)
{
    if (vec_digi_empty(it.container))
        return;
    vec_digi_it begin = vec_digi_begin(it.container);
    digi *ref = it.ref;
    long i1 = it.ref - begin.ref;
    long i2 = begin.end - it.ref;
    if (i1)
    {
        while (begin.ref != it.ref)
        {
            printf("%d ", *begin.ref->value);
            begin.ref++;
        }
    }
    printf("[");
    while (!vec_digi_it_done(&it))
    {
        printf("%d ", *it.ref->value);
        vec_digi_it_next(&it);
    }
    printf(") ");
    if (i2)
    {
        begin.ref = it.ref;
        while (begin.ref != begin.end)
        {
            printf("%d ", *begin.ref->value);
            begin.ref++;
        }
    }
    it.ref = ref;
    printf("\n");
}

void print_vector(std::vector<DIGI> &b)
{
    for (auto &d : b)
        printf("%d ", *d.value);
    printf("\n");
}

#ifdef DEBUG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 30
//#define TEST_MAX_VALUE INT_MAX
#define TEST_MAX_VALUE 15
#else
#define print_vec(x)
#define print_vector(x)
#define print_vec_range(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int middle(vec_digi *a)
{
    if (!a->size)
        return 0;
    return (*vec_digi_front(a)->value - *vec_digi_back(a)->value) / 2;
}

int median(vec_digi *a)
{
    vec_digi_it it = vec_digi_begin(a);
    vec_digi_it_advance(&it, a->size / 2);
    return a->size ? *it.ref->value : 0;
}

int pick_element(vec_digi *a)
{
    const size_t index = TEST_RAND(a->size);
    if (!a->size)
        return 0;
    digi *vp = vec_digi_at(a, index);
    return *vp->value;
}

int pick_random(vec_digi *a)
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

// tested variants
#if (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L)
// Tested ok with g++ 10, g++ 7.5,
// clang 10 (libc++ 11-18), apple clang 12 fail
#define ASSERT_EQUAL_CAP(c, s) assert(s.capacity() == c.capacity);
#else
// other llvm libc++ fail (gh actions), msvc untested
#define ASSERT_EQUAL_CAP(c, s)                                                                                         \
    if (s.capacity() != c.capacity)                                                                                    \
    {                                                                                                                  \
        LOG("capacity %zu vs %zu FAIL\n", c.capacity, s.capacity());                                                   \
        fail++;                                                                                                        \
    }
#endif

// cheat growth. the STL often has wrong and slow growth policies for algos.
// we rather reserve before, and then dont overallocate later.
#define ADJUST_CAP(m, c, s)                                                                                            \
    if (c.size == s.size() && c.capacity != s.capacity())                                                              \
    {                                                                                                                  \
        LOG("%s capacity %zu => %zu\n", m, c.capacity, s.capacity());                                                  \
        vec_digi_fit(&c, s.capacity());                                                                                \
    }

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        ASSERT_EQUAL_CAP(_x, _y)                                                                                       \
        assert(_x.size == _y.size());                                                                                  \
        assert(vec_digi_empty(&_x) == _y.empty());                                                                     \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            assert(*_y.front().value == *vec_digi_front(&_x)->value);                                                  \
            assert(*_y.back().value == *vec_digi_back(&_x)->value);                                                    \
        }                                                                                                              \
        std::vector<DIGI>::iterator _iter = _y.begin();                                                                \
        vec_foreach(digi, &_x, _ref)                                                                                   \
        {                                                                                                              \
            assert(*(_ref->value) == *_iter->value);                                                                   \
            _iter++;                                                                                                   \
        }                                                                                                              \
        digi *_ref = vec_digi_front(&_x);                                                                              \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*(_ref->value) == *_d.value);                                                                       \
            _ref++;                                                                                                    \
        }                                                                                                              \
        for (size_t i = 0; i < _y.size(); i++)                                                                         \
            assert(*_y.at(i).value == *vec_digi_at(&_x, i)->value);                                                    \
    }

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if ((_it).ref != &(_it).container->vector[(_it).container->size])                                                  \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*((_it).ref->value) == *(*_iter).value);                                                                \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!vec_digi_it_done(&(_it)))                                                                                     \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*((_it).ref->value) == *(*_iter).value);                                                                \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

#define CHECK_REF(_ref, b, _iter)                                                                                      \
    if (_iter != b.end())                                                                                              \
    assert(*(_ref->value) == *(*_iter).value)

static void gen_vectors(vec_digi *a, std::vector<DIGI> &b, size_t size)
{
    *a = vec_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for (int i = 0; i < (int)size; i++)
    {
        const int vb = TEST_RAND(TEST_MAX_VALUE);
        vec_digi_push_back(a, digi_init(vb));
        b.push_back(DIGI{vb});
    }
}

static void get_random_iters(vec_digi *a, vec_digi_it *range_a, std::vector<DIGI> &b,
                             std::vector<DIGI>::iterator &first_b, std::vector<DIGI>::iterator &last_b)
{
    vec_digi_it last_a;
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MAX(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        vec_digi_it it1 = vec_digi_begin(a);
        first_b = b.begin();
        vec_digi_it_advance(&it1, r1);
        first_b += r1;
        *range_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            last_a = vec_digi_end(a);
            last_b = b.end();
        }
        else
        {
            vec_digi_it it2 = vec_digi_begin(a);
            last_b = b.begin();
            vec_digi_it_advance(&it2, r2);
            last_b += r2;
            last_a = it2;
        }
    }
    else
    {
        vec_digi_it end = vec_digi_end(a);
        *range_a = end;
        last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    range_a->end = last_a.ref;
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    for (unsigned loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for (size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            vec_digi a, aa, aaa;
            std::vector<DIGI> b, bb, bbb;
            vec_digi_it range_a1, range_a2, it;
            vec_digi_it *pos;
            std::vector<DIGI>::iterator first_b1, last_b1, first_b2, last_b2, iter;
            bool found_a, found_b;
            size_t num_a, num_b;
            int value = TEST_RAND(TEST_MAX_VALUE);
            const size_t index = TEST_RAND(size);
            
            a = vec_digi_init();
            a.compare = digi_compare;
            a.equal = digi_equal;
            
            if (mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                vec_digi_resize(&a, size, digi_init(0));
                b.resize(size);
                for (int i = 0; i < (int)size; i++)
                {
#ifdef DEBUGxx
                    const int vb = i;
#else
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
#endif
                    vec_digi_set(&a, i, digi_init(vb));
                    b[i] = DIGI{vb};
                }
            }
            if (mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for (size_t pushes = 0; pushes < size; pushes++)
                {
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
                    vec_digi_push_back(&a, digi_init(vb));
                    b.push_back(DIGI{vb});
                }
            }

            int which;
            if (tests.size)
            {
                which = *queue_int_front(&tests);
                if (mode == MODE_TOTAL-1)
                    queue_int_pop(&tests);
            }
            else
                which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
            LOG("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            RECORD_WHICH;
            switch (which)
            {
            case TEST_PUSH_BACK: {
                b.push_back(DIGI{value});
                vec_digi_push_back(&a, digi_init(value));
                break;
            }
            case TEST_POP_BACK: {
                if (a.size > 0)
                {
                    b.pop_back();
                    vec_digi_pop_back(&a);
                }
                break;
            }
            case TEST_CLEAR: {
                b.clear();
                vec_digi_clear(&a);
                break;
            }
            case TEST_ERASE: {
                if (a.size > 0)
                {
                    it = vec_digi_begin(&a);
                    vec_digi_it_advance(&it, index);
                    it = vec_digi_erase(&it);
                    iter = b.erase(b.begin() + index);
                    CHECK_ITER(it, b, iter);
                }
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_INDEX: {
                if (a.size > 0)
                {
                    it = vec_digi_erase_index(&a, index);
                    iter = b.erase(b.begin() + index);
                    CHECK_ITER(it, b, iter);
                }
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_RANGE: // 5
            {
                if (a.size > 1)
                {
                    get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                    print_vec_range(range_a1);
                    vec_digi_erase_range(&range_a1);
                    iter = b.erase(first_b1, last_b1);
                    print_vec(&a);
                    size_t idx = vec_digi_it_index(&range_a1);
                    LOG("iter at %zu\n", idx);
                    print_vector(b);
                    long dist = std::distance(b.begin(), iter);
                    LOG("vs iter at %ld\n", dist);
                    assert((long)idx == dist);
                    // CHECK_RANGE(range_a1, iter, last_b1);
                }
                CHECK(a, b);
                break;
            }
            case TEST_INSERT: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
                    b.insert(b.begin() + index, DIGI{vb});
                    it = vec_digi_begin(&a);
                    vec_digi_it_advance(&it, index);
                    vec_digi_insert(&it, digi_init(vb));
                }
                break;
            }
            case TEST_INSERT_INDEX: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
                    const size_t i = TEST_RAND(a.size);
                    b.insert(b.begin() + i, DIGI{vb});
                    vec_digi_insert_index(&a, i, digi_init(vb));
                }
                break;
            }
            case TEST_INSERT_COUNT: {
                size_t count = TEST_RAND(512);
                b.insert(b.begin() + index, count, DIGI{value});
                it = vec_digi_begin(&a);
                vec_digi_it_advance(&it, index);
                vec_digi_insert_count(&it, count, digi_init(value));
                vec_digi_reserve(&a, b.capacity()); // our growth strategy
                                                    // is better. but for
                                                    // test sake adjust it
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_RANGE: {
                if (a.size > 2)
                {
                    print_vec(&a);
                    size_t size2 = TEST_RAND(TEST_MAX_SIZE);
                    aa = vec_digi_init_from(&a);
                    for (size_t pushes = 0; pushes < size2; pushes++)
                    {
                        const int vb = TEST_RAND(TEST_MAX_VALUE);
                        vec_digi_push_back(&aa, digi_init(vb));
                        bb.push_back(DIGI{vb});
                    }
                    print_vec(&aa);
                    get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                    it = vec_digi_begin(&a);
                    vec_digi_it_advance(&it, index);
                    b.insert(b.begin() + index, first_b2, last_b2);
                    vec_digi_insert_range(&it, &range_a2);
                    // our growth strategy is better. but for test sake adjust it
                    ADJUST_CAP("insert", a, b);
                    print_vec(&a);
                    print_vector(b);
                    CHECK(a, b);
                    vec_digi_free(&aa);
                }
                break;
            }
            case TEST_ASSIGN_RANGE: {
                print_vec(&a);
                aa = vec_digi_init_from(&a);
                gen_vectors(&aa, bb, TEST_RAND(a.size + 5));
                //print_vec(&aa);
                range_a2 = vec_digi_begin(&aa);
                // TEST grow or shrink
                vec_digi_assign_range(&a, range_a2.ref, range_a2.end); // FIXME leak
                b.assign(bb.begin(), bb.end());
                ADJUST_CAP("assign_range", a, b);
                print_vec(&a);
                //print_vector(b);
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
            case TEST_ASSIGN_GENERIC: {
                print_vec(&a);
                aa = vec_digi_init_from(&a);
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                //print_vec(&aa);
                range_a2 = vec_digi_begin(&aa);
                vec_digi_assign_generic(&a, &range_a2); // FIXME leak
                b.assign(bb.begin(), bb.end());
                ADJUST_CAP("assign_generic", a, b);
                print_vec(&a);
                //print_vector(b);
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_INSERT_GENERIC: {
                print_vec(&a);
                aa = vec_digi_init_from(&a);
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                print_vec(&aa);
                it = vec_digi_begin(&a);
                range_a2 = vec_digi_begin(&aa);
                vec_digi_insert_generic(&it, &range_a2);
                b.insert(b.begin(), bb.begin(), bb.end());
                ADJUST_CAP("insert", a, b);
                print_vec(&a);
                //print_vector(b);
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
#endif
            case TEST_RESIZE: {
                const size_t resize = 3 * index + 1;
                b.resize(resize);
                LOG("STL resize by %zu %zu -> %zu\n", resize, b.size(), b.capacity());
                vec_digi_resize(&a, resize, digi_init(0));
                LOG("CTL resize by %zu %zu -> %zu\n", resize, a.size, a.capacity);
                break;
            }
            case TEST_RESERVE: {
                const size_t capacity = 3 * TEST_RAND(a.capacity) + 1;
                b.reserve(capacity);
                vec_digi_reserve(&a, capacity);
                LOG("CTL reserve by %zu %zu\n", capacity, a.capacity);
                LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                break;
            }
            case TEST_SHRINK_TO_FIT: {
                b.shrink_to_fit();
                vec_digi_shrink_to_fit(&a);
                LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                break;
            }
            case TEST_SORT: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                break;
            }
            case TEST_COPY: {
                aa = vec_digi_copy(&a);
                bb = b;
                CHECK(aa, bb);
                vec_digi_free(&aa);
                break;
            }
            case TEST_ASSIGN: {
                size_t assign_size = index + 1;
                vec_digi_assign(&a, assign_size, digi_init(value));
                b.assign(assign_size, DIGI{value});
                break;
            }
            case TEST_SWAP: {
                LOG("CTL capacity %zu\n", a.capacity);
                LOG("STL capacity %zu\n", b.capacity());
                aa = vec_digi_copy(&a);
                aaa = vec_digi_init();
                LOG("CTL capacity %zu copy %zu\n", aa.capacity, aa.size);
                LOG("CTL capacity %zu init\n", aaa.capacity);
                bb = b;
                vec_digi_swap(&aaa, &aa);
                LOG("CTL capacity %zu after swap %zu\n", aaa.capacity, aaa.size);
                std::swap(bb, bbb);
                LOG("STL capacity %zu after swap %zu\n", bbb.capacity(), bbb.size());
                CHECK(aaa, bbb);
                vec_digi_free(&aaa);
                break;
            }
            case TEST_REMOVE_IF: {
                vec_digi_remove_if(&a, digi_is_odd);
                b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                break;
            }
            case TEST_ERASE_IF: {
#if __cpp_lib_erase_if >= 202002L
                num_a = vec_digi_erase_if(&a, digi_is_odd);
                num_b = std::erase_if(b, DIGIc_is_odd);
                assert(num_a == num_b);
#else
                vec_digi_erase_if(&a, digi_is_odd);
                b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
#endif
                break;
            }
            case TEST_EQUAL: {
                aa = vec_digi_copy(&a);
                bb = b;
                assert(vec_digi_equal(&a, &aa));
                assert(b == bb);
                vec_digi_free(&aa);
                break;
            }
            case TEST_FIND: {
                if (a.size > 0)
                {
                    int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE) : *vec_digi_at(&a, index)->value;
                    digi key = digi_init(vb);
                    it = vec_digi_find(&a, key);
                    iter = find(b.begin(), b.end(), DIGI{vb});
                    found_a = !vec_digi_it_done(&it);
                    found_b = iter != b.end();
                    assert(found_a == found_b);
                    if (found_a && found_b)
                        assert(*(it.ref->value) == *iter->value);
                    digi_free(&key);
                }
                break;
            }
            case TEST_FIND_IF: {
                it = vec_digi_find_if(&a, digi_is_odd);
                iter = std::find_if(b.begin(), b.end(), DIGI_is_odd);
                if (iter == b.end())
                    assert(vec_digi_it_done(&it));
                else
                    assert(*(it.ref->value) == *iter->value);
                break;
            }
            case TEST_FIND_IF_NOT: {
                it = vec_digi_find_if_not(&a, digi_is_odd);
                iter = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
                print_vec(&a);
                print_vector(b);
                CHECK_ITER(it, b, iter);
                if (iter == b.end())
                    assert(vec_digi_it_done(&it));
                else
                    assert(*(it.ref->value) == *iter->value);
                break;
            }
            case TEST_ALL_OF: {
                found_a = vec_digi_all_of(&a, digi_is_odd);
                found_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF: {
                found_a = vec_digi_any_of(&a, digi_is_odd);
                found_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF: {
                found_a = vec_digi_none_of(&a, digi_is_odd);
                found_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT: {
                num_a = vec_digi_count(&a, digi_init(value));
                num_b = std::count(b.begin(), b.end(), DIGI{value});
                assert(num_a == num_b);
                break;
            }
            case TEST_COUNT_IF: {
                num_a = vec_digi_count_if(&a, digi_is_odd);
                num_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
                assert(num_a == num_b);
                break;
            }
            case TEST_FIND_RANGE: {
                int vb = pick_random(&a);
                digi key = digi_init(vb);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_digi_find_range(&range_a1, key);
                iter = find(first_b1, last_b1, vb);
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                CHECK_RANGE(range_a1, iter, last_b1);
                digi_free(&key); // special
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_digi_find_if_range(&range_a1, digi_is_odd);
                iter = find_if(first_b1, last_b1, DIGI_is_odd);
                print_vec(&a);
                print_vector(b);
                CHECK_RANGE(it, iter, last_b1);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_digi_find_if_not_range(&range_a1, digi_is_odd);
                iter = find_if_not(first_b1, last_b1, DIGI_is_odd);
                CHECK_RANGE(it, iter, last_b1);
                break;
            }
            case TEST_ALL_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_digi_all_of_range(&range_a1, digi_is_odd);
                found_b = all_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_vec(&a);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_digi_any_of_range(&range_a1, digi_is_odd);
                found_b = any_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_vec(&a);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_digi_none_of_range(&range_a1, digi_is_odd);
                found_b = none_of(first_b1, last_b1, DIGI_is_odd);
                if (found_a != found_b)
                {
                    print_vec(&a);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                num_a = vec_digi_count_if_range(&range_a1, digi_is_odd);
                num_b = count_if(first_b1, last_b1, DIGI_is_odd);
                if (num_a != num_b)
                {
                    print_vec(&a);
                    print_vector(b);
                    printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                    fail++;
                }
                assert(num_a == num_b); // failed off by one, counts one too much
                break;
            }
            case TEST_COUNT_RANGE: {
                int vb = TEST_RAND(2) ? value : 0;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                // used to fail with 0,0 of 0
                num_a = vec_digi_count_range(&range_a1, digi_init(vb));
                num_b = count(first_b1, last_b1, DIGI{vb});
                assert(num_a == num_b);
                break;
            }
            case TEST_GENERATE: {
                digi_generate_reset();
                vec_digi_generate(&a, digi_generate);
                digi_generate_reset();
                std::generate(b.begin(), b.end(), DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_SEARCH: // 51
            {
                print_vec(&a);
                aa = vec_digi_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    size_t i = first_b2 - bb.begin();
                    vec_digi_set(&aa, i, digi_init(0));
                    bb[i] = DIGI{0};
                }
                print_vec_range(range_a2);
                it = vec_digi_search(&a, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", vec_digi_it_done(&it) ? "no" : "yes");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                CHECK_ITER(it, b, iter);
                vec_digi_free(&aa);
                break;
            }
            case TEST_SEARCH_RANGE: {
                aa = vec_digi_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    size_t i = first_b2 - bb.begin();
                    vec_digi_set(&aa, i, digi_init(0));
                    bb[i] = DIGI{0};
                }
                print_vec_range(range_a2);
                it = vec_digi_begin(&a);
                found_a = vec_digi_search_range(&it, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                found_b = iter != b.end();
                LOG("found a: %s\n", found_a ? "yes" : "no");
                LOG("found b: %s\n", found_b ? "yes" : "no");
                assert(found_a == found_b);
                CHECK_ITER(it, b, iter);
                vec_digi_free(&aa);
                break;
            }
            case TEST_SEARCH_N: {
                print_vec(&a);
                size_t count = TEST_RAND(4);
                const int vb = pick_random(&a);
                LOG("search_n %zu %d\n", count, value);
                it = vec_digi_search_n(&a, count, digi_init(vb));
                iter = search_n(b.begin(), b.end(), count, DIGI{vb});
                CHECK_ITER(it, b, iter);
                LOG("found %s at %zu\n", vec_digi_it_done(&it) ? "no" : "yes",
                    vec_digi_it_index(&it));
                break;
            }
            case TEST_SEARCH_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t count = TEST_RAND(4);
                const int vb = pick_random(&a);
                LOG("search_n_range %zu %d\n", count, vb);
                print_vec_range(range_a1);
                pos = vec_digi_search_n_range(&range_a1, count, digi_init(vb));
                iter = search_n(first_b1, last_b1, count, DIGI{vb});
                CHECK_RANGE(*pos, iter, last_b1);
                LOG("found %s at %zu\n", vec_digi_it_done(pos) ? "no" : "yes",
                    vec_digi_it_index(pos));
                break;
            }
            case TEST_ADJACENT_FIND: {
                print_vec(&a);
                it = vec_digi_adjacent_find(&a);
                iter = adjacent_find(b.begin(), b.end());
                CHECK_ITER(it, b, iter);
                LOG("found %s\n", vec_digi_it_done(&it) ? "no" : "yes");
                break;
            }
            case TEST_ADJACENT_FIND_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                pos = vec_digi_adjacent_find_range(&range_a1);
                iter = adjacent_find(first_b1, last_b1);
                CHECK_ITER(*pos, b, iter);
                LOG("found %s\n", vec_digi_it_done(pos) ? "no" : "yes");
                break;
            }
            case TEST_LOWER_BOUND: // 64
            {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                const int vb = pick_random(&a);
                it = vec_digi_lower_bound(&a, digi_init(vb));
                iter = lower_bound(b.begin(), b.end(), DIGI{vb});
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", vb, *it.ref->value, *iter->value);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_UPPER_BOUND: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                const int vb = pick_random(&a);
                it = vec_digi_upper_bound(&a, digi_init(vb));
                iter = upper_bound(b.begin(), b.end(), DIGI{vb});
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", vb, *it.ref->value, *iter->value);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_LOWER_BOUND_RANGE: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                const int vb = pick_random(&a);
                pos = vec_digi_lower_bound_range(&range_a1, digi_init(vb));
                iter = lower_bound(first_b1, last_b1, DIGI{vb});
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", vb, *pos->ref->value, *iter->value);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_UPPER_BOUND_RANGE: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                const int vb = pick_random(&a);
                pos = vec_digi_upper_bound_range(&range_a1, digi_init(vb));
                iter = upper_bound(first_b1, last_b1, DIGI{vb});
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", vb, *pos->ref->value, *iter->value);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_GENERATE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                digi_generate_reset();
                vec_digi_generate_range(&range_a1, digi_generate);
                digi_generate_reset();
                std::generate(first_b1, last_b1, DIGI_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM: {
                aa = vec_digi_transform(&a, digi_untrans);
                bb.resize(b.size());
                std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
            case TEST_EMPLACE_BACK: // 36
            {
#if __cplusplus >= 201103L
                b.emplace_back(DIGI{value});
#else
                b.insert(b.begin() + index, DIGI{value});
#endif
                digi key = digi_init(value);
                vec_digi_emplace_back(&a, &key);
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_EMPLACE: // 37
            {
                it = vec_digi_begin(&a);
                vec_digi_it_advance(&it, index);
#if __cplusplus >= 201103L
                b.emplace(b.begin() + index, DIGI{value});
#else
                b.insert(b.begin() + index, DIGI{value});
#endif
                digi key = digi_init(value);
                vec_digi_emplace(&it, &key);
                CHECK(a, b);
                break;
            }
#endif // DEBUG
            case TEST_INCLUDES: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                found_a = vec_digi_includes(&a, &aa);
                found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                assert(found_a == found_b);
                CHECK(aa, bb);
                vec_digi_free(&aa);
                break;
            }
            case TEST_INCLUDES_RANGE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a - aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                found_a = vec_digi_includes_range(&range_a1, &range_a2);
                LOG("STL b + bb\n");
                print_vector(b);
                print_vector(bb);
                found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
                assert(found_a == found_b);
                CHECK(aa, bb);
                vec_digi_free(&aa);
                break;
            }
            case TEST_UNION: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_digi_union(&a, &aa);
#ifndef _MSC_VER
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                LOG("STL b + bb => bbb\n");
                print_vector(b);
                print_vector(bb);
                print_vector(bbb);
                LOG("CTL a + aaa => aaa\n");
                CHECK(aa, bb);
                print_vec(&a);
                print_vec(&aa);
                print_vec(&aaa);
                ADJUST_CAP("union", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_digi_intersection(&a, &aa);
#ifndef _MSC_VER
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("intersection", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                print_vec(&a);
                print_vec(&aa);
                print_vec(&aaa);
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                print_vec(&a);
                aaa = vec_digi_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_digi_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_UNION_RANGE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_digi_union_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_vec(&aaa);

                LOG("STL b + bb\n");
                print_vector(b);
                print_vector(bb);
#ifndef _MSC_VER
                std::set_union(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_vector(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("union_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_INTERSECTION_RANGE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_digi_intersection_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_vec(&aaa);

                LOG("STL b + bb\n");
                print_vector(b);
                print_vector(bb);
#ifndef _MSC_VER
                std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_vector(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("intersection_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_DIFFERENCE_RANGE: {
                gen_vectors(&aa, bb, index);
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_digi_difference_range(&range_a1, &range_a2);
                LOG("CTL => aaa (%zu)\n", aa.size);
                print_vec(&aaa);

                LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
                print_vector(b);
                print_vector(bb);
#ifndef _MSC_VER
                std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb (%zu)\n", bbb.size());
                print_vector(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_digi_sort(&a);
                vec_digi_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_digi_symmetric_difference_range(&range_a1, &range_a2);
                LOG("CTL => aaa\n");
                print_vec(&aaa);

                LOG("STL b + bb\n");
                print_vector(b);
                print_vector(bb);
#ifndef _MSC_VER
                std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                print_vector(bbb);
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aaa);
                vec_digi_free(&aa);
                break;
            }
            case TEST_GENERATE_N: {
                size_t count = TEST_RAND(20);
                LOG("generate_n %zu\n", count);
#ifndef _MSC_VER
                digi_generate_reset();
                vec_digi_generate_n(&a, count, digi_generate);
                print_vec(&a);
                digi_generate_reset();
                // FIXME The STL is arguably broken here.
                int n = MIN(count, b.size());
                b.erase(b.begin(), b.begin() + n);
                std::generate_n(std::inserter(b, b.begin()), n, DIGI_generate);
                print_vector(b);
                CHECK(a, b);
#endif
                break;
            }
            case TEST_IOTA:
            {
                digi key = digi_init(0);
                vec_digi_iota(&a, key);
                print_vec(&a);
                std::iota(b.begin(), b.end(), DIGI{0});
                print_vector(b);
                CHECK(a, b);
                digi_free(&key);
                break;
            }
            case TEST_IOTA_RANGE:
            {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                digi key = digi_init(0);
                vec_digi_iota_range(&range_a1, key);
                print_vec_range(range_a1);
                std::iota(first_b1, last_b1, DIGI{0});
                print_vector(b);
                CHECK(a, b);
                digi_free(&key);
                break;
            }
#ifdef DEBUG
            case TEST_GENERATE_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t off = first_b1 - b.begin();
                size_t count = TEST_RAND(20 - off);
                digi_generate_reset();
                vec_digi_generate_n_range(&range_a1, count, digi_generate);
                digi_generate_reset();
                std::generate_n(first_b1, count, DIGI_generate);
                CHECK(a, b);
                break;
            }
#endif // DEBUG
            case TEST_TRANSFORM_IT: {
                print_vec(&a);
                if (a.size < 2)
                    break;
                it = vec_digi_begin(&a);
                vec_digi_it_advance(&it, 1);
                aa = vec_digi_transform_it(&a, &it, digi_bintrans);
                print_vec(&aa);
#ifndef _MSC_VER
                bb.reserve(b.size() - 1);
                std::transform(b.begin(), b.end() - 1, b.begin() + 1, std::back_inserter(bb), DIGI_bintrans);
                print_vector(bb);
                ADJUST_CAP("transform_it", aa, bb);
                CHECK(aa, bb);
#endif
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
            case TEST_TRANSFORM_RANGE: {
                print_vec(&a);
                if (a.size < 2)
                    break;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = vec_digi_init();
                vec_digi_resize(&aa, last_b1 - first_b1, digi_init(0));
                vec_digi_it dest = vec_digi_begin(&aa);
                vec_digi_transform_range(&range_a1, dest, digi_untrans);
#ifndef _MSC_VER
                bb.reserve(last_b1 - first_b1);
                std::transform(first_b1, last_b1, std::back_inserter(bb), DIGI_untrans);
                ADJUST_CAP("transform_range", aa, bb);
                CHECK(aa, bb);
#endif
                // check heap use-after-free
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
#ifdef DEBUG
            case TEST_TRANSFORM_IT_RANGE: {
                if (a.size < 2)
                    break;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_digi_begin(&a);
                vec_digi_it_advance(&it, 1);
                aa = vec_digi_init();
                vec_digi_resize(&aa, last_b1 - first_b1, digi_init(0));
                range_a2 = vec_digi_begin(&aa);
                vec_digi_transform_it_range(&range_a1, &it, range_a2, digi_bintrans);
                iter = b.begin();
                std::advance(iter, 1);
#ifndef _MSC_VER
                bb.reserve(last_b1 - first_b1 - 1);
                std::transform(first_b1, last_b1 - 1, iter, std::back_inserter(bb), DIGI_bintrans);
                ADJUST_CAP("transform_it_range", aa, bb);
                CHECK(aa, bb);
#endif
                // heap use-after-free?
                CHECK(a, b);
                vec_digi_free(&aa);
                break;
            }
#endif // DEBUG
            case TEST_COPY_IF: {
                aa = vec_digi_copy_if(&a, digi_is_odd);
/*
#if __cplusplus >= 202002L
                auto bb = a | std::ranges::views::filter(DIGI_is_odd);
                std::ranges::copy(bb, std::back_inserter(bb));
                ADJUST_CAP("filter_range", aa, bb);
                CHECK(aa, bb);
#endif
*/
#if __cplusplus >= 201103L && !defined(_MSC_VER)
                std::copy_if(b.begin(), b.end(), std::back_inserter(bb), DIGI_is_odd);
#else
                for (auto &d: b) {
                    if (DIGI_is_odd(d))
                        bb.push_back(d);
                }
#endif
                ADJUST_CAP("copy_if", aa, bb);
                CHECK(aa, bb);
                vec_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_COPY_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = vec_digi_copy_if_range(&range_a1, digi_is_odd);
#if __cplusplus >= 201103L && !defined(_MSC_VER)
                std::copy_if(first_b1, last_b1, std::back_inserter(bb), DIGI_is_odd);
#else
                for (auto d = first_b1; d != last_b1; d++) {
                    if (DIGI_is_odd(*d))
                        bb.push_back(*d);
                }
#endif
                ADJUST_CAP("copy_if_range", aa, bb);
                CHECK(aa, bb);
                vec_digi_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_MISMATCH: {
                if (a.size < 2)
                    break;
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_digi_it b1, b2;
                b1 = vec_digi_begin(&a);
                b2 = vec_digi_begin(&aa);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                /*found_a = */ vec_digi_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
                if (!bb.size() || !distance(first_b2, last_b2))
                {
                    printf("skip std::mismatch with empty 2nd range. use C++14\n");
                    vec_digi_free(&aa);
                    break;
                }
                auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
                int d1a = vec_digi_it_distance(&b1, &range_a1);
                int d2a = vec_digi_it_distance(&b2, &range_a2);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                // TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                vec_digi_free(&aa);
                break;
            }
            case TEST_EQUAL_VALUE: {
                size_t size1 = MIN(TEST_RAND(a.size), 5);
                vec_digi_resize(&a, size1, digi_init(0));
                b.resize(size1);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t i = TEST_RAND(a.size - 1);
                int vb = a.size ? *a.vector[i].value : 0;
                LOG("equal_value %d\n", vb);
                print_vec_range(range_a1);
                found_a = vec_digi_equal_value(&range_a1, digi_init(vb));
                found_b = first_b1 != last_b1;
                for (; first_b1 != last_b1; first_b1++)
                {
                    if (vb != *(*first_b1).value)
                    {
                        found_b = false;
                        break;
                    }
                }
                LOG("found_a: %d found_b: %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_EQUAL_RANGE: {
                aa = vec_digi_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                found_a = vec_digi_equal_range(&range_a1, &range_a2);
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
                vec_digi_free(&aa);
                break;
            }
            case TEST_LEXICOGRAPHICAL_COMPARE: {
                aa = vec_digi_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                found_a = vec_digi_lexicographical_compare(&range_a1, &range_a2);
                found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
                LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                vec_digi_free(&aa);
                break;
            }
            case TEST_FIND_FIRST_OF: {
                gen_vectors(&aa, bb, TEST_RAND(15));
                range_a2 = vec_digi_begin(&aa);
                it = vec_digi_find_first_of(&a, &range_a2);
                iter = std::find_first_of(b.begin(), b.end(), bb.begin(), bb.end());
                print_vec(&a);
                print_vec(&aa);
                LOG("=> %zu vs %ld\n", vec_digi_it_index(&it), iter - b.begin());
                CHECK_ITER(it, b, iter);
                vec_digi_free(&aa);
                break;
            }
            case TEST_FIND_FIRST_OF_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(15));
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                found_a = vec_digi_find_first_of_range(&range_a1, &range_a2);
                iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                    iter != last_b1 ? "yes" : "no", range_a1.ref - a.vector,
                    iter - b.begin());
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                vec_digi_free(&aa);
                break;
            }
            case TEST_FIND_END: {
                gen_vectors(&aa, bb, TEST_RAND(4));
                range_a2 = vec_digi_begin(&aa);
                print_vec(&a);
                print_vec(&aa);
                it = vec_digi_find_end(&a, &range_a2);
                iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
                found_a = !vec_digi_it_done(&it);
                found_b = iter != b.end();
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                    iter - b.begin());
                CHECK_ITER(it, b, iter);
                assert(found_a == found_b);
                vec_digi_free(&aa);
                break;
            }
            case TEST_FIND_END_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                gen_vectors(&aa, bb, TEST_RAND(4));
                range_a2 = vec_digi_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
                it = vec_digi_find_end_range(&range_a1, &range_a2);
                iter = find_end(first_b1, last_b1, bb.begin(), bb.end());
                CHECK_ITER(it, b, iter);
#endif
                vec_digi_free(&aa);
                break;
            }
            case TEST_UNIQUE: {
                print_vec(&a);
                digi *orig_end = &a.vector[a.size];
                it = vec_digi_unique(&a);
                found_a = it.end < orig_end;
                size_t idx = vec_digi_it_index(&it);
                print_vec(&a);
                // C++ is special here with its move hack
                iter = unique(b.begin(), b.end());
                found_b = iter != b.end();
                long dist = std::distance(b.begin(), iter);
                b.resize(dist);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", idx);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_vector(b);
                assert(found_a == found_b);
                assert((long)idx == dist);
                break;
            }
            case TEST_UNIQUE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                digi *orig_end = range_a1.end;
                it = vec_digi_unique_range(&range_a1);
                found_a = it.end < orig_end;
                size_t idx = vec_digi_it_index(&it);
                iter = unique(first_b1, last_b1);
                found_b = iter != last_b1;
                long dist = std::distance(b.begin(), iter);
                if (found_b)
                    b.erase(iter, last_b1);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", idx);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_vec(&a);
                print_vector(b);
                assert(found_a == found_b);
                assert((long)idx == dist);
                break;
            }
            case TEST_BINARY_SEARCH: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                int key = pick_random(&a);
                found_a = vec_digi_binary_search(&a, digi_init(key));
                found_b = binary_search(b.begin(), b.end(), DIGI{key});
                LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_BINARY_SEARCH_RANGE: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                int key = pick_random(&a);
                found_a = vec_digi_binary_search_range(&range_a1, digi_init(key));
                found_b = binary_search(first_b1, last_b1, DIGI{key});
                LOG("%d: %d vs %d\n", key, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_MERGE: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_digi_sort(&aa);
                std::sort(bb.begin(), bb.end());

                aaa = vec_digi_merge(&a, &aa);
#ifndef _MSC_VER
                merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aa);
                vec_digi_free(&aaa);
                break;
            }
            case TEST_MERGE_RANGE: {
                vec_digi_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_digi_sort(&aa);
                std::sort(bb.begin(), bb.end());
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                aaa = vec_digi_merge_range(&range_a1, &range_a2);
#ifndef _MSC_VER
                merge(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                vec_digi_free(&aa);
                vec_digi_free(&aaa);
                break;
            }
            case TEST_IS_SORTED: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec(&a);
                found_a = vec_digi_is_sorted(&range_a1);
                found_b = std::is_sorted(first_b1, last_b1);
                LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_IS_SORTED_UNTIL: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                range_a2 = range_a1;
                range_a2.ref = range_a1.end;
                pos = vec_digi_is_sorted_until(&range_a1, &range_a2);
                first_b1 = std::is_sorted_until(first_b1, last_b1);
                CHECK_RANGE(*pos, first_b1, last_b1);
                break;
            }
            case TEST_REVERSE: {
                print_vec(&a);
                vec_digi_reverse(&a);
                reverse(b.begin(), b.end());
                print_vec(&a);
                print_vector(b);
                CHECK(a, b);
                break;
            }
            case TEST_REVERSE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                vec_digi_reverse_range(&range_a1);
                std::reverse(first_b1, last_b1);
                print_vec(&a);
                print_vector(b);
                CHECK(a, b);
                break;
            }

            default:
                fail++;
#ifdef DEBUG
                printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
                printf("unhandled testcase %d\n", which);
#endif
                break;
            }
            CHECK(a, b);
            vec_digi_free(&a);
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
