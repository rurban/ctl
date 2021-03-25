#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#define POD
#define T int
#include <ctl/vector.h>

#include <algorithm>
#include <vector>
#include <numeric>

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
    TEST(EMPLACE_BACK)                                                                                                 \
    TEST(RESIZE)                                                                                                       \
    TEST(RESERVE)                                                                                                      \
    TEST(SHRINK_TO_FIT)                                                                                                \
    TEST(SORT)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(SWAP)                                                                                                         \
    TEST(ASSIGN)                                                                                                       \
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
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
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
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(REVERSE)                                                                                                      \
    TEST(REVERSE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(EMPLACE) /* 76 */                                                                                             \
    TEST(GENERATE_N_RANGE)                                                                                             \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(TRANSFORM_IT_RANGE)                                                                                           \
    TEST(INPLACE_MERGE)

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

int is_odd(int *a)
{
    return *a % 2;
}

int stl_is_odd(int a)
{
    return a % 2;
}

static int _generator_state = 0;
void int_generate_reset()
{
    _generator_state = 0.0;
}
int int_generate(void)
{
    _generator_state += 1.0;
    return _generator_state;
}
int int_untrans(int *v)
{
    return *v >> 1;
}
int INT_untrans(int &v)
{
    return v >> 1;
}
int int_bintrans(int *v1, int *v2)
{
    return *v1 ^ *v2;
}
int INT_bintrans(int &v1, int &v2)
{
    return v1 ^ v2;
}

void print_vec(vec_int *a)
{
    vec_foreach(int, a, ref) printf("%d ", *ref);
    printf("\n");
}

void print_vec_range(vec_int_it it)
{
    if (vec_int_empty(it.container))
        return;
    vec_int_it begin = vec_int_begin(it.container);
    int *ref = it.ref;
    long i1 = it.ref - begin.ref;
    long i2 = begin.end - it.ref;
    if (i1)
    {
        while (begin.ref != it.ref)
        {
            printf("%d ", *begin.ref);
            begin.ref++;
        }
    }
    printf("[");
    while (!vec_int_it_done(&it))
    {
        printf("%d ", *it.ref);
        vec_int_it_next(&it);
    }
    printf(") ");
    if (i2)
    {
        begin.ref = it.ref;
        while (begin.ref != begin.end)
        {
            printf("%d ", *begin.ref);
            begin.ref++;
        }
    }
    it.ref = ref;
    printf("\n");
}

void print_vector(std::vector<int> &b)
{
    for (auto &d : b)
        printf("%d ", d);
    printf("\n");
}

#ifdef DEBUG
#define TEST_MAX_VALUE INT_MAX
//#define TEST_MAX_VALUE 1000
#else
#define print_vec(x)
#define print_vec_range(x)
#define print_vector(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int middle(vec_int *a)
{
    if (!a->size)
        return 0;
    return (*vec_int_front(a) - *vec_int_back(a)) / 2;
}

int median(vec_int *a)
{
    vec_int_it it = vec_int_begin(a);
    vec_int_it_advance(&it, a->size / 2);
    return a->size ? *it.ref : 0;
}

int pick_element(vec_int *a)
{
    const size_t index = TEST_RAND(a->size);
    return a->size ? *vec_int_at(a, index) : 0;
}

int pick_random(vec_int *a)
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

// cheat growth
#define ADJUST_CAP(m, c, s)                                                                                            \
    if (c.size == s.size() && c.capacity != s.capacity())                                                              \
    {                                                                                                                  \
        LOG("%s capacity %zu => %zu FAIL\n", m, c.capacity, s.capacity());                                          \
        vec_int_fit(&c, s.capacity());                                                                                 \
    }

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        ASSERT_EQUAL_CAP(_x, _y)                                                                                       \
        assert(_x.size == _y.size());                                                                                  \
        assert(vec_int_empty(&_x) == _y.empty());                                                                      \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            assert(_y.front() == *vec_int_front(&_x));                                                                 \
            assert(_y.back() == *vec_int_back(&_x));                                                                   \
        }                                                                                                              \
        std::vector<int>::iterator _iter = _y.begin();                                                                 \
        vec_foreach(int, &_x, _ref)                                                                                    \
        {                                                                                                              \
            assert(*_ref == *_iter);                                                                                   \
            _iter++;                                                                                                   \
        }                                                                                                              \
        int *_it = vec_int_front(&_x);                                                                                 \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_it == _d);                                                                                        \
            _it++;                                                                                                     \
        }                                                                                                              \
        for (size_t i = 0; i < _y.size(); i++)                                                                         \
            assert(_y.at(i) == *vec_int_at(&_x, i));                                                                   \
    }

#define CHECK_REF(_ref, b, _iter)                                                                                      \
    if (_iter != b.end())                                                                                              \
    assert(*_ref == *_iter)

#define CHECK_ITER(_it, b, _iter)                                                                                      \
    if ((_it).ref != &(_it).container->vector[(_it).container->size])                                                  \
    {                                                                                                                  \
        assert(_iter != b.end());                                                                                      \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!vec_int_it_done(&_it))                                                                                        \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

static void gen_vectors(vec_int *a, std::vector<int> &b, size_t size)
{
    *a = vec_int_init();
    for (int i = 0; i < (int)size; i++)
    {
        vec_int_push_back(a, i);
        b.push_back(i);
    }
}

static void get_random_iters(vec_int *a, vec_int_it *first_a, std::vector<int> &b, std::vector<int>::iterator &first_b,
                             std::vector<int>::iterator &last_b)
{
    vec_int_it last_a;
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        vec_int_it it1 = vec_int_begin(a);
        first_b = b.begin();
        vec_int_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            last_a = vec_int_end(a);
            last_b = b.end();
        }
        else
        {
            vec_int_it it2 = vec_int_begin(a);
            last_b = b.begin();
            vec_int_it_advance(&it2, r2);
            last_b += r2;
            last_a = it2;
        }
    }
    else
    {
        vec_int_it end = vec_int_end(a);
        *first_a = end;
        last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a.ref;
}

int main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10,false);
    int log = getenv("LOG") ? 1 : 0;
    int SAFE_DEBUG = getenv("SAFE_DEBUG") ? 1 : 0;
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
            vec_int a, aa, aaa;
            std::vector<int> b, bb, bbb;
            vec_int_it range_a1, range_a2, it;
            vec_int_it *pos;
            std::vector<int>::iterator first_b1, last_b1, first_b2, last_b2, iter;
            bool found_a, found_b;
            size_t num_a, num_b;
            int value = TEST_RAND(TEST_MAX_VALUE);
            size_t index = TEST_RAND(size);

            a = vec_int_init();
            if (mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                vec_int_resize(&a, size, 0);
                b.resize(size);
                for (int i = 0; i < (int)size; i++)
                {
#ifdef DEBUGxx
                    const int vb = i;
#else
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
#endif
                    vec_int_set(&a, i, vb);
                    b[i] = vb;
                }
            }
            if (mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for (size_t pushes = 0; pushes < size; pushes++)
                {
                    const int vb = TEST_RAND(INT_MAX);
                    vec_int_push_back(&a, vb);
                    b.push_back(vb);
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
            if (log)
            {
                printf("TEST=%d (size %zu, cap %zu)\n", which, a.size, a.capacity);
            }
            if (SAFE_DEBUG)
            {
                if (which > TEST_ADJACENT_FIND_RANGE)
                    which = 0;
            }
            LOG("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            RECORD_WHICH;
            switch (which)
            {
            case TEST_PUSH_BACK: {
                b.push_back(value);
                vec_int_push_back(&a, value);
                break;
            }
            case TEST_POP_BACK: {
                if (a.size > 0)
                {
                    b.pop_back();
                    vec_int_pop_back(&a);
                }
                break;
            }
            case TEST_CLEAR: {
                b.clear();
                vec_int_clear(&a);
                break;
            }
            case TEST_ERASE: {
                if (a.size > 0)
                {
                    it = vec_int_begin(&a);
                    vec_int_it_advance(&it, index);
                    it = vec_int_erase(&it);
                    iter = b.erase(b.begin() + index);
                    CHECK_ITER(it, b, iter);
                }
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_INDEX: {
                if (a.size > 0)
                {
                    iter = b.erase(b.begin() + index);
                    it = vec_int_erase_index(&a, index);
                    CHECK_ITER(it, b, iter);
                }
                CHECK(a, b);
                break;
            }
            case TEST_ERASE_RANGE: {
                if (a.size > 1)
                {
                    get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                    print_vec_range(range_a1);
                    vec_int_erase_range(&range_a1);
                    iter = b.erase(first_b1, last_b1);
                    print_vec(&a);
                    print_vector(b);
                    CHECK_RANGE(range_a1, iter, last_b1);
                }
                CHECK(a, b);
                break;
            }
            case TEST_INSERT: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    value = TEST_RAND(TEST_MAX_VALUE);
                    b.insert(b.begin() + index, value);
                    vec_int_insert_index(&a, index, value);
                }
                break;
            }
            case TEST_INSERT_INDEX: {
                size_t amount = TEST_RAND(512);
                for (size_t count = 0; count < amount; count++)
                {
                    value = TEST_RAND(TEST_MAX_VALUE);
                    b.insert(b.begin() + index, value);
                    it = vec_int_begin(&a);
                    vec_int_it_advance(&it, index);
                    vec_int_insert(&it, value);
                }
                break;
            }
            case TEST_INSERT_COUNT: {
                size_t count = TEST_RAND(512);
                b.insert(b.begin() + index, count, value);
                it = vec_int_begin(&a);
                vec_int_it_advance(&it, index);
                vec_int_insert_count(&it, count, value);
                vec_int_reserve(&a, b.capacity()); // our growth strategy
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
                    aa = vec_int_init_from(&a);
                    for (size_t pushes = 0; pushes < size2; pushes++)
                    {
                        value = TEST_RAND(TEST_MAX_VALUE);
                        vec_int_push_back(&aa, value);
                        bb.push_back(value);
                    }
                    print_vec(&aa);
                    get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                    it = vec_int_begin(&a);
                    vec_int_it_advance(&it, index);
                    b.insert(b.begin() + index, first_b2, last_b2);
                    vec_int_insert_range(&it, &range_a2);
                    // our growth strategy is better. but for test sake adjust it
                    vec_int_reserve(&a, b.capacity());
                    print_vec(&a);
                    print_vector(b);
                    CHECK(a, b);
                    vec_int_free(&aa);
                }
                break;
            }
            case TEST_RESIZE: {
                const size_t resize = 3 * TEST_RAND(a.size) + 1;
                b.resize(resize);
                LOG("STL resize by %zu %zu -> %zu\n", resize, b.size(), b.capacity());
                vec_int_resize(&a, resize, 0);
                LOG("CTL resize by %zu %zu -> %zu\n", resize, a.size, a.capacity);
                break;
            }
            case TEST_RESERVE: {
                const size_t capacity = 3 * TEST_RAND(a.capacity) + 1;
                b.reserve(capacity);
                vec_int_reserve(&a, capacity);
                LOG("CTL reserve by %zu %zu\n", capacity, a.capacity);
                LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                break;
            }
            case TEST_SHRINK_TO_FIT:
                b.shrink_to_fit();
                vec_int_shrink_to_fit(&a);
                LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                break;
            case TEST_SORT:
                vec_int_sort(&a);
                sort(b.begin(), b.end());
                break;
            case TEST_COPY:
                aa = vec_int_copy(&a);
                bb = b;
                CHECK(aa, bb);
                vec_int_free(&aa);
                break;
            case TEST_ASSIGN: {
                size_t assign_size = TEST_RAND(a.size) + 1;
                vec_int_assign(&a, assign_size, value);
                b.assign(assign_size, value);
                break;
            }
            case TEST_SWAP:
                LOG("CTL capacity %zu\n", a.capacity);
                LOG("STL capacity %zu\n", b.capacity());
                aa = vec_int_copy(&a);
                aaa = vec_int_init();
                LOG("CTL capacity %zu copy %zu\n", aa.capacity, aa.size);
                LOG("CTL capacity %zu init\n", aaa.capacity);
                bb = b;
                vec_int_swap(&aaa, &aa);
                LOG("CTL capacity %zu after swap %zu\n", aaa.capacity, aaa.size);
                swap(bb, bbb);
                LOG("STL capacity %zu after swap %zu\n", bbb.capacity(), bbb.size());
                CHECK(aaa, bbb);
                vec_int_free(&aaa);
                break;
            case TEST_REMOVE_IF:
                vec_int_remove_if(&a, is_odd);
                b.erase(remove_if(b.begin(), b.end(), stl_is_odd), b.end());
                break;
            case TEST_ERASE_IF:
#if __cpp_lib_erase_if >= 202002L
                num_a = vec_int_erase_if(&a, is_odd);
                num_b = std::erase_if(b, stl_is_odd);
                assert(num_a == num_b);
#else
                vec_int_erase_if(&a, is_odd);
                b.erase(std::remove_if(b.begin(), b.end(), stl_is_odd), b.end());
#endif
                break;
            case TEST_EQUAL:
                aa = vec_int_copy(&a);
                bb = b;
                assert(vec_int_equal(&a, &aa));
                assert(b == bb);
                vec_int_free(&aa);
                break;
            case TEST_FIND:
                if (a.size > 0)
                {
                    value = TEST_RAND(2) ? TEST_RAND(INT_MAX) : *vec_int_at(&a, index);
                    it = vec_int_find(&a, value);
                    iter = find(b.begin(), b.end(), value);
                    found_a = !vec_int_it_done(&it);
                    found_b = iter != b.end();
                    assert(found_a == found_b);
                    if (found_a && found_b)
                        assert(*it.ref == *iter);
                }
                break;
            case TEST_FIND_IF:
                it = vec_int_find_if(&a, is_odd);
                iter = find_if(b.begin(), b.end(), stl_is_odd);
                if (iter == b.end())
                    assert(vec_int_it_done(&it));
                else
                    assert(*iter == *it.ref);
                break;
            case TEST_FIND_IF_NOT:
                it = vec_int_find_if_not(&a, is_odd);
                iter = find_if_not(b.begin(), b.end(), stl_is_odd);
                if (iter == b.end())
                    assert(vec_int_it_done(&it));
                else
                    assert(*iter == *it.ref);
                break;
            case TEST_ALL_OF:
                found_a = vec_int_all_of(&a, is_odd);
                found_b = all_of(b.begin(), b.end(), stl_is_odd);
                assert(found_a == found_b);
                break;
            case TEST_ANY_OF:
                found_a = vec_int_any_of(&a, is_odd);
                found_b = any_of(b.begin(), b.end(), stl_is_odd);
                assert(found_a == found_b);
                break;
            case TEST_NONE_OF:
                found_a = vec_int_none_of(&a, is_odd);
                found_b = none_of(b.begin(), b.end(), stl_is_odd);
                assert(found_a == found_b);
                break;
            case TEST_COUNT:
                num_a = vec_int_count(&a, value);
                num_b = count(b.begin(), b.end(), value);
                assert(num_a == num_b);
                break;
            case TEST_COUNT_IF:
                num_a = vec_int_count_if(&a, is_odd);
                num_b = count_if(b.begin(), b.end(), stl_is_odd);
                assert(num_a == num_b);
                break;
            case TEST_FIND_RANGE:
                value = pick_random(&a);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_int_find_range(&range_a1, value);
                iter = find(first_b1, last_b1, value);
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                CHECK_RANGE(range_a1, iter, last_b1);
                CHECK(a, b);
                break;
            case TEST_FIND_IF_RANGE:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_int_find_if_range(&range_a1, is_odd);
                iter = find_if(first_b1, last_b1, stl_is_odd);
                print_vec(&a);
                print_vector(b);
                CHECK_ITER(it, b, iter);
                break;
            case TEST_FIND_IF_NOT_RANGE:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_int_find_if_not_range(&range_a1, is_odd);
                iter = find_if_not(first_b1, last_b1, stl_is_odd);
                CHECK_ITER(it, b, iter);
                break;
            case TEST_ALL_OF_RANGE:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_int_all_of_range(&range_a1, is_odd);
                found_b = all_of(first_b1, last_b1, stl_is_odd);
                if (found_a != found_b)
                {
                    print_vec_range(range_a1);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            case TEST_ANY_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_int_any_of_range(&range_a1, is_odd);
                found_b = any_of(first_b1, last_b1, stl_is_odd);
                if (found_a != found_b)
                {
                    print_vec_range(range_a1);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = vec_int_none_of_range(&range_a1, is_odd);
                found_b = none_of(first_b1, last_b1, stl_is_odd);
                if (found_a != found_b)
                {
                    print_vec_range(range_a1);
                    print_vector(b);
                    printf("%d != %d is_odd\n", (int)found_a, (int)found_b);
                }
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                num_a = vec_int_count_if_range(&range_a1, is_odd);
                num_b = count_if(first_b1, last_b1, stl_is_odd);
                if (num_a != num_b)
                {
                    print_vec(&a);
                    print_vector(b);
                    printf("%d != %d FAIL\n", (int)num_a, (int)num_b);
                    fail++;
                }
                assert(num_a == num_b); // failed. off by one, counts one too much
                break;
            }
            case TEST_COUNT_RANGE: {
                value = TEST_RAND(2) ? value : 0;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                // used to fail with 0,0 of 0
                num_a = vec_int_count_range(&range_a1, value);
                num_b = count(first_b1, last_b1, value);
                assert(num_a == num_b);
                break;
            }
            case TEST_EMPLACE_BACK: {
#if __cplusplus >= 201103L
                b.emplace_back(value);
#else
                b.insert(b.begin() + index, value);
#endif
                vec_int_emplace_back(&a, &value);
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_EMPLACE: {
                it = vec_int_begin(&a);
                vec_int_it_advance(&it, index);
#if __cplusplus >= 201103L
                b.emplace(b.begin() + index, value);
#else
                b.insert(b.begin() + index, value);
#endif
                vec_int_emplace(&it, &value);
                CHECK(a, b);
                break;
            }
#endif // DEBUG
            case TEST_INCLUDES: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                found_a = vec_int_includes(&a, &aa);
                found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                assert(found_a == found_b);
                CHECK(aa, bb);
                vec_int_free(&aa);
                break;
            }
            case TEST_INCLUDES_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a - aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                found_a = vec_int_includes_range(&range_a1, &range_a2);
                LOG("STL b + bb\n");
                print_vector(b);
                print_vector(bb);
                found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
                assert(found_a == found_b);
                CHECK(aa, bb);
                vec_int_free(&aa);
                break;
            }
            case TEST_UNION: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_int_union(&a, &aa);
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
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_INTERSECTION: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_int_intersection(&a, &aa);
#ifndef _MSC_VER
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("intersection", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                print_vec(&a);
                print_vec(&aa);
                print_vec(&aaa);
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_DIFFERENCE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                print_vec(&a);
                aaa = vec_int_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = vec_int_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_UNION_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_int_union_range(&range_a1, &range_a2);
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
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_INTERSECTION_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_int_intersection_range(&range_a1, &range_a2);
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
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_DIFFERENCE_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_int_difference_range(&range_a1, &range_a2);
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
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&a);
                vec_int_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                LOG("CTL a + aa\n");
                print_vec_range(range_a1);
                print_vec_range(range_a2);
                aaa = vec_int_symmetric_difference_range(&range_a1, &range_a2);
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
                vec_int_free(&aaa);
                vec_int_free(&aa);
                break;
            }
            case TEST_GENERATE: {
                int_generate_reset();
                vec_int_generate(&a, int_generate);
                int_generate_reset();
                std::generate(b.begin(), b.end(), int_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                int_generate_reset();
                vec_int_generate_range(&range_a1, int_generate);
                int_generate_reset();
                std::generate(first_b1, last_b1, int_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM: {
                aa = vec_int_transform(&a, int_untrans);
                bb.resize(b.size());
                std::transform(b.begin(), b.end(), bb.begin(), INT_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                vec_int_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT: {
                print_vec(&a);
                if (a.size < 2)
                    break;
                it = vec_int_begin(&a);
                vec_int_it_advance(&it, 1);
                aa = vec_int_transform_it(&a, &it, int_bintrans);
                bb.resize(b.size() - 1);
                std::transform(b.begin(), b.end() - 1, b.begin() + 1, bb.begin(), INT_bintrans);
                ADJUST_CAP("transform_it", aa, bb);
                CHECK(aa, bb);
                CHECK(a, b);
                vec_int_free(&aa);
                break;
            }
            case TEST_GENERATE_N: {
                size_t count = TEST_RAND(20);
                LOG("generate_n %zu\n", count);
#ifndef _MSC_VER
                int_generate_reset();
                vec_int_generate_n(&a, count, int_generate);
                print_vec(&a);
                int_generate_reset();
                // FIXME The STL is arguably broken here.
                int n = MIN(count, b.size());
                b.erase(b.begin(), b.begin() + n);
                std::generate_n(std::inserter(b, b.begin()), n, int_generate);
                print_vector(b);
#endif
                CHECK(a, b);
                break;
            }
            case TEST_IOTA:
            {
                vec_int_iota(&a, 0);
                std::iota(b.begin(), b.end(), 0);
                CHECK(a, b);
                break;
            }
            case TEST_IOTA_RANGE:
            {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                vec_int_iota_range(&range_a1, 0);
                std::iota(first_b1, last_b1, 0);
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_GENERATE_N_RANGE: // 60
            {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t off = first_b1 - b.begin();
                size_t count = TEST_RAND(20 - off);
                int_generate_reset();
                vec_int_generate_n_range(&range_a1, count, int_generate);
                int_generate_reset();
                std::generate_n(first_b1, count, int_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM_RANGE: // 61
            {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = vec_int_init();
                range_a2 = vec_int_begin(&aa);
                it = vec_int_transform_range(&range_a1, range_a2, int_untrans);
                bb.resize(last_b1 - first_b1);
                iter = std::transform(first_b1, last_b1 - 1, b.begin() + 1, bb.begin(), INT_bintrans);
                CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                CHECK(a, b);
                vec_int_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT_RANGE: {
                if (a.size < 2)
                    break;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = vec_int_begin(&a);
                vec_int_it_advance(&it, 1);
                aa = vec_int_init();
                vec_int_resize(&aa, last_b1 - first_b1, 0);
                range_a2 = vec_int_begin(&aa);
                /* vec_int_it it = */
                vec_int_transform_it_range(&range_a1, &it, range_a2, int_bintrans);
                auto it2 = b.begin();
                std::advance(it2, 1);
#ifndef _MSC_VER
                bb.reserve(last_b1 - first_b1 - 1);
                /*auto iter =*/
                std::transform(first_b1, last_b1, it2, std::back_inserter(bb), INT_bintrans);
                ADJUST_CAP("transform_it_range", aa, bb);
                // CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
#endif
                // heap use-after-free
                CHECK(a, b);
                vec_int_free(&aa);
                break;
            }
#endif // DEBUG
            case TEST_MISMATCH: {
                if (a.size < 2)
                    break;
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_it b1, b2;
                b1 = vec_int_begin(&a);
                b2 = vec_int_begin(&aa);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                /*found_a = */ vec_int_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
                if (!bb.size() || !distance(first_b2, last_b2))
                {
                    printf("skip std::mismatch with empty 2nd range. use C++14\n");
                    vec_int_free(&aa);
                    break;
                }
                auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
                int d1a = vec_int_it_distance(&b1, &range_a1);
                int d2a = vec_int_it_distance(&b2, &range_a2);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                // TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                vec_int_free(&aa);
                break;
            }
            case TEST_SEARCH: // 51
            {
                print_vec(&a);
                aa = vec_int_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    size_t i = first_b2 - bb.begin();
                    vec_int_set(&aa, i, 0);
                    bb[i] = 0;
                }
                print_vec_range(range_a2);
                it = vec_int_search(&a, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", vec_int_it_done(&it) ? "no" : "yes");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                CHECK_ITER(it, b, iter);
                vec_int_free(&aa);
                break;
            }
            case TEST_SEARCH_RANGE: {
                aa = vec_int_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    size_t i = first_b2 - bb.begin();
                    vec_int_set(&aa, i, 0);
                    bb[i] = 0;
                }
                print_vec_range(range_a2);
                range_a1 = vec_int_begin(&a);
                found_a = vec_int_search_range(&range_a1, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", found_a ? "yes" : "no");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                assert(found_a == !vec_int_it_done(&range_a1));
                CHECK_ITER(range_a1, b, iter);
                vec_int_free(&aa);
                break;
            }
            case TEST_SEARCH_N: {
                print_vec(&a);
                size_t count = TEST_RAND(4);
                value = pick_random(&a);
                LOG("search_n %zu %d\n", count, value);
                it = vec_int_search_n(&a, count, value);
                iter = search_n(b.begin(), b.end(), count, value);
                CHECK_ITER(it, b, iter);
                LOG("found %s at %zu\n", vec_int_it_done(&it) ? "no" : "yes",
                    vec_int_it_index(&it));
                break;
            }
            case TEST_SEARCH_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t count = TEST_RAND(4);
                value = pick_random(&a);
                LOG("search_n_range %zu %d\n", count, value);
                print_vec_range(range_a1);
                pos = vec_int_search_n_range(&range_a1, count, value);
                iter = search_n(first_b1, last_b1, count, value);
                CHECK_RANGE(*pos, iter, last_b1);
                LOG("found %s at %zu\n", vec_int_it_done(pos) ? "no" : "yes",
                    vec_int_it_index(pos));
                break;
            }
            case TEST_ADJACENT_FIND: {
                print_vec(&a);
                it = vec_int_adjacent_find(&a);
                iter = adjacent_find(b.begin(), b.end());
                CHECK_ITER(it, b, iter);
                LOG("found %s\n", vec_int_it_done(&it) ? "no" : "yes");
                break;
            }
            case TEST_ADJACENT_FIND_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                pos = vec_int_adjacent_find_range(&range_a1);
                iter = adjacent_find(first_b1, last_b1);
                CHECK_ITER(*pos, b, iter);
                LOG("found %s\n", vec_int_it_done(pos) ? "no" : "yes");
                break;
            }
            case TEST_LOWER_BOUND:
            {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                it = vec_int_lower_bound(&a, value);
                iter = lower_bound(b.begin(), b.end(), value);
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", value, *it.ref, *iter);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_UPPER_BOUND: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                it = vec_int_upper_bound(&a, value);
                iter = upper_bound(b.begin(), b.end(), value);
                if (iter != b.end())
                {
                    LOG("%d: %d vs %d\n", value, *it.ref, *iter);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_LOWER_BOUND_RANGE: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                pos = vec_int_lower_bound_range(&range_a1, value);
                iter = lower_bound(first_b1, last_b1, value);
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", value, *pos->ref, *iter);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_UPPER_BOUND_RANGE: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                pos = vec_int_upper_bound_range(&range_a1, value);
                iter = upper_bound(first_b1, last_b1, value);
                if (iter != last_b1)
                {
                    LOG("%d: %d vs %d\n", value, *pos->ref, *iter);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_EQUAL_VALUE: {
                size_t size1 = MIN(TEST_RAND(a.size), 5);
                vec_int_resize(&a, size1, 0);
                b.resize(size1);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                index = TEST_RAND(a.size - 1);
                value = a.size ? a.vector[index] : 0;
                LOG("equal_value %d\n", value);
                print_vec_range(range_a1);
                found_a = vec_int_equal_value(&range_a1, value);
                found_b = first_b1 != last_b1;
                for (; first_b1 != last_b1; first_b1++)
                {
                    if (value != *first_b1)
                    {
                        found_b = false;
                        break;
                    }
                }
                LOG("found_a: %d found_b: %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_EQUAL_RANGE:
                aa = vec_int_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                found_a = vec_int_equal_range(&range_a1, &range_a2);
                found_b = std::equal(first_b1, last_b1, first_b2, last_b2);
                LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
#else
                vec_int_equal_range(&range_a1, &range_a2);
                printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
                vec_int_free(&aa);
                break;
            case TEST_LEXICOGRAPHICAL_COMPARE:
                aa = vec_int_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
//# if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                found_a = vec_int_lexicographical_compare(&range_a1, &range_a2);
                found_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
                LOG("found_a: %d found_b %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
//# else
//              vec_int_lexicographical_compare(&range_a1, &range_a2);
//              printf("std::lexicographical_compare requires C++14 with robust_nonmodifying_seq_ops\n");
//# endif
                vec_int_free(&aa);
                break;
            case TEST_FIND_FIRST_OF:
                gen_vectors(&aa, bb, TEST_RAND(15));
                range_a2 = vec_int_begin(&aa);
                it = vec_int_find_first_of(&a, &range_a2);
                iter = std::find_first_of(b.begin(), b.end(), bb.begin(), bb.end());
                print_vec(&a);
                print_vec(&aa);
                LOG("=> %zu vs %ld\n", vec_int_it_index(&it), iter - b.begin());
                CHECK_ITER(it, b, iter);
                vec_int_free(&aa);
                break;
            case TEST_FIND_FIRST_OF_RANGE:
                gen_vectors(&aa, bb, TEST_RAND(15));
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                found_a = vec_int_find_first_of_range(&range_a1, &range_a2);
                iter = std::find_first_of(first_b1, last_b1, first_b2, last_b2);
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no",
                    iter != last_b1 ? "yes" : "no", range_a1.ref - a.vector,
                    iter - b.begin());
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                vec_int_free(&aa);
                break;
            case TEST_FIND_END:
                gen_vectors(&aa, bb, TEST_RAND(4));
                range_a2 = vec_int_begin(&aa);
                print_vec(&a);
                print_vec(&aa);
                it = vec_int_find_end(&a, &range_a2);
                iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
                found_a = !vec_int_it_done(&it);
                found_b = iter != b.end();
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                    iter - b.begin());
                CHECK_ITER(it, b, iter);
                assert(found_a == found_b);
                vec_int_free(&aa);
                break;
            case TEST_FIND_END_RANGE:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                gen_vectors(&aa, bb, TEST_RAND(4));
                range_a2 = vec_int_begin(&aa);
#if __cpp_lib_erase_if >= 202002L
                it = vec_int_find_end_range(&range_a1, &range_a2);
                iter = find_end(first_b1, last_b1, bb.begin(), bb.end());
                CHECK_ITER(it, b, iter);
#endif
                vec_int_free(&aa);
                break;
            case TEST_UNIQUE: {
                print_vec(&a);
                int *orig_end = &a.vector[a.size];
                it = vec_int_unique(&a);
                found_a = it.end < orig_end;
                index = vec_int_it_index(&it);
                print_vec(&a);
                // C++ is special here with its move hack
                iter = unique(b.begin(), b.end());
                found_b = iter != b.end();
                long dist = std::distance(b.begin(), iter);
                b.resize(dist);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", index);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_vector(b);
                assert(found_a == found_b);
                assert((long)index == dist);
                break;
            }
            case TEST_UNIQUE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                int *orig_end = range_a1.end;
                it = vec_int_unique_range(&range_a1);
                found_a = it.end < orig_end;
                index = vec_int_it_index(&it);
                iter = unique(first_b1, last_b1);
                found_b = iter != last_b1;
                long dist = std::distance(b.begin(), iter);
                if (found_b)
                    b.erase(iter, last_b1);
                LOG("found %s at %zu, ", found_a ? "yes" : "no", index);
                LOG("vs found %s at %ld\n", found_b ? "yes" : "no", dist);
                print_vec(&a);
                print_vector(b);
                assert(found_a == found_b);
                assert((long)index == dist);
                break;
            }
            case TEST_BINARY_SEARCH: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                value = pick_random(&a);
                found_a = vec_int_binary_search(&a, value);
                found_b = binary_search(b.begin(), b.end(), value);
                LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_BINARY_SEARCH_RANGE: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                value = pick_random(&a);
                found_a = vec_int_binary_search_range(&range_a1, value);
                found_b = binary_search(first_b1, last_b1, value);
                LOG("%d: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            }
            case TEST_MERGE: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&aa);
                std::sort(bb.begin(), bb.end());

                aaa = vec_int_merge(&a, &aa);
#ifndef _MSC_VER
                merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                vec_int_free(&aa);
                vec_int_free(&aaa);
                break;
            }
            case TEST_MERGE_RANGE: {
                vec_int_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                gen_vectors(&aa, bb, TEST_RAND(a.size));
                vec_int_sort(&aa);
                std::sort(bb.begin(), bb.end());
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                aaa = vec_int_merge_range(&range_a1, &range_a2);
#ifndef _MSC_VER
                merge(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                CHECK(aaa, bbb);
#endif
                vec_int_free(&aa);
                vec_int_free(&aaa);
                break;
            }
#ifdef DEBUG
            case TEST_INPLACE_MERGE: {
                if (a.size < 3)
                    return 0;
                //vec_int_it r1_a = vec_int_begin(&a);
                vec_int_it r2_a = vec_int_begin(&a);
                vec_int_it_advance(&r2_a, a.size/2);
                //vec_int_it r3_a = vec_int_end(&a);
                std::vector<int>::iterator r1_b, r2_b, r3_b;
                r1_b = b.begin();
                r2_b = b.begin() + b.size() / 2;
                r3_b = b.end();
                print_vec (&a);
                //vec_int_inplace_merge(&r1_a, &r2_a, &r3_a);
                std::inplace_merge(&r1_b, &r2_b, &r3_b);
                LOG("inplace_merge:\n");
                print_vec (&a);
                print_vector (b);
                CHECK(a, b);
                break;
            }
#endif

            case TEST_IS_SORTED: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec(&a);
                found_a = vec_int_is_sorted(&range_a1);
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
                pos = vec_int_is_sorted_until(&range_a1, &range_a2);
                iter = std::is_sorted_until(first_b1, last_b1);
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            }
            case TEST_REVERSE: {
                print_vec(&a);
                vec_int_reverse(&a);
                reverse(b.begin(), b.end());
                CHECK(a, b);
                break;
            }
            case TEST_REVERSE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                print_vec_range(range_a1);
                vec_int_reverse_range(&range_a1);
                reverse(first_b1, last_b1);
                CHECK(a, b);
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
            vec_int_free(&a);
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
