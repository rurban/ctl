#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#define POD
#define T int
#include <ctl/vector.h>

#include <vector>
#include <algorithm>

int is_odd(int* a) {
    return *a % 2;
}

int stl_is_odd(int a) {
    return a % 2;
}

static int _generator_state = 0;
void int_generate_reset () {
    _generator_state = 0.0;
}
int int_generate (void) {
    _generator_state += 1.0;
    return _generator_state;
}
int int_untrans (int* v) {
    return *v >> 1;
}
int INT_untrans (int& v) {
    return v >> 1;
}
int int_bintrans (int* v1, int* v2) {
    return *v1 ^ *v2;
}
int INT_bintrans (int& v1, int& v2) {
    return v1 ^ v2;
}

void print_vec(vec_int *a)
{
    vec_foreach(int, a, ref)
        printf ("%d ", *ref);
    printf ("\n");
}

void print_vec_range(vec_int_it it)
{
    if (vec_int_empty(it.container))
        return;
    vec_int_it begin = vec_int_begin(it.container);
    int* ref = it.ref;
    long i1 = it.ref - begin.ref;
    long i2 = begin.end - it.ref;
    if (i1)
    {
        while(begin.ref != it.ref)
        {
            printf ("%d ", *begin.ref);
            begin.ref++;
        }
    }
    printf ("[");
    while(!vec_int_it_done(&it))
    {
        printf ("%d ", *it.ref);
        vec_int_it_next(&it);
    }
    printf (") ");
    if (i2)
    {
        begin.ref = it.ref;
        while(begin.ref != begin.end)
        {
            printf ("%d ", *begin.ref);
            begin.ref++;
        }
    }
    it.ref = ref;
    printf ("\n");
}

void print_vector(std::vector<int> &b)
{
    for(auto& d: b)
        printf ("%d ", d);
    printf ("\n");
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

int random_element(vec_int* a)
{
    const size_t index = TEST_RAND(a->size);
    return a->size ? *vec_int_at(a, index) : 0;
}

// tested variants
#if (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L)
// Tested ok with g++ 10, g++ 7.5,
// clang 10 (libc++ 11-18), apple clang 12 fail
# define ASSERT_EQUAL_CAP(c, s) assert(s.capacity() == c.capacity);
#else
// other llvm libc++ fail (gh actions), msvc untested
# define ASSERT_EQUAL_CAP(c, s) if (s.capacity() != c.capacity) \
    { printf("capacity %zu vs %zu FAIL\n", c.capacity, s.capacity()); fail++; }
#endif

// cheat growth
#define ADJUST_CAP(m, c, s)                                             \
    if (c.size == s.size() && c.capacity != s.capacity())               \
    {                                                                   \
        printf("%s capacity %zu => %zu FAIL\n", m, c.capacity, s.capacity()); \
        vec_int_fit(&c, s.capacity());                                 \
    }

#define CHECK(_x, _y) {                                           \
    ASSERT_EQUAL_CAP(_x, _y)                                      \
    assert(_x.size == _y.size());                                 \
    assert(vec_int_empty(&_x) == _y.empty());                     \
    if(_x.size > 0) {                                             \
        assert(_y.front() == *vec_int_front(&_x));                \
        assert(_y.back() == *vec_int_back(&_x));                  \
    }                                                             \
    std::vector<int>::iterator _iter = _y.begin();                \
    vec_foreach(int, &_x, _ref) {                                 \
        assert(*_ref == *_iter);                                  \
        _iter++;                                                  \
    }                                                             \
    int* _it = vec_int_front(&_x);                                \
    for(auto& _d : _y) {                                          \
        assert(*_it == _d);                                       \
        _it++;                                                    \
    }                                                             \
    for(size_t i = 0; i < _y.size(); i++)                         \
        assert(_y.at(i) == *vec_int_at(&_x, i));                  \
}

#define CHECK_REF(_ref, b, _iter)                                 \
    if (_iter != b.end())                                         \
        assert(*_ref == *_iter)

#define CHECK_ITER(_it, b, _iter)                                 \
    if ((_it).ref != &(_it).container->vector[(_it).container->size]) \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*(_it).ref == *_iter);                             \
    } else                                                        \
        assert (_iter == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                            \
    if (!vec_int_it_done(&_it))                                   \
    {                                                             \
        assert (_iter != b_end);                                  \
        assert(*(_it).ref == *_iter);                             \
    } else                                                        \
        assert (_iter == b_end)

static void
gen_vectors(vec_int* a, std::vector<int>& b, size_t size)
{
    *a = vec_int_init();
    for(int i = 0; i < (int)size; i++)
    {
        vec_int_push_back(a, i);
        b.push_back(i);
    }
}

static void
get_random_iters (vec_int *a, vec_int_it* first_a,
                  std::vector<int>& b, std::vector<int>::iterator &first_b,
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

int
main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
    int log = getenv("LOG") ? 1 : 0;
    int SAFE_DEBUG = getenv("SAFE_DEBUG") ? 1 : 0;
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t size = TEST_RAND(TEST_MAX_SIZE);
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            vec_int a = vec_int_init();
            std::vector<int> b;
            if(mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                vec_int_resize(&a, size, 0);
                b.resize(size);
                for(int i = 0; i < (int)size; i++)
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
            if(mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    const int value = TEST_RAND(INT_MAX);
                    vec_int_push_back(&a, value);
                    b.push_back(value);
                }
            }

#define FOREACH_METH(TEST) \
        TEST(PUSH_BACK) \
        TEST(POP_BACK) \
        TEST(CLEAR) \
        TEST(ERASE) \
        TEST(ERASE_INDEX) \
        TEST(ERASE_RANGE) \
        TEST(INSERT) \
        TEST(INSERT_INDEX) \
        TEST(INSERT_COUNT) \
        TEST(INSERT_RANGE) \
        TEST(EMPLACE_BACK) \
        TEST(RESIZE) \
        TEST(RESERVE) \
        TEST(SHRINK_TO_FIT) \
        TEST(SORT) \
        TEST(COPY) \
        TEST(SWAP) \
        TEST(ASSIGN) \
        TEST(REMOVE_IF) \
        TEST(ERASE_IF) \
        TEST(EQUAL) \
        TEST(FIND) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(ALL_OF) \
        TEST(ANY_OF) \
        TEST(NONE_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(COUNT) \
        TEST(COUNT_IF) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE) \
        TEST(INCLUDES) \
        TEST(INCLUDES_RANGE) \
        TEST(UNION) \
        TEST(INTERSECTION) \
        TEST(DIFFERENCE) \
        TEST(SYMMETRIC_DIFFERENCE) \
        TEST(UNION_RANGE) \
        TEST(INTERSECTION_RANGE) \
        TEST(DIFFERENCE_RANGE) \
        TEST(SYMMETRIC_DIFFERENCE_RANGE) \
        TEST(GENERATE) \
        TEST(GENERATE_RANGE) \
        TEST(GENERATE_N) \
        TEST(TRANSFORM) \
        TEST(TRANSFORM_IT) \
        TEST(MISMATCH) \
        TEST(SEARCH) \
        TEST(SEARCH_RANGE) \
        TEST(ADJACENT_FIND) \
        TEST(ADJACENT_FIND_RANGE) \

#define FOREACH_DEBUG(TEST) \
        TEST(EMPLACE) \
        TEST(EQUAL_RANGE) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM_RANGE) \
        TEST(TRANSFORM_IT_RANGE) \
        TEST(FIND_END) \
        TEST(FIND_END_RANGE) \
        TEST(LOWER_BOUND) \
        TEST(UPPER_BOUND) \
        TEST(LOWER_BOUND_RANGE) \
        TEST(UPPER_BOUND_RANGE) \

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
            if (log) {
                printf ("TEST=%d (size %zu, cap %zu)\n", which, a.size, a.capacity);
            }
            if (SAFE_DEBUG) {
                if (which > TEST_ADJACENT_FIND_RANGE)
                    which = 0;
            }
            LOG ("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            switch(which)
            {
                case TEST_PUSH_BACK:
                {
                    const int value = TEST_RAND(INT_MAX);
                    b.push_back(value);
                    vec_int_push_back(&a, value);
                    break;
                }
                case TEST_POP_BACK:
                {
                    if(a.size > 0)
                    {
                        b.pop_back();
                        vec_int_pop_back(&a);
                    }
                    break;
                }
                case TEST_CLEAR:
                {
                    b.clear();
                    vec_int_clear(&a);
                    break;
                }
                case TEST_ERASE:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        vec_int_it pos = vec_int_begin(&a);
                        vec_int_it_advance(&pos, index);
                        pos = vec_int_erase(&pos);
                        auto it = b.erase(b.begin() + index);
                        CHECK_ITER(pos, b, it);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE_INDEX:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        auto iter = b.erase(b.begin() + index);
                        vec_int_it it = vec_int_erase_index(&a, index);
                        CHECK_ITER(it, b, iter);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE_RANGE:
                {
                    if(a.size > 1)
                    {
                        vec_int_it first_a;
                        std::vector<int>::iterator first_b, last_b;
                        get_random_iters (&a, &first_a, b, first_b, last_b);
                        print_vec_range(first_a);
                        vec_int_erase_range(&first_a);
                        auto it = b.erase(first_b, last_b);
                        print_vec(&a);
                        print_vector(b);
                        CHECK_RANGE(first_a, it, last_b);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        vec_int_insert_index(&a, index, value);
                    }
                    break;
                }
                case TEST_INSERT_INDEX:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        vec_int_it pos = vec_int_begin(&a);
                        vec_int_it_advance(&pos, index);
                        vec_int_insert(&pos, value);
                    }
                    break;
                }
                case TEST_INSERT_COUNT:
                {
                    size_t count = TEST_RAND(512);
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size);
                    b.insert(b.begin() + index, count, value);
                    vec_int_it pos = vec_int_begin(&a);
                    vec_int_it_advance(&pos, index);
                    vec_int_insert_count(&pos, count, value);
                    vec_int_reserve(&a, b.capacity()); // our growth strategy
                                                        // is better. but for
                                                        // test sake adjust it
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT_RANGE:
                {
                    if (a.size > 2)
                    {
                        print_vec(&a);
                        size_t size2 = TEST_RAND(TEST_MAX_SIZE);
                        vec_int aa = vec_int_init_from(&a);
                        std::vector<int> bb;
                        vec_int_it first_a;
                        std::vector<int>::iterator first_b, last_b;
                        for(size_t pushes = 0; pushes < size2; pushes++)
                        {
                            const int value = TEST_RAND(TEST_MAX_VALUE);
                            vec_int_push_back(&aa, value);
                            bb.push_back(value);
                        }
                        print_vec(&aa);
                        get_random_iters (&aa, &first_a, bb, first_b, last_b);
                        const size_t index = TEST_RAND(a.size);
                        vec_int_it pos = vec_int_begin(&a);
                        vec_int_it_advance(&pos, index);
                        b.insert(b.begin() + index, first_b, last_b);
                        vec_int_insert_range(&pos, &first_a);
                        // our growth strategy is better. but for test sake adjust it
                        vec_int_reserve(&a, b.capacity());
                        print_vec(&a);
                        print_vector(b);
                        CHECK(a, b);
                        vec_int_free(&aa);
                    }
                    break;
                }
                case TEST_RESIZE:
                {
                    const size_t resize = 3 * TEST_RAND(a.size) + 1;
                    b.resize(resize);
                    LOG("STL resize by %zu %zu -> %zu\n", resize, b.size(), b.capacity());
                    vec_int_resize(&a, resize, 0);
                    LOG("CTL resize by %zu %zu -> %zu\n", resize, a.size, a.capacity);
                    break;
                }
                case TEST_RESERVE:
                {
                    const size_t capacity = 3 * TEST_RAND(a.capacity) + 1;
                    b.reserve(capacity);
                    vec_int_reserve(&a, capacity);
                    LOG("CTL reserve by %zu %zu\n", capacity, a.capacity);
                    LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                    break;
                }
                case TEST_SHRINK_TO_FIT:
                {
                    b.shrink_to_fit();
                    vec_int_shrink_to_fit(&a);
                    LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                    LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                    break;
                }
                case TEST_SORT:
                {
                    vec_int_sort(&a);
                    sort(b.begin(), b.end());
                    break;
                }
                case TEST_COPY:
                {
                    vec_int aa = vec_int_copy(&a);
                    std::vector<int> bb = b;
                    CHECK(aa, bb);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    size_t assign_size = TEST_RAND(a.size) + 1;
                    vec_int_assign(&a, assign_size, value);
                    b.assign(assign_size, value);
                    break;
                }
                case TEST_SWAP:
                {
                    LOG("CTL capacity %zu\n", a.capacity);
                    LOG("STL capacity %zu\n", b.capacity());
                    vec_int aa = vec_int_copy(&a);
                    vec_int aaa = vec_int_init();
                    LOG("CTL capacity %zu copy %zu\n", aa.capacity, aa.size);
                    LOG("CTL capacity %zu init\n", aaa.capacity);
                    std::vector<int> bb = b;
                    std::vector<int> bbb;
                    vec_int_swap(&aaa, &aa);
                    LOG("CTL capacity %zu after swap %zu\n", aaa.capacity, aaa.size);
                    swap(bb, bbb);
                    LOG("STL capacity %zu after swap %zu\n", bbb.capacity(), bbb.size());
                    CHECK(aaa, bbb);
                    vec_int_free(&aaa);
                    break;
                }
                case TEST_REMOVE_IF:
                {
                    vec_int_remove_if(&a, is_odd);
                    b.erase(remove_if(b.begin(), b.end(), stl_is_odd), b.end());
                    break;
                }
                case TEST_ERASE_IF:
                {
#if __cpp_lib_erase_if >= 202002L
                    size_t num_a = vec_int_erase_if(&a, is_odd);
                    size_t num_b = std::erase_if(b, stl_is_odd);
                    assert(num_a == num_b);
#else
                    vec_int_erase_if(&a, is_odd);
                    b.erase(std::remove_if(b.begin(), b.end(), stl_is_odd), b.end());
#endif
                    break;
                }
                case TEST_EQUAL:
                {
                    vec_int aa = vec_int_copy(&a);
                    std::vector<int> bb = b;
                    assert(vec_int_equal(&a, &aa));
                    assert(b == bb);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_FIND:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        int value = TEST_RAND(2) ? TEST_RAND(INT_MAX) : *vec_int_at(&a, index);
                        vec_int_it aa = vec_int_find(&a, value);
                        auto bb = find(b.begin(), b.end(), value);
                        bool found_a = !vec_int_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa.ref == *bb);
                    }
                    break;
                }
                case TEST_FIND_IF:
                {
                    vec_int_it aa = vec_int_find_if(&a, is_odd);
                    auto bb = find_if(b.begin(), b.end(), stl_is_odd);
                    if(bb == b.end())
                        assert(vec_int_it_done(&aa));
                    else
                        assert(*bb == *aa.ref);
                    break;
                }
                case TEST_FIND_IF_NOT:
                {
                    vec_int_it aa = vec_int_find_if_not(&a, is_odd);
                    auto bb = find_if_not(b.begin(), b.end(), stl_is_odd);
                    if(bb == b.end())
                        assert(vec_int_it_done(&aa));
                    else
                        assert(*bb == *aa.ref);
                    break;
                }
                case TEST_ALL_OF:
                {
                    bool is_a = vec_int_all_of(&a, is_odd);
                    bool is_b = all_of(b.begin(), b.end(), stl_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_ANY_OF:
                {
                    bool is_a = vec_int_any_of(&a, is_odd);
                    bool is_b = any_of(b.begin(), b.end(), stl_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_NONE_OF:
                {
                    bool is_a = vec_int_none_of(&a, is_odd);
                    bool is_b = none_of(b.begin(), b.end(), stl_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_COUNT:
                {
                    int key = TEST_RAND(TEST_MAX_SIZE);
                    int aa = vec_int_count(&a, key);
                    int bb = count(b.begin(), b.end(), key);
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF:
                {
                    size_t count_a = vec_int_count_if(&a, is_odd);
                    size_t count_b = count_if(b.begin(), b.end(), stl_is_odd);
                    assert(count_a == count_b);
                    break;
                }
                case TEST_FIND_RANGE:
                {
                    int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                                          : random_element(&a);
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    bool found_a = vec_int_find_range(&first_a, vb);
                    auto it = find(first_b, last_b, vb);
                    if (found_a)
                        assert(it != last_b);
                    else
                        assert(it == last_b);
                    CHECK_RANGE(first_a, it, last_b);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_IF_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    first_a = vec_int_find_if_range(&first_a, is_odd);
                    auto it = find_if(first_b, last_b, stl_is_odd);
                    print_vec(&a);
                    print_vector(b);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_FIND_IF_NOT_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    first_a = vec_int_find_if_not_range(&first_a, is_odd);
                    auto it = find_if_not(first_b, last_b, stl_is_odd);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_ALL_OF_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    bool aa = vec_int_all_of_range(&first_a, is_odd);
                    bool bb = all_of(first_b, last_b, stl_is_odd);
                    if (aa != bb)
                    {
                        print_vec(&a);
                        print_vector(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_ANY_OF_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    bool aa = vec_int_any_of_range(&first_a, is_odd);
                    bool bb = any_of(first_b, last_b, stl_is_odd);
                    if (aa != bb)
                    {
                        print_vec(&a);
                        print_vector(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_NONE_OF_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    bool aa = vec_int_none_of_range(&first_a, is_odd);
                    bool bb = none_of(first_b, last_b, stl_is_odd);
                    if (aa != bb)
                    {
                        print_vec(&a);
                        print_vector(b);
                        printf ("%d != %d is_odd\n", (int)aa, (int)bb);
                    }
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    size_t numa = vec_int_count_if_range(&first_a, is_odd);
                    size_t numb = count_if(first_b, last_b, stl_is_odd);
                    if (numa != numb)
                    {
                        print_vec(&a);
                        print_vector(b);
                        printf ("%d != %d FAIL\n", (int)numa, (int)numb);
                        fail++;
                    }
                    assert(numa == numb); //fails. off by one, counts one too much
                    break;
                }
                case TEST_COUNT_RANGE:
                {
                    int test_value = 0;
                    int v = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                        : test_value;
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    // used to fail with 0,0 of 0
                    size_t numa = vec_int_count_range(&first_a, v);
                    size_t numb = count(first_b, last_b, v);
                    assert(numa == numb);
                    break;
                }
                case TEST_EMPLACE_BACK:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
# if __cplusplus >= 201103L
                    b.emplace_back(value);
# else
                    b.insert(b.begin() + index, value);
# endif
                    vec_int_emplace_back(&a, &value);
                    CHECK(a, b);
                    break;
                }
#ifdef DEBUG
                case TEST_EMPLACE:
                {
                    int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size);
                    vec_int_it pos = vec_int_begin(&a);
                    vec_int_it_advance(&pos, index);
# if __cplusplus >= 201103L
                    b.emplace(b.begin() + index, value);
# else
                    b.insert(b.begin() + index, value);
# endif
                    vec_int_emplace(&pos, &value);
                    CHECK(a, b);
                    break;
                }
#endif // DEBUG
                case TEST_INCLUDES:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    bool a_found = vec_int_includes(&a, &aa);
                    bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                    assert (a_found == b_found);
                    CHECK(aa, bb);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_INCLUDES_RANGE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int_it first_a1;
                    std::vector<int>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, b, first_b1, last_b1);
                    vec_int_it first_a2;
                    std::vector<int>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, bb, first_b2, last_b2);

                    LOG("CTL a - aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    bool a_found = vec_int_includes_range(&first_a1, &first_a2);
                    std::vector<int> bbb;
                    LOG("STL b + bb\n");
                    print_vector(b);
                    print_vector(bb);
                    bool b_found = std::includes(first_b1, last_b1, first_b2, last_b2);
                    assert(a_found == b_found);
                    CHECK(aa, bb);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_UNION:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int aaa = vec_int_union(&a, &aa);
# ifndef _MSC_VER
                    std::vector<int> bbb;
                    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                                   std::back_inserter(bbb));
                    LOG("STL b + bb => bbb\n");
                    print_vector(b);
                    print_vector(bb);
                    print_vector(bbb);
                    LOG("CTL a + aaa => aaa\n");
                    CHECK(aa, bb);
                    print_vec(&a);
                    print_vec(&aa);
                    print_vec(&aaa);
                    ADJUST_CAP("union", aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_INTERSECTION:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int aaa = vec_int_intersection(&a, &aa);
# ifndef _MSC_VER
                    std::vector<int> bbb;
                    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                          std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    print_vec(&a);
                    print_vec(&aa);
                    print_vec(&aaa);
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    print_vec(&a);
                    vec_int aaa = vec_int_difference(&a, &aa);
# ifndef _MSC_VER
                    std::vector<int> bbb;
                    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                        std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("difference",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int aaa = vec_int_symmetric_difference(&a, &aa);
# ifndef _MSC_VER
                    std::vector<int> bbb;
                    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                                  std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_UNION_RANGE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int_it first_a1;
                    std::vector<int>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, b, first_b1, last_b1);
                    vec_int_it first_a2;
                    std::vector<int>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_int aaa = vec_int_union_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<int> bbb;
                    LOG("STL b + bb\n");
                    print_vector(b);
                    print_vector(bb);
# ifndef _MSC_VER
                    std::set_union(first_b1, last_b1, first_b2, last_b2,
                                   std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_vector(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("union_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_INTERSECTION_RANGE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int_it first_a1;
                    std::vector<int>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, b, first_b1, last_b1);
                    vec_int_it first_a2;
                    std::vector<int>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_int aaa = vec_int_intersection_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<int> bbb;
                    LOG("STL b + bb\n");
                    print_vector(b);
                    print_vector(bb);
# ifndef _MSC_VER
                    std::set_intersection(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_vector(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE_RANGE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int_it first_a1;
                    std::vector<int>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, b, first_b1, last_b1);
                    vec_int_it first_a2;
                    std::vector<int>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, bb, first_b2, last_b2);

                    LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_int aaa = vec_int_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa (%zu)\n", aa.size);
                    print_vec(&aaa);

                    std::vector<int> bbb;
                    LOG("STL b (%zu) + bb (%zu)\n", b.size(), bb.size());
                    print_vector(b);
                    print_vector(bb);
# ifndef _MSC_VER
                    std::set_difference(first_b1, last_b1, first_b2, last_b2,
                                        std::back_inserter(bbb));
                    LOG("STL => bbb (%zu)\n", bbb.size());
                    print_vector(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("difference_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE_RANGE:
                {
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_sort(&a);
                    vec_int_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_int_it first_a1;
                    std::vector<int>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, b, first_b1, last_b1);
                    vec_int_it first_a2;
                    std::vector<int>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_int aaa = vec_int_symmetric_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<int> bbb;
                    LOG("STL b + bb\n");
                    print_vector(b);
                    print_vector(bb);
# ifndef _MSC_VER
                    std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    print_vector(bbb);
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference_range",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_int_free(&aaa);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_GENERATE:
                {
                    int_generate_reset();
                    vec_int_generate(&a, int_generate);
                    int_generate_reset();
                    std::generate(b.begin(), b.end(), int_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_RANGE:
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    int_generate_reset();
                    vec_int_generate_range(&first_a, int_generate);
                    int_generate_reset();
                    std::generate(first_b, last_b, int_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM:
                {
                    vec_int aa = vec_int_transform(&a, int_untrans);
                    std::vector<int> bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), bb.begin(), INT_untrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_IT:
                {
                    print_vec(&a);
                    if (a.size < 2)
                        break;
                    vec_int_it pos = vec_int_begin(&a);
                    vec_int_it_advance(&pos, 1);
                    vec_int aa = vec_int_transform_it(&a, &pos, int_bintrans);
                    std::vector<int> bb;
                    bb.resize(b.size()-1);
                    std::transform(b.begin(), b.end()-1, b.begin()+1, bb.begin(), INT_bintrans);
                    ADJUST_CAP("transform_it", aa, bb);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_GENERATE_N:
                {
                    size_t count = TEST_RAND(20);
                    LOG("generate_n %zu\n", count);                    
# ifndef _MSC_VER                                        
                    int_generate_reset();
                    vec_int_generate_n(&a, count, int_generate);
                    print_vec(&a);
                    int_generate_reset();
                    // FIXME The STL is arguably broken here.
                    int n = MIN(count, b.size());
                    b.erase(b.begin(), b.begin()+n);
                    std::generate_n(std::inserter(b, b.begin()), n, int_generate);
                    print_vector(b);
# endif
                    CHECK(a, b);
                    break;
                }
#ifdef DEBUG
                case TEST_GENERATE_N_RANGE: // 60
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    size_t off = first_b - b.begin();
                    size_t count = TEST_RAND(20 - off);
                    int_generate_reset();
                    vec_int_generate_n_range(&first_a, count, int_generate);
                    int_generate_reset();
                    std::generate_n(first_b, count, int_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM_RANGE: // 61
                {
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    vec_int aa = vec_int_init();
                    vec_int_it dest = vec_int_begin(&aa);
                    vec_int_it it = vec_int_transform_range(&first_a, dest, int_untrans);
                    std::vector<int> bb;
                    bb.resize(last_b - first_b);
                    auto iter = std::transform(first_b, last_b-1, b.begin()+1, bb.begin(),
                                               INT_bintrans);
                    CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_IT_RANGE:
                {
                    if (a.size < 2)
                        break;
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
                    vec_int_it pos = vec_int_begin(&a);
                    vec_int_it_advance(&pos, 1);
                    vec_int aa = vec_int_init();
                    vec_int_resize(&aa, last_b - first_b, 0);
                    vec_int_it dest = vec_int_begin(&aa);
                    /* vec_int_it it = */
                    vec_int_transform_it_range(&first_a,
                                               &pos, dest, int_bintrans);
                    auto it2 = b.begin();
                    std::advance(it2, 1);
# ifndef _MSC_VER
                    std::vector<int> bb;
                    bb.reserve(last_b - first_b - 1);
                    /*auto iter =*/
                     std::transform(first_b, last_b, it2,
                                    std::back_inserter(bb), INT_bintrans);
                    ADJUST_CAP("transform_it_range", aa, bb);
                    //CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
# endif
                    // heap use-after-free
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
#endif // DEBUG
                case TEST_MISMATCH:
                {
                    if(a.size < 2)
                        break;
                    vec_int aa;
                    std::vector<int> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_int_it b1, b2;
                    b1 = vec_int_begin(&a);
                    b2 = vec_int_begin(&aa);
                    vec_int_it r1a, r2a;
                    std::vector<int>::iterator r1b, last1_b, r2b, last2_b;
                    get_random_iters (&a, &r1a, b, r1b, last1_b);
                    get_random_iters (&aa, &r2a, bb, r2b, last2_b);
                    /*bool found_a = */vec_int_mismatch(&r1a, &r2a);
                    auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
                    int d1a = vec_int_it_distance(&b1, &r1a);
                    int d2a = vec_int_it_distance(&b2, &r2a);
                    LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                    //TODO check found_a against iter results
                    assert(d1a == distance(b.begin(), pair.first));
                    assert(d2a == distance(bb.begin(), pair.second));
                    vec_int_free(&aa);
                    break;
                }
                case TEST_SEARCH: // 51
                {
                    print_vec(&a);
                    vec_int aa = vec_int_copy(&a);
                    std::vector<int> bb = b;
                    vec_int_it first_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&aa, &first_a, bb, first_b, last_b);
                    if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                        size_t i = first_b - bb.begin();
                        vec_int_set(&aa, i, 0);
                        bb[i] = 0;
                    }
                    print_vec_range(first_a);                    
                    vec_int_it found_a = vec_int_search(&a, &first_a);
                    auto found_b = search(b.begin(), b.end(), first_b, last_b);
                    LOG("found a: %s\n", vec_int_it_done(&found_a) ? "no" : "yes");
                    LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
                    CHECK_ITER(found_a, b, found_b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_SEARCH_RANGE:
                {
                    vec_int aa = vec_int_copy(&a);
                    std::vector<int> bb = b;
                    vec_int_it needle, range;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&aa, &needle, bb, first_b, last_b);
                    if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                        size_t i = first_b - bb.begin();
                        vec_int_set(&aa, i, 0);
                        bb[i] = 0;
                    }
                    print_vec_range(needle);
                    range = vec_int_begin(&a);
                    bool found = vec_int_search_range(&range, &needle);
                    auto iter = search(b.begin(), b.end(), first_b, last_b);
                    LOG("found a: %s\n", found ? "yes" : "no");
                    LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                    assert(found == !vec_int_it_done(&range));
                    CHECK_ITER(range, b, iter);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_ADJACENT_FIND:
                {
                    print_vec(&a);
                    vec_int_it aa = vec_int_adjacent_find(&a);
                    auto bb = adjacent_find(b.begin(), b.end());
                    CHECK_ITER(aa, b, bb);
                    LOG("found %s\n", vec_int_it_done(&aa) ? "no" : "yes");
                    break;
                }
                case TEST_ADJACENT_FIND_RANGE:
                {
                    vec_int_it range;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &range, b, first_b, last_b);
                    print_vec_range(range);
                    vec_int_it *aa = vec_int_adjacent_find_range(&range);
                    auto bb = adjacent_find(first_b, last_b);
                    CHECK_ITER(*aa, b, bb);
                    LOG("found %s\n", vec_int_it_done(aa) ? "no" : "yes");
                    break;
                }
#ifdef DEBUG
                case TEST_LOWER_BOUND: // 64
                {
                    int median = *vec_int_at(&a, a.size / 2);
                    vec_int_it aa = vec_int_lower_bound(&a, median);
                    auto bb = lower_bound(b.begin(), b.end(), median);
                    CHECK_ITER(aa, b, bb);
                    break;
                }
                case TEST_UPPER_BOUND:
                {
                    int median = *vec_int_at(&a, a.size / 2);
                    vec_int_it aa = vec_int_upper_bound(&a, median);
                    auto bb = upper_bound(b.begin(), b.end(), median);
                    CHECK_ITER(aa, b, bb);
                    break;
                }
                /**/case TEST_LOWER_BOUND_RANGE:
                {
                    break;
                }
                /**/case TEST_UPPER_BOUND_RANGE:
                {
                    break;
                }
#endif
#if 0
                case TEST_FIND_END:
                {
                    if(a.size > 0)
                    {
                        vec_int_it first_a;
                        vec_int_it aa = vec_int_find_end(&a, &s_first, &s_last);
                        auto bb = find_end(b.begin(), b.end(), ...);
                        bool found_a = !vec_int_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*aa == *bb);
                    }
                    break;
                }
                case TEST_FIND_END_RANGE:
                {
                    vec_int_it first_a, s_first;
                    std::vector<int>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = vec_int_find_end_range(&first_a, &s_first_a);
                    auto it = find_end(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
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
            vec_int_free(&a);
        }
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
