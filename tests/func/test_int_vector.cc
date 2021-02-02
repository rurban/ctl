#include "../test.h"
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
    return  _generator_state;
}
int int_untrans (int* v) {
    return 2.0 * *v;
}
int INT_untrans (int& v) {
    return 2.0 * v;
}
int int_bintrans (int* v1, int* v2) {
    return *v1 * *v2;
}
int INT_bintrans (int& v1, int& v2) {
    return v1 * v2;
}

void print_vec(vec_int *a)
{
    vec_foreach(int, a, ref)
        printf ("%d ", *ref);
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
#define print_vector(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(vec_int* a)
{
    const size_t index = TEST_RAND(a->size);
    return *vec_int_at(a, index);
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

#ifdef DEBUG
#define CHECK_ITER(_it, b, _iter)                                 \
    if (!vec_int_it_done(&_it))                                   \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*_it.ref == *_iter);                               \
    } else                                                        \
        assert (_iter == b.end())

static void
get_random_iters (vec_int *a, vec_int_it* first_a, vec_int_it* last_a,
                  std::vector<int>& b, std::vector<int>::iterator &first_b,
                  std::vector<int>::iterator &last_b)
{
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
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            *last_a = vec_int_end(a);
            last_b = b.end();
        }
        else
        {
            vec_int_it it2 = vec_int_begin(a);
            last_b = b.begin();
            vec_int_it_advance(&it2, r2);
            last_b += r2;
            *last_a = it2;
        }
    }
    else
    {
        vec_int_it end = vec_int_end(a);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
}
#endif

int
main(void)
{
    int fail = 0;
    INIT_SRAND;
    INIT_TEST_LOOPS(10);
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
                LOG("mode DIRECT\n");
                vec_int_resize(&a, size, 0);
                b.resize(size);
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
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
        TEST(RESIZE) \
        TEST(RESERVE) \
        TEST(SHRINK_TO_FIT) \
        TEST(SORT) \
        TEST(COPY) \
        TEST(SWAP) \
        TEST(INSERT) \
        TEST(ASSIGN) \
        TEST(REMOVE_IF) \
        TEST(EQUAL) \
        TEST(FIND) \
        TEST(ALL_OF) \
        TEST(FIND_IF) \
        TEST(FIND_IF_NOT) \
        TEST(NONE_OF) \
        TEST(COUNT) \
        TEST(COUNT_IF) \

#define FOREACH_DEBUG(TEST) \
        TEST(INSERT_COUNT) \
        TEST(INSERT_RANGE) \
        TEST(EQUAL_RANGE) \
        TEST(FIND_RANGE) \
        TEST(FIND_IF_RANGE) \
        TEST(FIND_IF_NOT_RANGE) \
        TEST(ANY_OF) \
        TEST(ALL_OF_RANGE) \
        TEST(ANY_OF_RANGE) \
        TEST(NONE_OF_RANGE) \
        TEST(COUNT_IF_RANGE) \
        TEST(COUNT_RANGE) \
        TEST(DIFFERENCE) \
        TEST(INTERSECTION) \
        TEST(GENERATE_N) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM) \
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
            //if (which > TEST_COUNT_IF)
            //    which = 0;
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
                case TEST_ERASE_INDEX:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        auto it = b.erase(b.begin() + index);
                        int* pos = vec_int_erase_index(&a, index);
                        CHECK_REF(pos, b, it);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        vec_int_it pos = vec_int_begin(&a);
                        vec_int_it_advance(&pos, index);
                        int* i = vec_int_erase(&a, pos.ref);
                        auto it = b.erase(b.begin() + index);
                        CHECK_REF(i, b, it);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_INSERT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(INT_MAX);
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        vec_int_insert(&a, index, value);
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
                    const int value = TEST_RAND(INT_MAX);
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
#ifdef DEBUG    // wrong range end condition. ref == last is already too late.
                case TEST_FIND_RANGE:
                {
                    int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                        : random_element(&a);
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_int_find_range(&first_a, &last_a, vb);
                    auto it = find(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_IF_RANGE:
                {
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_int_find_if_range(&first_a, &last_a, is_odd);
                    auto it = find_if(first_b, last_b, stl_is_odd);
                    print_vec(&a);
                    print_vector(b);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_FIND_IF_NOT_RANGE:
                {
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_int_find_if_not_range(&first_a, &last_a, is_odd);
                    auto it = find_if_not(first_b, last_b, stl_is_odd);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_ALL_OF_RANGE:
                {
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_int_all_of_range(&first_a, &last_a, is_odd);
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
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_int_any_of_range(&first_a, &last_a, is_odd);
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
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_int_none_of_range(&first_a, &last_a, is_odd);
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
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t numa = vec_int_count_if_range(&first_a, &last_a, is_odd);
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
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    // used to fail with 0,0 of 0
                    size_t numa = vec_int_count_range(&first_a, &last_a, v);
                    size_t numb = count(first_b, last_b, v);
                    assert(numa == numb);
                    break;
                }
                case TEST_ANY_OF: // broken
                {
                    bool is_a = vec_int_all_of(&a, is_odd);
                    bool is_b = any_of(b.begin(), b.end(), stl_is_odd);
                    if (is_a != is_b)
                    {
                        //print_vec(&a);
                        //print_vector(b);
                        printf ("%d != %d FAIL\n", (int)is_a, (int)is_b);
                        fail++;
                    }
                    //assert(is_a == is_b);
                    break;
                }
#endif
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
#ifdef DEBUG
                case TEST_INSERT_COUNT:
                case TEST_INSERT_RANGE:
                case TEST_EQUAL_RANGE:
                case TEST_DIFFERENCE:
                case TEST_INTERSECTION:
                    printf("nyi\n");
                    break;
                case TEST_GENERATE_N:
                {
                    size_t count = TEST_RAND(20);
                    int_generate_reset();
                    vec_int_generate_n(&a, count, int_generate);
                    int_generate_reset();
                    std::generate_n(b.begin(), count, int_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_N_RANGE:
                {
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t off = first_b - b.begin();
                    size_t count = TEST_RAND(20 - off);
                    int_generate_reset();
                    vec_int_generate_n_range(&first_a, count, int_generate);
                    int_generate_reset();
                    std::generate_n(first_b, count, int_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM:
                {
                    vec_int aa = vec_int_transform(&a, int_untrans);
                    std::vector<int> bb;
                    std::transform(b.begin(), b.end(), bb.begin(), INT_untrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_IT:
                {
                    vec_int_it pos = vec_int_begin(&a);
                    vec_int_it_advance(&pos, 1);
                    vec_int aa = vec_int_transform_it(&a, &pos, int_bintrans);
                    std::vector<int> bb;
                    std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), INT_bintrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_RANGE:
                {
                    vec_int_it first_a, last_a;
                    std::vector<int>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    vec_int aa = vec_int_init();
                    vec_int_it dest = vec_int_begin(&aa);
                    vec_int_it it = vec_int_transform_range(&first_a, &last_a, dest, int_untrans);
                    std::vector<int> bb;
                    auto iter = std::transform(b.begin(), b.end(), b.begin()+1, bb.begin(), INT_bintrans);
                    CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_int_free(&aa);
                    break;
                }
#endif
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
