#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include "digi.hh"

#define T digi
#include <ctl/vector.h>

#include <vector>
#include <algorithm>

void print_vec(vec_digi *a)
{
    vec_foreach(digi, a, ref)
        printf ("%d ", *ref->value);
    printf ("\n");
}

void print_vec_range(vec_digi_it it)
{
    if (vec_digi_empty(it.container))
        return;
    vec_digi_it begin = vec_digi_begin(it.container);
    digi* ref = it.ref;
    long i1 = it.ref - begin.ref;
    long i2 = begin.end - it.ref;
    if (i1)
    {
        while(begin.ref != it.ref)
        {
            printf ("%d ", *begin.ref->value);
            begin.ref++;
        }
    }
    printf ("[");
    while(!vec_digi_it_done(&it))
    {
        printf ("%d ", *it.ref->value);
        vec_digi_it_next(&it);
    }
    printf (") ");
    if (i2)
    {
        begin.ref = it.ref;
        while(begin.ref != begin.end)
        {
            printf ("%d ", *begin.ref->value);
            begin.ref++;
        }
    }
    it.ref = ref;
    printf ("\n");
}

void print_vector(std::vector<DIGI> &b)
{
    for(auto& d: b)
        printf ("%d ", *d.value);
    printf ("\n");
}

#ifdef DEBUG
#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 15
//#define TEST_MAX_VALUE INT_MAX
#define TEST_MAX_VALUE 100
#else
#define print_vec(x)
#define print_vector(x)
#define print_vec_range(x)
#define TEST_MAX_VALUE INT_MAX
#endif

int random_element(vec_digi* a)
{
    const size_t index = TEST_RAND(a->size);
    if (!a->size)
        return 0;
    digi *vp = vec_digi_at(a, index);
    return *vp->value;
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
        vec_digi_fit(&c, s.capacity());                                 \
    }


#define CHECK(_x, _y) {                                           \
    ASSERT_EQUAL_CAP(_x, _y)                                      \
    assert(_x.size == _y.size());                                 \
    assert(vec_digi_empty(&_x) == _y.empty());                    \
    if(_x.size > 0) {                                             \
        assert(*_y.front().value == *vec_digi_front(&_x)->value); \
        assert(*_y.back().value == *vec_digi_back(&_x)->value);   \
    }                                                             \
    std::vector<DIGI>::iterator _iter = _y.begin();               \
    vec_foreach(digi, &_x, _ref) {                                \
        assert(*(_ref->value) == *_iter->value);                  \
        _iter++;                                                  \
    }                                                             \
    digi* _ref = vec_digi_front(&_x);                             \
    for(auto& _d : _y) {                                          \
        assert(*(_ref->value) == *_d.value);                      \
        _ref++;                                                   \
    }                                                             \
    for(size_t i = 0; i < _y.size(); i++)                         \
        assert(*_y.at(i).value == *vec_digi_at(&_x, i)->value);   \
}

#define CHECK_ITER(_it, b, _iter)                                 \
    if ((_it).ref != &(_it).container->vector[(_it).container->size]) \
    {                                                             \
        assert (_iter != b.end());                                \
        assert(*((_it).ref->value) == *(*_iter).value);           \
    } else                                                        \
        assert (_iter == b.end())

#define CHECK_REF(_ref, b, _iter)                                 \
    if (_iter != b.end())                                         \
        assert(*(_ref->value) == *(*_iter).value)

static void
gen_vectors(vec_digi* a, std::vector<DIGI>& b, size_t size)
{
    *a = vec_digi_init();
    a->compare = digi_compare;
    a->equal = digi_equal;
    for(int i = 0; i < (int)size; i++)
    {
        vec_digi_push_back(a, digi_init(i));
        b.push_back(DIGI{i});
    }
}

static void
get_random_iters (vec_digi *a, vec_digi_it* first_a, vec_digi_it* last_a,
                  std::vector<DIGI>& b, std::vector<DIGI>::iterator &first_b,
                  std::vector<DIGI>::iterator &last_b)
{
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        vec_digi_it it1 = vec_digi_begin(a);
        first_b = b.begin();
        vec_digi_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            *last_a = vec_digi_end(a);
            last_b = b.end();
        }
        else
        {
            vec_digi_it it2 = vec_digi_begin(a);
            last_b = b.begin();
            vec_digi_it_advance(&it2, r2);
            last_b += r2;
            *last_a = it2;
        }
    }
    else
    {
        vec_digi_it end = vec_digi_end(a);
        *first_a = end;
        *last_a = end;
        first_b = b.begin();
        last_b = b.end();
    }
    first_a->end = last_a->ref;
}

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
            vec_digi a = vec_digi_init();
            a.compare = digi_compare;
            a.equal = digi_equal;
            std::vector<DIGI> b;
            if(mode == MODE_DIRECT)
            {
                LOG("mode direct\n");
                vec_digi_resize(&a, size, digi_init(0));
                b.resize(size);
                for(int i = 0; i < (int)size; i++)
                {
#ifdef DEBUG
                    const int vb = i;
#else
                    const int vb = TEST_RAND(TEST_MAX_VALUE);
#endif
                    vec_digi_set(&a, i, digi_init(vb));
                    b[i] = DIGI{vb};
                }
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode growth\n");
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    vec_digi_push_back(&a, digi_init(value));
                    b.push_back(DIGI{value});
                }
            }

#define FOREACH_METH(TEST) \
        TEST(PUSH_BACK) \
        TEST(POP_BACK) \
        TEST(CLEAR) \
        TEST(ERASE) \
        TEST(ERASE_INDEX) \
        TEST(INSERT) \
        TEST(INSERT_INDEX) \
        TEST(INSERT_COUNT) \
        TEST(INSERT_RANGE) \
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
        TEST(EMPLACE_BACK) \
        TEST(MISMATCH) \
        TEST(SEARCH) \
        TEST(SEARCH_RANGE) \
        TEST(ADJACENT_FIND) \
        TEST(ADJACENT_FIND_RANGE) \

#define FOREACH_DEBUG(TEST) \
        TEST(EMPLACE) /* 56 */ \
        TEST(ERASE_RANGE) \
        TEST(EQUAL_RANGE) \
        TEST(GENERATE_N_RANGE) \
        TEST(TRANSFORM_RANGE) \
        TEST(TRANSFORM_IT_RANGE) \
        TEST(FIND_END) \
        TEST(FIND_END_IF) \
        TEST(FIND_END_RANGE) \
        TEST(FIND_END_IF_RANGE) \
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
            //if (which > TEST_INSERT_COUNT)
            //    which = 0;
            LOG ("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            switch(which)
            {
                case TEST_PUSH_BACK:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    b.push_back(DIGI{value});
                    vec_digi_push_back(&a, digi_init(value));
                    break;
                }
                case TEST_POP_BACK:
                {
                    if(a.size > 0)
                    {
                        b.pop_back();
                        vec_digi_pop_back(&a);
                    }
                    break;
                }
                case TEST_CLEAR:
                {
                    b.clear();
                    vec_digi_clear(&a);
                    break;
                }
                case TEST_ERASE:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        vec_digi_it pos = vec_digi_begin(&a);
                        vec_digi_it_advance(&pos, index);
                        pos = vec_digi_erase(&pos);
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
                        vec_digi_it it = vec_digi_erase_index(&a, index);
                        CHECK_ITER(it, b, iter);
                    }
                    CHECK(a, b);
                    break;
                }
#ifdef DEBUG
                case TEST_ERASE_RANGE: // 40
                {
                    if(a.size > 1)
                    {
                        const size_t i1 = TEST_RAND(a.size);
                        const size_t i2 = i1 + TEST_RAND(a.size - i1);
                        vec_digi_it from = vec_digi_begin(&a);
                        vec_digi_it_advance(&from, i1);
                        vec_digi_it to = vec_digi_begin(&a);
                        vec_digi_it_advance(&to, i2);
                        from = vec_digi_erase_range(&from, &to);
                        /*auto it =*/ b.erase(b.begin() + i1, b.begin() + i2);
                        //CHECK_ITER(from, b, it); // wrong return value
                        print_vec(&a);
                        print_vector(b);
                    }
                    CHECK(a, b);
                    break;
                }
#endif
                case TEST_INSERT:
                {
                    size_t amount = TEST_RAND(512);
                    for(size_t count = 0; count < amount; count++)
                    {
                        const int value = TEST_RAND(TEST_MAX_VALUE);
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, DIGI{value});
                        vec_digi_it pos = vec_digi_begin(&a);
                        vec_digi_it_advance(&pos, index);
                        vec_digi_insert(&pos, digi_init(value));
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
                        b.insert(b.begin() + index, DIGI{value});
                        vec_digi_insert_index(&a, index, digi_init(value));
                    }
                    break;
                }
                case TEST_INSERT_COUNT:
                {
                    size_t count = TEST_RAND(512);
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size);
                    b.insert(b.begin() + index, count, DIGI{value});
                    vec_digi_it pos = vec_digi_begin(&a);
                    vec_digi_it_advance(&pos, index);
                    vec_digi_insert_count(&pos, count, digi_init(value));
                    vec_digi_reserve(&a, b.capacity()); // our growth strategy
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
                        vec_digi aa = vec_digi_init_from(&a);
                        std::vector<DIGI> bb;
                        vec_digi_it first_a, last_a;
                        std::vector<DIGI>::iterator first_b, last_b;
                        for(size_t pushes = 0; pushes < size2; pushes++)
                        {
                            const int value = TEST_RAND(TEST_MAX_VALUE);
                            vec_digi_push_back(&aa, digi_init(value));
                            bb.push_back(DIGI{value});
                        }
                        print_vec(&aa);
                        get_random_iters (&aa, &first_a, &last_a, bb, first_b, last_b);
                        const size_t index = TEST_RAND(a.size);
                        vec_digi_it pos = vec_digi_begin(&a);
                        vec_digi_it_advance(&pos, index);
                        b.insert(b.begin() + index, first_b, last_b);
                        vec_digi_insert_range(&pos, &first_a, &last_a);
                        // our growth strategy is better. but for test sake adjust it
                        vec_digi_reserve(&a, b.capacity());
                        print_vec(&a);
                        print_vector(b);
                        CHECK(a, b);
                        vec_digi_free(&aa);
                    }
                    break;
                }
                case TEST_RESIZE:
                {
                    const size_t resize = 3 * TEST_RAND(a.size) + 1;
                    b.resize(resize);
                    LOG("STL resize by %zu %zu -> %zu\n", resize, b.size(), b.capacity());
                    vec_digi_resize(&a, resize, digi_init(0));
                    LOG("CTL resize by %zu %zu -> %zu\n", resize, a.size, a.capacity);
                    break;
                }
                case TEST_RESERVE:
                {
                    const size_t capacity = 3 * TEST_RAND(a.capacity) + 1;
                    b.reserve(capacity);
                    vec_digi_reserve(&a, capacity);
                    LOG("CTL reserve by %zu %zu\n", capacity, a.capacity);
                    LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                    break;
                }
                case TEST_SHRINK_TO_FIT:
                {
                    b.shrink_to_fit();
                    vec_digi_shrink_to_fit(&a);
                    LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                    LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                    break;
                }
                case TEST_SORT:
                {
                    vec_digi_sort(&a);
                    std::sort(b.begin(), b.end());
                    break;
                }
                case TEST_COPY:
                {
                    vec_digi aa = vec_digi_copy(&a);
                    std::vector<DIGI> bb = b;
                    CHECK(aa, bb);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    size_t assign_size = TEST_RAND(a.size) + 1;
                    vec_digi_assign(&a, assign_size, digi_init(value));
                    b.assign(assign_size, DIGI{value});
                    break;
                }
                case TEST_SWAP:
                {
                    LOG("CTL capacity %zu\n", a.capacity);
                    LOG("STL capacity %zu\n", b.capacity());
                    vec_digi aa = vec_digi_copy(&a);
                    vec_digi aaa = vec_digi_init();
                    LOG("CTL capacity %zu copy %zu\n", aa.capacity, aa.size);
                    LOG("CTL capacity %zu init\n", aaa.capacity);
                    std::vector<DIGI> bb = b;
                    std::vector<DIGI> bbb;
                    vec_digi_swap(&aaa, &aa);
                    LOG("CTL capacity %zu after swap %zu\n", aaa.capacity, aaa.size);
                    std::swap(bb, bbb);
                    LOG("STL capacity %zu after swap %zu\n", bbb.capacity(), bbb.size());
                    CHECK(aaa, bbb);
                    vec_digi_free(&aaa);
                    break;
                }
                case TEST_REMOVE_IF:
                {
                    vec_digi_remove_if(&a, digi_is_odd);
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
                    break;
                }
                case TEST_ERASE_IF:
                {
#if __cpp_lib_erase_if >= 202002L
                    size_t num_a = vec_digi_erase_if(&a, digi_is_odd);
                    size_t num_b = std::erase_if(b, DIGIc_is_odd);
                    assert(num_a == num_b);
#else
                    vec_digi_erase_if(&a, digi_is_odd);
                    b.erase(std::remove_if(b.begin(), b.end(), DIGI_is_odd), b.end());
#endif
                    break;
                }
                case TEST_EQUAL:
                {
                    vec_digi aa = vec_digi_copy(&a);
                    std::vector<DIGI> bb = b;
                    assert(vec_digi_equal(&a, &aa));
                    assert(b == bb);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_FIND:
                {
                    if(a.size > 0)
                    {
                        const size_t index = TEST_RAND(a.size);
                        int value = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                            : *vec_digi_at(&a, index)->value;
                        digi key = digi_init(value);
                        vec_digi_it aa = vec_digi_find(&a, key);
                        auto bb = find(b.begin(), b.end(), DIGI{value});
                        bool found_a = !vec_digi_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*(aa.ref->value) == *bb->value);
                        digi_free(&key);
                    }
                    break;
                }
                case TEST_FIND_IF:
                {
                    vec_digi_it it = vec_digi_find_if(&a, digi_is_odd);
                    auto bb = std::find_if(b.begin(), b.end(), DIGI_is_odd);
                    if(bb == b.end())
                        assert(vec_digi_it_done(&it));
                    else
                        assert(*(it.ref->value) == *bb->value);
                    break;
                }
                case TEST_FIND_IF_NOT:
                {
                    vec_digi_it aa = vec_digi_find_if_not(&a, digi_is_odd);
                    auto bb = std::find_if_not(b.begin(), b.end(), DIGI_is_odd);
                    print_vec(&a);
                    print_vector(b);
                    CHECK_ITER(aa, b, bb);
                    if(bb == b.end())
                        assert(vec_digi_it_done(&aa));
                    else
                        assert(*(aa.ref->value) == *bb->value);
                    break;
                }
                case TEST_ALL_OF:
                {
                    bool is_a = vec_digi_all_of(&a, digi_is_odd);
                    bool is_b = std::all_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_ANY_OF:
                {
                    bool is_a = vec_digi_any_of(&a, digi_is_odd);
                    bool is_b = std::any_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_NONE_OF:
                {
                    bool is_a = vec_digi_none_of(&a, digi_is_odd);
                    bool is_b = std::none_of(b.begin(), b.end(), DIGI_is_odd);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_COUNT:
                {
                    int key = TEST_RAND(TEST_MAX_SIZE);
                    int aa = vec_digi_count(&a, digi_init(key));
                    int bb = std::count(b.begin(), b.end(), DIGI{key});
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF:
                {
                    size_t count_a = vec_digi_count_if(&a, digi_is_odd);
                    size_t count_b = std::count_if(b.begin(), b.end(), DIGI_is_odd);
                    assert(count_a == count_b);
                    break;
                }
                case TEST_FIND_RANGE:
                {
                    int vb = TEST_RAND(2) ? TEST_RAND(TEST_MAX_VALUE)
                        : random_element(&a);
                    digi key = digi_init(vb);
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_digi_find_range(&first_a, &last_a, key);
                    auto it = find(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    digi_free (&key); // special
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_IF_RANGE:
                {
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_digi_find_if_range(&first_a, &last_a, digi_is_odd);
                    auto it = find_if(first_b, last_b, DIGI_is_odd);
                    print_vec(&a);
                    print_vector(b);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_FIND_IF_NOT_RANGE:
                {
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = vec_digi_find_if_not_range(&first_a, &last_a, digi_is_odd);
                    auto it = find_if_not(first_b, last_b, DIGI_is_odd);
                    CHECK_ITER(first_a, b, it);
                    break;
                }
                case TEST_ALL_OF_RANGE:
                {
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_digi_all_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = all_of(first_b, last_b, DIGI_is_odd);
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
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_digi_any_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = any_of(first_b, last_b, DIGI_is_odd);
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
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = vec_digi_none_of_range(&first_a, &last_a, digi_is_odd);
                    bool bb = none_of(first_b, last_b, DIGI_is_odd);
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
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t numa = vec_digi_count_if_range(&first_a, &last_a, digi_is_odd);
                    size_t numb = count_if(first_b, last_b, DIGI_is_odd);
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
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    // used to fail with 0,0 of 0
                    size_t numa = vec_digi_count_range(&first_a, &last_a, digi_init(v));
                    size_t numb = count(first_b, last_b, DIGI{v});
                    assert(numa == numb);
                    break;
                }
                case TEST_GENERATE:
                {
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
                    vec_digi aa = vec_digi_copy(&a);
                    std::vector<DIGI> bb = b;
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&aa, &first_a, &last_a, bb, first_b, last_b);
                    if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                        size_t i = first_b - bb.begin();
                        vec_digi_set(&aa, i, digi_init(0));
                        bb[i] = DIGI{0};
                    }
                    print_vec_range(first_a);                    
                    vec_digi_it found_a = vec_digi_search(&a, &first_a, &last_a);
                    auto found_b = search(b.begin(), b.end(), first_b, last_b);
                    LOG("found a: %s\n", vec_digi_it_done(&found_a) ? "no" : "yes");
                    LOG("found b: %s\n", found_b == b.end() ? "no" : "yes");
                    CHECK_ITER(found_a, b, found_b);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_SEARCH_RANGE:
                {
                    vec_digi aa = vec_digi_copy(&a);
                    std::vector<DIGI> bb = b;
                    vec_digi_it needle, last_a, range;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&aa, &needle, &last_a, bb, first_b, last_b);
                    if (aa.size && TEST_RAND(2)) { // 50% unsuccessful
                        size_t i = first_b - bb.begin();
                        vec_digi_set(&aa, i, digi_init(0));
                        bb[i] = DIGI{0};
                    }
                    print_vec_range(needle);
                    range = vec_digi_begin(&a);
                    bool found = vec_digi_search_range(&range, &needle);
                    auto iter = search(b.begin(), b.end(), first_b, last_b);
                    LOG("found a: %s\n", found ? "yes" : "no");
                    LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                    assert(found == !vec_digi_it_done(&range));
                    CHECK_ITER(range, b, iter);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_ADJACENT_FIND:
                {
                    print_vec(&a);
                    vec_digi_it aa = vec_digi_adjacent_find(&a);
                    auto bb = adjacent_find(b.begin(), b.end());
                    CHECK_ITER(aa, b, bb);
                    LOG("found %s\n", vec_digi_it_done(&aa) ? "no" : "yes");
                    break;
                }
                case TEST_ADJACENT_FIND_RANGE:
                {
                    vec_digi_it range, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &range, &last_a, b, first_b, last_b);
                    print_vec_range(range);
                    vec_digi_it *aa = vec_digi_adjacent_find_range(&range);
                    auto bb = adjacent_find(first_b, last_b);
                    CHECK_ITER(*aa, b, bb);
                    LOG("found %s\n", vec_digi_it_done(aa) ? "no" : "yes");
                    break;
                }
#ifdef DEBUG
                case TEST_LOWER_BOUND: // 64
                {
                    int median = *vec_digi_at(&a, a.size / 2)->value;
                    vec_digi_it aa = vec_digi_lower_bound(&a, digi_init(median));
                    auto bb = lower_bound(b.begin(), b.end(), DIGI{median});
                    CHECK_ITER(aa, b, bb);
                    break;
                }
                case TEST_UPPER_BOUND:
                {
                    int median = *vec_digi_at(&a, a.size / 2)->value;
                    vec_digi_it aa = vec_digi_upper_bound(&a, digi_init(median));
                    auto bb = upper_bound(b.begin(), b.end(), DIGI{median});
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
                case TEST_GENERATE_RANGE:
                {
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    digi_generate_reset();
                    vec_digi_generate_range(&first_a, &last_a, digi_generate);
                    digi_generate_reset();
                    std::generate(first_b, last_b, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM:
                {
                    vec_digi aa = vec_digi_transform(&a, digi_untrans);
                    std::vector<DIGI> bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), bb.begin(), DIGI_untrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_EMPLACE_BACK: // 36
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
# if __cplusplus >= 201103L
                    b.emplace_back(DIGI{value});
# else
                    b.insert(b.begin() + index, DIGI{value});
# endif
                    digi key = digi_init(value);
                    vec_digi_emplace_back(&a, &key);
                    CHECK(a, b);
                    break;
                }
#ifdef DEBUG
                case TEST_EMPLACE: // 37
                {
                    const int value = TEST_RAND(TEST_MAX_VALUE);
                    const size_t index = TEST_RAND(a.size);
                    vec_digi_it pos = vec_digi_begin(&a);
                    vec_digi_it_advance(&pos, index);
# if __cplusplus >= 201103L
                    b.emplace(b.begin() + index, DIGI{value});
# else
                    b.insert(b.begin() + index, DIGI{value});
# endif
                    digi key = digi_init(value);
                    vec_digi_emplace(&pos, &key);
                    CHECK(a, b);
                    break;
                }
#endif // DEBUG
                case TEST_INCLUDES:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    bool a_found = vec_digi_includes(&a, &aa);
                    bool b_found = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                    assert (a_found == b_found);
                    CHECK(aa, bb);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_INCLUDES_RANGE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi_it first_a1, last_a1;
                    std::vector<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    vec_digi_it first_a2, last_a2;
                    std::vector<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a - aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    bool a_found = vec_digi_includes_range(&first_a1, &first_a2);
                    std::vector<DIGI> bbb;
                    LOG("STL b + bb\n");
                    print_vector(b);
                    print_vector(bb);
                    bool b_found = std::includes(first_b1, last_b1, first_b2, last_b2);
                    assert(a_found == b_found);
                    CHECK(aa, bb);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_UNION:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi aaa = vec_digi_union(&a, &aa);
# ifndef _MSC_VER
                    std::vector<DIGI> bbb;
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
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_INTERSECTION:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi aaa = vec_digi_intersection(&a, &aa);
# ifndef _MSC_VER
                    std::vector<DIGI> bbb;
                    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                          std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    print_vec(&a);
                    print_vec(&aa);
                    print_vec(&aaa);
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    print_vec(&a);
                    vec_digi aaa = vec_digi_difference(&a, &aa);
# ifndef _MSC_VER
                    std::vector<DIGI> bbb;
                    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                        std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("difference",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi aaa = vec_digi_symmetric_difference(&a, &aa);
# ifndef _MSC_VER
                    std::vector<DIGI> bbb;
                    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                                  std::back_inserter(bbb));
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference",aaa,bbb);
                    CHECK(aaa, bbb);
# endif
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_UNION_RANGE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi_it first_a1, last_a1;
                    std::vector<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    vec_digi_it first_a2, last_a2;
                    std::vector<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_digi aaa = vec_digi_union_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<DIGI> bbb;
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
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_INTERSECTION_RANGE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi_it first_a1, last_a1;
                    std::vector<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    vec_digi_it first_a2, last_a2;
                    std::vector<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_digi aaa = vec_digi_intersection_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<DIGI> bbb;
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
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE_RANGE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi_it first_a1, last_a1;
                    std::vector<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    vec_digi_it first_a2, last_a2;
                    std::vector<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a (%zu) + aa (%zu)\n", a.size, aa.size);
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_digi aaa = vec_digi_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa (%zu)\n", aa.size);
                    print_vec(&aaa);

                    std::vector<DIGI> bbb;
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
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE_RANGE:
                {
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_sort(&a);
                    vec_digi_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    vec_digi_it first_a1, last_a1;
                    std::vector<DIGI>::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    vec_digi_it first_a2, last_a2;
                    std::vector<DIGI>::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    print_vec_range(first_a1);
                    print_vec_range(first_a2);
                    vec_digi aaa = vec_digi_symmetric_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    print_vec(&aaa);

                    std::vector<DIGI> bbb;
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
                    vec_digi_free(&aaa);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_GENERATE_N:
                {
                    size_t count = TEST_RAND(20);
                    LOG("generate_n %zu\n", count);                    
# ifndef _MSC_VER                    
                    digi_generate_reset();
                    vec_digi_generate_n(&a, count, digi_generate);
                    print_vec(&a);
                    digi_generate_reset();
                    // FIXME The STL is arguably broken here.
                    int n = MIN(count, b.size());
                    b.erase(b.begin(), b.begin()+n);
                    std::generate_n(std::inserter(b, b.begin()), n, DIGI_generate);
                    print_vector(b);
                    CHECK(a, b);
#endif
                    break;
                }
#ifdef DEBUG
                case TEST_GENERATE_N_RANGE:
                {
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t off = first_b - b.begin();
                    size_t count = TEST_RAND(20 - off);
                    digi_generate_reset();
                    vec_digi_generate_n_range(&first_a, count, digi_generate);
                    digi_generate_reset();
                    std::generate_n(first_b, count, DIGI_generate);
                    CHECK(a, b);
                    break;
                }
#endif // DEBUG
                case TEST_TRANSFORM_IT:
                {
                    print_vec(&a);
                    if (a.size < 2)
                        break;
                    vec_digi_it pos = vec_digi_begin(&a);
                    vec_digi_it_advance(&pos, 1);
                    vec_digi aa = vec_digi_transform_it(&a, &pos, digi_bintrans);
                    print_vec(&aa);
# ifndef _MSC_VER
                    std::vector<DIGI> bb;
                    bb.reserve(b.size()-1);
                    std::transform(b.begin(), b.end()-1, b.begin()+1,
                                   std::back_inserter(bb), DIGI_bintrans);
                    print_vector(bb);
                    ADJUST_CAP("transform_it", aa, bb);
                    CHECK(aa, bb);
# endif
                    CHECK(a, b);
                    vec_digi_free(&aa);
                    break;
                }
#ifdef DEBUG
                case TEST_TRANSFORM_RANGE:
                {
                    print_vec(&a);
                    if (a.size < 2)
                        break;
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    vec_digi aa = vec_digi_init();
                    vec_digi_resize(&aa, last_b - first_b, digi_init(0));
                    vec_digi_it dest = vec_digi_begin(&aa);
                    vec_digi_it it = vec_digi_transform_range(&first_a, &last_a, dest,
                                                              digi_untrans);
# ifndef _MSC_VER
                    std::vector<DIGI> bb;
                    bb.reserve(last_b - first_b);
                    auto iter = std::transform(first_b, last_b, std::back_inserter(bb),
                                               DIGI_untrans);
                    ADJUST_CAP("transform_range", aa, bb);
                    //CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
# endif
                    // heap use-after-free
                    CHECK(a, b);
                    vec_digi_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_IT_RANGE:
                {
                    if (a.size < 2)
                        break;
                    vec_digi_it first_a, last_a;
                    std::vector<DIGI>::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    vec_digi_it pos = vec_digi_begin(&a);
                    vec_digi_it_advance(&pos, 1);
                    vec_digi aa = vec_digi_init();
                    vec_digi_resize(&aa, last_b - first_b, digi_init(0));
                    vec_digi_it dest = vec_digi_begin(&aa);
                    vec_digi_it it = vec_digi_transform_it_range(&first_a, &last_a,
                                                                 &pos, dest, digi_bintrans);
                    auto it2 = b.begin();
                    std::advance(it2, 1);
# ifndef _MSC_VER
                    std::vector<DIGI> bb;
                    bb.reserve(last_b - first_b - 1);
                    auto iter = std::transform(first_b, last_b, it2,
                                               std::back_inserter(bb), DIGI_bintrans);
                    ADJUST_CAP("transform_it_range", aa, bb);
                    //CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
# endif
                    // heap use-after-free
                    CHECK(a, b);
                    vec_digi_free(&aa);
                    break;
                }
#endif // DEBUG
                case TEST_MISMATCH:
                {
                    if(a.size < 2)
                        break;
                    vec_digi aa;
                    std::vector<DIGI> bb;
                    gen_vectors(&aa, bb, TEST_RAND(a.size));
                    vec_digi_it b1, b2;
                    b1 = vec_digi_begin(&a);
                    b2 = vec_digi_begin(&aa);
                    vec_digi_it r1a, last1_a, r2a, last2_a;
                    std::vector<DIGI>::iterator r1b, last1_b, r2b, last2_b;
                    get_random_iters (&a, &r1a, &last1_a, b, r1b, last1_b);
                    get_random_iters (&aa, &r2a, &last2_a, bb, r2b, last2_b);
                    /*bool found_a = */vec_digi_mismatch(&r1a, &r2a);
                    auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
                    int d1a = vec_digi_it_distance(&b1, &r1a);
                    int d2a = vec_digi_it_distance(&b2, &r2a);
                    LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                    //TODO check found_a against iter results
                    assert(d1a == distance(b.begin(), pair.first));
                    assert(d2a == distance(bb.begin(), pair.second));
                    vec_digi_free(&aa);
                    break;
                }
#if 0
                case TEST_FIND_END:
                {
                    if(a.size > 0)
                    {
                        vec_digi_it first_a, last_a;
                        vec_digi_it aa = vec_digi_find_end(&a, &s_first, &s_last);
                        auto bb = find_end(b.begin(), b.end(), ...);
                        bool found_a = !vec_digi_it_done(&aa);
                        bool found_b = bb != b.end();
                        assert(found_a == found_b);
                        if(found_a && found_b)
                            assert(*(aa->value) == *bb->value);
                    }
                    break;
                }
                case TEST_FIND_END_RANGE:
                {
                    vec_digi_it first_a, last_a, s_first, s_last;
                    std::vector<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = vec_digi_find_end_range(&first_a, &last_a, &s_first_a, &s_last_a);
                    auto it = find_end(first_b, last_b, vb);
                    CHECK_ITER(first_a, b, it);
                    CHECK(a, b);
# endif
                    break;
                }
                case TEST_FIND_END_IF_RANGE:
                {
                    vec_digi_it first_a, last_a, s_first, s_last;
                    std::vector<DIGI>::iterator first_b, last_b, s_first_b, s_last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
# if __cpp_lib_erase_if >= 202002L
                    first_a = vec_digi_find_end_if_range(&first_a, &last_a, &s_first, &s_last, digi_is_odd);
                    auto it = find_end(first_b, last_b, s_first_b, s_last_b, DIGI_is_odd);
                    CHECK_ITER(first_a, b, it);
                    digi_free (&key); // special
                    CHECK(a, b);
# endif
                    break;
                }
#endif // 0
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
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
