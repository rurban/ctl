#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#define INCLUDE_ALGORITHM
#define INCLUDE_NUMERIC
#include <ctl/string.h>

#include <algorithm>
#include <numeric>
#include <string>
#include <string>
#ifdef NEED_RANDOM_ENGINE
#include <random>
#endif

#define FOREACH_METH(TEST)                                                                                             \
    TEST(PUSH_BACK)                                                                                                    \
    TEST(POP_BACK)                                                                                                     \
    TEST(APPEND)                                                                                                       \
    TEST(C_STR)                                                                                                        \
    TEST(CLEAR)                                                                                                        \
    TEST(ERASE)                                                                                                        \
    TEST(ERASE_INDEX)                                                                                                  \
    TEST(RESIZE)                                                                                                       \
    TEST(RESERVE)                                                                                                      \
    TEST(SHRINK_TO_FIT)                                                                                                \
    TEST(SORT)                                                                                                         \
    TEST(COPY)                                                                                                         \
    TEST(SWAP)                                                                                                         \
    TEST(INSERT)                                                                                                       \
    TEST(INSERT_INDEX)                                                                                                 \
    TEST(INSERT_COUNT)                                                                                                 \
    TEST(INSERT_RANGE)                                                                                                 \
    TEST(ASSIGN)                                                                                                       \
    TEST(EQUAL)                                                                                                        \
    TEST(EQUAL_VALUE)                                                                                                  \
    TEST(EQUAL_RANGE)                                                                                                  \
    TEST(REPLACE)                                                                                                      \
    TEST(FIND)                                                                                                         \
    TEST(RFIND)                                                                                                        \
    TEST(FIND_FIRST_OF)                                                                                                \
    TEST(FIND_FIRST_OF_RANGE)                                                                                          \
    TEST(FIND_LAST_OF)                                                                                                 \
    TEST(FIND_FIRST_NOT_OF)                                                                                            \
    TEST(FIND_LAST_NOT_OF)                                                                                             \
    TEST(SUBSTR)                                                                                                       \
    TEST(COMPARE)                                                                                                      \
    TEST(COUNT)                                                                                                        \
    TEST(COUNT_IF)                                                                                                     \
    TEST(ALL_OF)                                                                                                       \
    TEST(ANY_OF)                                                                                                       \
    TEST(NONE_OF)                                                                                                      \
    TEST(FIND_IF)                                                                                                      \
    TEST(FIND_IF_NOT)                                                                                                  \
    TEST(FIND_END)                                                                                                     \
    TEST(FIND_END_RANGE)                                                                                               \
    TEST(FIND_RANGE)                                                                                                   \
    TEST(FIND_IF_RANGE)                                                                                                \
    TEST(FIND_IF_NOT_RANGE)                                                                                            \
    TEST(ALL_OF_RANGE)                                                                                                 \
    TEST(ANY_OF_RANGE)                                                                                                 \
    TEST(NONE_OF_RANGE)                                                                                                \
    TEST(COUNT_IF_RANGE)                                                                                               \
    TEST(COUNT_RANGE)                                                                                                  \
    TEST(MISMATCH)                                                                                                     \
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
    TEST(COPY_IF)                                                                                                      \
    TEST(COPY_IF_RANGE)                                                                                                \
    TEST(SEARCH)                                                                                                       \
    TEST(SEARCH_RANGE)                                                                                                 \
    TEST(SEARCH_N)                                                                                                     \
    TEST(SEARCH_N_RANGE)                                                                                               \
    TEST(ADJACENT_FIND)                                                                                                \
    TEST(ADJACENT_FIND_RANGE)                                                                                          \
    TEST(LOWER_BOUND)                                                                                                  \
    TEST(UPPER_BOUND)                                                                                                  \
    TEST(LOWER_BOUND_RANGE)                                                                                            \
    TEST(UPPER_BOUND_RANGE)                                                                                            \
    TEST(BINARY_SEARCH)                                                                                                \
    TEST(BINARY_SEARCH_RANGE)                                                                                          \
    TEST(MERGE)                                                                                                        \
    TEST(MERGE_RANGE)                                                                                                  \
    TEST(LEXICOGRAPHICAL_COMPARE)                                                                                      \
    TEST(INCLUDES)                                                                                                     \
    TEST(INCLUDES_RANGE)                                                                                               \
    TEST(IS_SORTED)                                                                                                    \
    TEST(IS_SORTED_UNTIL)                                                                                              \
    TEST(REVERSE)                                                                                                      \
    TEST(REVERSE_RANGE)                                                                                                \
    TEST(IOTA)                                                                                                         \
    TEST(IOTA_RANGE)                                                                                                   \
    TEST(SHUFFLE)                                                                                                      \
    TEST(SHUFFLE_RANGE)

#define FOREACH_DEBUG(TEST)                                                                                            \
    TEST(GENERATE_N_RANGE) /* 83 */                                                                                    \
    TEST(TRANSFORM_RANGE)                                                                                              \
    TEST(UNIQUE)                                                                                                       \
    TEST(UNIQUE_RANGE)

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
CLANG_DIAG_IGNORE(-Wunneeded-internal-declaration)
// only needed for the size
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
CLANG_DIAG_RESTORE
#ifdef DEBUG
static const char *test_names[] = {
    FOREACH_METH(GENERATE_NAME)
    FOREACH_DEBUG(GENERATE_NAME)
    ""};
#endif
// clang-format on

#define MIN_STR_SIZE (30) // NO SUPPORT FOR SMALL STRINGS yet
#define ALPHA_LETTERS (23)

// mark functions which need 16 align
#define LOG_CAP(a, b)                                                                                                  \
    LOG("ctl capacity %u (0x%lx) vs %u (0x%lx) %s\n", (unsigned)a.capacity, a.capacity, (unsigned)b.capacity(),        \
        b.capacity(), a.capacity == b.capacity() ? "" : "FAIL")

// tested variants
#if (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L && _GLIBCXX_RELEASE < 11)
// Tested ok with g++ 10, g++ 7.5,
// clang 10 (libc++ 11-18), apple clang 12 fail
#define ASSERT_EQUAL_CAP(c, s) assert(s.capacity() == c.capacity);
#else
// other llvm libc++ fail (gh actions), msvc also.
#define ASSERT_EQUAL_CAP(c, s)                                                                                         \
    if (s.capacity() != c.capacity)                                                                                    \
    {                                                                                                                  \
        printf("capacity %u vs %u FAIL\n", (unsigned)c.capacity, (unsigned)s.capacity());                              \
        fail++;                                                                                                        \
    }
#endif

// cheat growth. the STL often has wrong and slow growth policies for algos.
// we rather reserve before, and then dont overallocate later.
#define ADJUST_CAP(m, c, s)                                                                                            \
    if (c.size == s.size() && c.capacity != s.capacity())                                                              \
    {                                                                                                                  \
        printf("%s capacity %u => %u\n", m, (unsigned)c.capacity, (unsigned)s.capacity());                             \
        str_fit(&c, s.capacity());                                                                                     \
    }

#define CHECK(_x, _y)                                                                                                  \
    {                                                                                                                  \
        assert(strlen(str_c_str(&_x)) == strlen(_y.c_str()));                                                          \
        assert(strcmp(str_c_str(&_x), _y.c_str()) == 0);                                                               \
        ASSERT_EQUAL_CAP(_x, _y);                                                                                      \
        assert(_x.size == _y.size());                                                                                  \
        assert(str_empty(&_x) == _y.empty());                                                                          \
        if (_x.size > 0)                                                                                               \
        {                                                                                                              \
            assert(_y.front() == *str_front(&_x));                                                                     \
            assert(_y.back() == *str_back(&_x));                                                                       \
        }                                                                                                              \
        std::string::iterator _iter = _y.begin();                                                                      \
        str_foreach(&_x, _ref)                                                                                         \
        {                                                                                                              \
            assert(*_ref == *_iter);                                                                                   \
            _iter++;                                                                                                   \
        }                                                                                                              \
        char *_it = str_begin(&_x);                                                                                    \
        for (auto &_d : _y)                                                                                            \
        {                                                                                                              \
            assert(*_it == _d);                                                                                        \
            _it++;                                                                                                     \
        }                                                                                                              \
        for (size_t i = 0; i < _y.size(); i++)                                                                         \
            assert(_y.at(i) == *str_at(&_x, i));                                                                       \
    }

#define CHECK_ITER(aa, b, bb)                                                                                          \
    if ((aa).ref != &(aa).container->vector[(aa).container->size])                                                     \
    {                                                                                                                  \
        assert(bb != b.end());                                                                                         \
        assert(*(aa).ref == *bb);                                                                                      \
    }                                                                                                                  \
    else                                                                                                               \
        assert(bb == b.end())
#define CHECK_RANGE(_it, _iter, b_end)                                                                                 \
    if (!str_it_done(&_it))                                                                                            \
    {                                                                                                                  \
        assert(_iter != b_end);                                                                                        \
        assert(*(_it).ref == *_iter);                                                                                  \
    }                                                                                                                  \
    else                                                                                                               \
        assert(_iter == b_end)

#define RAND_CHAR ('0' + TEST_RAND('z' - '0'))
#define RAND_ALPHA ((TEST_RAND(2) ? 'a' : 'A') + TEST_RAND(ALPHA_LETTERS))

static char *create_test_string(size_t size)
{
    char *temp = (char *)malloc(size + 1);
    for (size_t i = 0; i < size; i++)
    {
        temp[i] = RAND_ALPHA;
    }
    temp[size] = '\0';
    return temp;
}

static int char_compare(char *a, char *b)
{
    return *a < *b;
}

int is_upper(char *a)
{
    return *a >= 'A' && *a <= 'Z';
}

int STL_is_upper(const char &a)
{
    return a >= 'A' && a <= 'Z';
}

static int _generator_state = 0;
void str_generate_reset()
{
    _generator_state = 0;
}
char str_generate(void)
{
    _generator_state++;
    return '0' + (_generator_state % ('z' - '0'));
}
char STR_generate(void)
{
    _generator_state++;
    return '0' + (_generator_state % ('z' - '0'));
}
char str_untrans(char *s)
{
    return *s + 1;
}
char STR_untrans(const char &s)
{
    return s + 1;
}
char str_bintrans(char *s1, char *s2)
{
    return *s1 ^ *s2;
}
char STR_bintrans(const char &s1, const char &s2)
{
    return s1 ^ s2;
}

static void gen_strings(str *a, std::string &b, size_t size)
{
    char *_ta = create_test_string(size);
    *a = str_init(_ta);
    b = _ta;
    str_fit(a, b.capacity());
    free(_ta);
}

static void get_random_iters(str *a, str_it *first_a, std::string &b, std::string::iterator &first_b,
                             std::string::iterator &last_b)
{
    str_it last_a;
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %u, %u of %u\n", (unsigned)r1, (unsigned)r2, (unsigned)a->size);
    if (a->size)
    {
        str_it it1 = str_it_begin(a);
        first_b = b.begin();
        str_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            last_a = str_it_end(a);
            last_b = b.end();
        }
        else
        {
            str_it it2 = str_it_begin(a);
            last_b = b.begin();
            str_it_advance(&it2, r2);
            last_b += r2;
            last_a = it2;
        }
    }
    else
    {
        str_it end = str_it_end(a);
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
    INIT_TEST_LOOPS(10,false)
    for (unsigned loop = 0; loop < loops; loop++)
    {
        size_t str_size = TEST_RAND(TEST_MAX_SIZE);
        if (str_size < MIN_STR_SIZE)
            str_size = MIN_STR_SIZE;
#if defined(DEBUG) && !defined(LONG)
        str_size = 15; // short strings for certain methods
#endif
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for (size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            char *base = create_test_string(str_size);
            char *temp; /* = create_test_string(TEST_RAND(256)); */
            str a, aa, aaa;
            std::string b, bb, bbb;
            str_it range_a1, range_a2, it;
            str_it *pos;
            std::string::iterator first_b1, last_b1, first_b2, last_b2, iter;
            bool found_a, found_b;
            size_t num_a, num_b;
            char value = RAND_ALPHA;
            size_t index = TEST_RAND(str_size);
#ifdef NEED_RANDOM_ENGINE
            std::default_random_engine rng {seed};
#endif

            if (mode == MODE_DIRECT)
            {
                LOG("mode DIRECT\n");
                a = str_init(base);
                b = base;
            }
            if (mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
                a = str_init("");
                for (size_t i = 0; i < str_size; i++)
                {
                    str_push_back(&a, base[i]);
                    b.push_back(base[i]);
                }
            }
            a.compare = char_compare;
            int which;
            if (tests.size)
            {
                which = *queue_int_front(&tests);
                if (mode == MODE_TOTAL - 1) // pop only at 2nd growth mode
                    queue_int_pop(&tests);
            }
            else
                which = (test >= 0 ? test : TEST_RAND(TEST_TOTAL));
            LOG("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            RECORD_WHICH;
            switch (which)
            {
            case TEST_PUSH_BACK:
                b.push_back(value);
                str_push_back(&a, value);
                LOG_CAP(a, b);
                break;
            case TEST_POP_BACK:
                if (a.size > 0)
                {
                    b.pop_back();
                    str_pop_back(&a);
                }
                LOG_CAP(a, b);
                break;
            case TEST_APPEND:
                temp = create_test_string(TEST_RAND(256));
                str_append(&a, temp);
                b.append(temp);
                free(temp);
                break;
            case TEST_C_STR:
                assert(strlen(str_c_str(&a))); // strlen(NULL) is valid
                assert(str_c_str(&a) == str_data(&a));
                LOG("CTL C_STR %zu %zu\n", a.size, a.capacity);
                break;
            case TEST_REPLACE: {
                temp = create_test_string(TEST_RAND(a.size));
                str_replace(&a, index, index, temp);
                b.replace(index, index, temp);
                free(temp);
                break;
            }
            case TEST_FIND: {
                const size_t size = TEST_RAND(4);
                temp = create_test_string(size);
                assert(str_find(&a, temp) == b.find(temp));
                free(temp);
                break;
            }
            case TEST_RFIND: {
                temp = create_test_string(TEST_RAND(3));
                assert(str_rfind(&a, temp) == b.rfind(temp));
                free(temp);
                break;
            }
            case TEST_FIND_FIRST_OF: {
                const size_t size = TEST_RAND(4);
                temp = create_test_string(size);
                LOG("str_find_first_of(\"%s\", \"%s\')\n", a.vector, temp);
                num_a = str_find_first_of(&a, temp);
                num_b = b.find_first_of(temp);
                LOG("=> %zu vs %zu\n", num_a, num_b);
                assert(num_a == num_b);
                free(temp);
                break;
            }
            case TEST_FIND_FIRST_OF_RANGE: {
                const size_t size = TEST_RAND(4);
                temp = create_test_string(size);
                bb = temp;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = str_init(temp);
                range_a2 = str_it_begin(&aa);
                LOG("str_find_first_of_range(\"%.*s\", [%s])\n", (int)(last_b1 - first_b1),
                    range_a1.ref, temp);
                free(temp);
                found_a = str_find_first_of_range(&range_a1, &range_a2);
                iter = std::find_first_of(first_b1, last_b1, bb.begin(), bb.end());
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", iter != last_b1 ? "yes" : "no",
                    range_a1.ref - a.vector, iter - first_b1);
                if (found_a)
                    assert(*iter == *range_a1.ref);
                else
                    assert(iter == last_b1);
                str_free(&aa);
                break;
            }
            case TEST_FIND_LAST_OF: {
                const size_t size = TEST_RAND(3);
                temp = create_test_string(size);
                assert(str_find_last_of(&a, temp) == b.find_last_of(temp));
                free(temp);
                break;
            }
            case TEST_FIND_FIRST_NOT_OF: {
                const size_t size = TEST_RAND(192);
                temp = create_test_string(size);
                assert(str_find_first_not_of(&a, temp) == b.find_first_not_of(temp));
                free(temp);
                break;
            }
            case TEST_FIND_LAST_NOT_OF: {
                const size_t size = TEST_RAND(192);
                temp = create_test_string(size);
                assert(str_find_last_not_of(&a, temp) == b.find_last_not_of(temp));
                free(temp);
                break;
            }
            case TEST_SUBSTR: {
                const size_t size = TEST_RAND(a.size - index);
                if (size > MIN_STR_SIZE)
                {
                    str substr1 = str_substr(&a, index, size);
                    std::string substr2 = b.substr(index, size);
                    CHECK(substr1, substr2);
                    str_free(&substr1);
                }
                break;
            }
            case TEST_COMPARE: {
                // CHECKME!
                char *ta = a.vector;
                char *tb = create_test_string(index);
                aa = str_init(tb);
                b = ta;
                bb = tb;
                assert(TEST_SIGN(str_compare(&a, tb))  == TEST_SIGN(b.compare(tb)));
                assert(TEST_SIGN(str_compare(&aa, ta)) == TEST_SIGN(bb.compare(ta)));
                assert(TEST_SIGN(str_compare(&a, ta))  == TEST_SIGN(b.compare(ta)));
                assert(TEST_SIGN(str_compare(&aa, tb)) == TEST_SIGN(bb.compare(tb)));
                str_free(&aa);
                free(tb);
                break;
            }
            case TEST_CLEAR: {
                str_clear(&a);
                b.clear();
                LOG_CAP(a, b);
                break;
            }
            case TEST_ERASE: {
                const size_t i = TEST_RAND(a.size - 1);
                b.erase(b.begin() + i);
                it = str_it_iter(&a, i);
                str_erase(&it);
                break;
            }
            case TEST_ERASE_INDEX: {
                const size_t i = TEST_RAND(a.size - 1);
                b.erase(b.begin() + i);
                str_erase_index(&a, i);
                break;
            }
            case TEST_INSERT_INDEX: {
                size_t letters = TEST_RAND(512);
                for (size_t count = 0; count < letters; count++)
                {
                    const size_t i = TEST_RAND(a.size);
                    value = RAND_ALPHA;
                    b.insert(b.begin() + i, value);
                    str_insert_index(&a, i, value);
                }
                break;
            }
            case TEST_INSERT: {
                size_t letters = TEST_RAND(512);
                for (size_t count = 0; count < letters; count++)
                {
                    const size_t i = TEST_RAND(a.size);
                    value = RAND_ALPHA;
                    b.insert(b.begin() + i, value);
                    it = str_it_begin(&a);
                    str_it_advance(&it, i);
                    str_insert(&it, value);
                }
                break;
            }
            case TEST_INSERT_COUNT: {
                size_t count = TEST_RAND(24);
                LOG("insert_count %zu x '%c' at %zu\n", count, value, index);
                // note: different order of args to vector!
                b.insert(b.begin() + index, count, value);
                LOG("STL \"%s\" (%zu)\n", b.c_str(), b.size());
                it = str_it_begin(&a);
                str_it_advance(&it, index);
                str_insert_count(&it, count, value);
                LOG("CTL \"%s\" (%zu)\n", str_c_str(&a), a.size);
                ADJUST_CAP("insert_count", a, b);
                CHECK(a, b);
                break;
            }
            case TEST_INSERT_RANGE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                get_random_iters(&aa, &range_a1, bb, first_b1, last_b1);
                b.insert(b.begin() + index, first_b1, last_b1);
                it = str_it_begin(&a);
                str_it_advance(&it, index);
                str_insert_range(&it, &range_a1);
                ADJUST_CAP("insert_range", a, b);
                CHECK(a, b);
                str_free(&aa);
                break;
            }
            case TEST_RESIZE: {
                const size_t resize = 3 * TEST_RAND(a.size);
                b.resize(resize);
                str_resize(&a, resize, '\0');
                LOG("CTL resize by %zu %zu %zu\n", resize, a.size, a.capacity);
                LOG("STL resize by %zu %zu %zu\n", resize, b.size(), b.capacity());
                break;
            }
            case TEST_RESERVE: {
                const size_t capacity = 3 * TEST_RAND(a.capacity);
                b.reserve(capacity);
                str_reserve(&a, capacity);
                LOG("CTL reserve by %zu %zu\n", a.capacity, a.capacity);
                LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                break;
            }
            case TEST_SHRINK_TO_FIT: {
                b.shrink_to_fit();
                str_shrink_to_fit(&a);
                LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                LOG_CAP(a, b);
                break;
            }
            case TEST_SORT: {
                LOG("before sort \"%s\"\n", str_c_str(&a));
                str_sort(&a);
                LOG("after  sort \"%s\"\n", str_c_str(&a));
                std::sort(b.begin(), b.end());
                LOG("STL    sort \"%s\"\n", b.c_str());
                LOG_CAP(a, b);
                break;
            }
            case TEST_COPY: {
                aa = str_copy(&a);
                bb = b;
                LOG("copy  a: \"%s\": %zu\n", str_c_str(&a), a.capacity);
                LOG("copy aa: \"%s\": %zu\n", str_c_str(&aa), aa.capacity);
                CHECK(aa, bb);
                str_free(&aa);
                break;
            }
            case TEST_ASSIGN: {
                str_assign(&a, index, value);
                b.assign(index, value);
                break;
            }
            case TEST_EQUAL: {
                aa = str_copy(&a);
                bb = b;
                if (TEST_RAND(2) && a.size)
                {
                    a.vector[0] = 'a';
                    b[0] = 'a';
                }
                bool same_b = b == bb;
                assert(str_equal(&a, &aa) == same_b);
                str_free(&aa);
                break;
            }
            case TEST_EQUAL_VALUE: {
                size_t size1 = MIN(TEST_RAND(a.size), 5);
                str_resize(&a, size1, '\0');
                b.resize(size1);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                index = TEST_RAND(a.size - 1);
                value = a.size ? a.vector[index] : 'a';
                LOG("equal_value %c of \"%.*s\"\n", value, (int)(range_a1.end - range_a1.ref), range_a1.ref);
                bool same_a = str_equal_value(&range_a1, value);
                bool same_b = first_b1 != last_b1;
                for (; first_b1 != last_b1; first_b1++)
                {
                    if (value != *first_b1)
                    {
                        same_b = false;
                        break;
                    }
                }
                LOG("same_a: %d same_b: %d\n", (int)same_a, (int)same_b);
                assert(same_a == same_b);
                break;
            }
            case TEST_EQUAL_RANGE: {
                aa = str_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                bool same_a = str_equal_range(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                bool same_b = std::equal(first_b1, last_b1, first_b2, last_b2);
                LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
                assert(same_a == same_b);
#else
                bool same_b = std::equal(first_b1, last_b1, first_b2);
                LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
                if (same_a != same_b)
                    printf("std::equal requires C++14 with robust_nonmodifying_seq_ops\n");
#endif
                str_free(&aa);
                break;
            }
            case TEST_LEXICOGRAPHICAL_COMPARE: {
                aa = str_copy(&a);
                bb = b;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                bool same_a = str_lexicographical_compare(&range_a1, &range_a2);
                bool same_b = std::lexicographical_compare(first_b1, last_b1, first_b2, last_b2);
                LOG("same_a: %d same_b %d\n", (int)same_a, (int)same_b);
                assert(same_a == same_b);
                str_free(&aa);
                break;
            }
            case TEST_SWAP: {
                aa = str_copy(&a);
                aaa = str_init("");
                std::string cb = b;
                str_swap(&aaa, &aa);
                std::swap(cb, bbb);
                LOG_CAP(aaa, bbb);
                CHECK(aaa, bbb);
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_COUNT: {
                assert(count(b.begin(), b.end(), value) == str_count(&a, value));
                break;
            }
            case TEST_GENERATE: {
                str_generate_reset();
                str_generate(&a, str_generate);
                str_generate_reset();
                std::generate(b.begin(), b.end(), STR_generate);
                CHECK(a, b);
                break;
            }
            case TEST_GENERATE_N: {
                size_t count = TEST_RAND(20);
                str_generate_reset();
                str_generate_n(&a, count, str_generate);
                str_generate_reset();
                std::generate_n(b.begin(), count, STR_generate);
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF: {
                it = str_find_if(&a, is_upper);
                iter = std::find_if(b.begin(), b.end(), STL_is_upper);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_FIND_IF_NOT: {
                it = str_find_if_not(&a, is_upper);
                iter = std::find_if_not(b.begin(), b.end(), STL_is_upper);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_FIND_END: {
                gen_strings(&aa, bb, TEST_RAND(4));
                range_a2 = str_it_begin(&aa);
                it = str_find_end(&a, &range_a2);
                iter = find_end(b.begin(), b.end(), bb.begin(), bb.end());
                found_a = !str_it_done(&it);
                found_b = iter != b.end();
                LOG("=> %s/%s, %ld/%ld\n", found_a ? "yes" : "no", found_b ? "yes" : "no", it.ref - a.vector,
                    iter - b.begin());
                CHECK_ITER(it, b, iter);
                assert(found_a == found_b);
                str_free(&aa);
                break;
            }
            case TEST_FIND_END_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                gen_strings(&aa, bb, TEST_RAND(4));
#if __cpp_lib_erase_if >= 202002L
                range_a2 = str_it_begin(&aa);
                it = str_find_end_range(&range_a1, &range_a2);
                iter = find_end(first_b1, last_b1, bb.begin(), bb.end());
                LOG("%s in %s\n", range_a2.ref, range_a1.ref);
                LOG("vs %s in %s\n", bb.c_str(), b.c_str());
                CHECK_ITER(it, b, iter);
#endif
                str_free(&aa);
                break;
            }
            case TEST_FIND_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = str_find_range(&range_a1, value);
                iter = std::find(first_b1, last_b1, value);
                if (found_a)
                    assert(iter != last_b1);
                else
                    assert(iter == last_b1);
                CHECK_RANGE(range_a1, iter, last_b1);
                CHECK(a, b);
                break;
            }
            case TEST_FIND_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = str_find_if_range(&range_a1, is_upper);
                iter = std::find_if(first_b1, last_b1, STL_is_upper);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_FIND_IF_NOT_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                it = str_find_if_not_range(&range_a1, is_upper);
                iter = std::find_if_not(first_b1, last_b1, STL_is_upper);
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_ALL_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = str_all_of_range(&range_a1, is_upper);
                found_b = std::all_of(first_b1, last_b1, STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = str_any_of_range(&range_a1, is_upper);
                found_b = std::any_of(first_b1, last_b1, STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = str_none_of_range(&range_a1, is_upper);
                found_b = std::none_of(first_b1, last_b1, STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                num_a = str_count_if_range(&range_a1, is_upper);
                num_b = std::count_if(first_b1, last_b1, STL_is_upper);
                assert(num_a == num_b);
                break;
            }
            case TEST_COUNT_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                // used to fail with 0,0 of 0
                num_a = str_count_range(&range_a1, value);
                num_b = count(first_b1, last_b1, value);
                assert(num_a == num_b);
                break;
            }
            case TEST_ALL_OF: {
                found_a = str_all_of(&a, is_upper);
                found_b = all_of(b.begin(), b.end(), STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_ANY_OF: {
                found_a = str_any_of(&a, is_upper);
                found_b = any_of(b.begin(), b.end(), STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_NONE_OF: {
                found_a = str_none_of(&a, is_upper);
                found_b = none_of(b.begin(), b.end(), STL_is_upper);
                assert(found_a == found_b);
                break;
            }
            case TEST_COUNT_IF: {
                num_a = str_count_if(&a, is_upper);
                num_b = count_if(b.begin(), b.end(), STL_is_upper);
                assert(num_a == num_b);
                break;
            }
            case TEST_GENERATE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                str_generate_reset();
                str_generate_range(&range_a1, str_generate);
                str_generate_reset();
                std::generate(first_b1, last_b1, STR_generate);
                CHECK(a, b);
                break;
            }
            case TEST_TRANSFORM: {
                aa = str_transform(&a, str_untrans);
                bb.resize(b.size());
                std::transform(b.begin(), b.end(), bb.begin(), STR_untrans);
                CHECK(aa, bb);
                CHECK(a, b);
                str_free(&aa);
                break;
            }
            case TEST_TRANSFORM_IT: {
                it = str_it_begin(&a);
                str_it_advance(&it, 1);
                aa = str_transform_it(&a, &it, str_bintrans);
                LOG("\"%s\" (%zu)\n", str_c_str(&aa), aa.size);
#ifndef _MSC_VER
                bb.reserve(b.size() - 1);
                std::transform(b.begin(), b.end() - 1, b.begin() + 1, std::back_inserter(bb), STR_bintrans);
                LOG("\"%s\" (%zu)\n", bb.c_str(), bb.size());
                ADJUST_CAP("transform_it", aa, bb);
                CHECK(aa, bb);
#endif
                CHECK(a, b);
                str_free(&aa);
                break;
            }
            case TEST_UNION: // 49
            {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = str_union(&a, &aa);
#ifndef _MSC_VER
                std::set_union(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                LOG("STL b + bb => bbb\n");
                LOG("%s\n", b.c_str());
                LOG("%s\n", bb.c_str());
                LOG("=> %s\n", bbb.c_str());
                LOG("CTL a + aaa => aaa\n");
                ADJUST_CAP("union", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("union", aaa, bbb);
                LOG("%s\n", str_c_str(&a));
                LOG("%s\n", str_c_str(&aa));
                LOG("=> %s\n", str_c_str(&aaa));
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_INTERSECTION: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = str_intersection(&a, &aa);
#ifndef _MSC_VER
                std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                LOG("%s (%zu)\n", str_c_str(&a), a.size);
                LOG("%s (%zu)\n", str_c_str(&aa), aa.size);
                LOG("=> %s (%zu) vs %s (%zu)\n", str_c_str(&aaa), aaa.size, bbb.c_str(), bbb.size());
                ADJUST_CAP("intersection", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("intersection", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                aaa = str_symmetric_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                ADJUST_CAP("symmetric_difference", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_DIFFERENCE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                // LOG(&a);
                aaa = str_difference(&a, &aa);
#ifndef _MSC_VER
                std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                ADJUST_CAP("difference", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("difference", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_UNION_RANGE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                // LOG("CTL a + aa\n");
                // LOG_range(range_a1);
                // LOG_range(range_a2);
                aaa = str_union_range(&range_a1, &range_a2);
                // LOG("CTL => aaa\n");
                // LOG(&aaa);

                // LOG("STL b + bb\n");
                // LOG(b);
                // LOG(bb);
#ifndef _MSC_VER
                std::set_union(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                ADJUST_CAP("union_range", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("union_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_INTERSECTION_RANGE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                // LOG("CTL a - aa\n");
                // LOG_range(range_a1);
                // LOG_range(range_a2);
                aaa = str_intersection_range(&range_a1, &range_a2);
                // LOG("CTL => aaa (%zu)\n", aaa.size);
                // LOG("STL b - bb\n");
                // LOG(b);
                // LOG(bb);
#ifndef _MSC_VER
                std::set_intersection(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb (%zu)\n", bbb.size());
                ADJUST_CAP("intersection_range", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("intersection_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_DIFFERENCE_RANGE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                // LOG("CTL a + aa\n");
                // LOG_range(range_a1);
                // LOG_range(range_a2);
                aaa = str_difference_range(&range_a1, &range_a2);
                // LOG("CTL => aaa\n");
                // LOG(&aaa);
                // LOG("STL b + bb\n");
                // LOG(b);
                // LOG(bb);
#ifndef _MSC_VER
                std::set_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                ADJUST_CAP("difference_range", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_SYMMETRIC_DIFFERENCE_RANGE: {
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                // LOG("CTL a + aa\n");
                // LOG_range(range_a1);
                // LOG_range(range_a2);
                aaa = str_symmetric_difference_range(&range_a1, &range_a2);
                // LOG("CTL => aaa\n");
                // LOG(&aaa);

                // LOG("STL b + bb\n");
                // LOG(b);
                // LOG(bb);
#ifndef _MSC_VER
                std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("STL => bbb\n");
                ADJUST_CAP("symmetric_difference_range", aa, bb);
                CHECK(aa, bb);
                ADJUST_CAP("symmetric_difference_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aaa);
                str_free(&aa);
                break;
            }
            case TEST_IOTA: {
                str_iota(&a, 'a');
                LOG("%s\n", str_c_str(&a));
                std::iota(b.begin(), b.end(), 'a');
                LOG("%s\n", b.c_str());
                CHECK(a, b);
                break;
            }
            case TEST_IOTA_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                str_iota_range(&range_a1, 'a');
                LOG("%s\n", str_c_str(&a));
                LOG("\"%.*s\"\n", (int)(last_b1 - first_b1), range_a1.ref);
                std::iota(first_b1, last_b1, 'a');
                LOG("%s\n", b.c_str());
                CHECK(a, b);
                break;
            }
            case TEST_SHUFFLE: {
                LOG("%s\n", str_c_str(&a));
                str_shuffle(&a);
                LOG("%s\n", str_c_str(&a));
#ifndef NEED_RANDOM_ENGINE
                std::random_shuffle(b.begin(), b.end());
#else
                std::shuffle(b.begin(), b.end(), rng);
#endif
                LOG("%s\n", b.c_str());
                str_sort(&a);
                std::sort(b.begin(), b.end());
                CHECK(a, b);
                break;
            }
            case TEST_SHUFFLE_RANGE: {
                LOG("%s\n", str_c_str(&a));
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                str_shuffle_range(&range_a1);
                LOG("\"%.*s\"\n", (int)(last_b1 - first_b1), range_a1.ref);
#ifndef NEED_RANDOM_ENGINE
                std::random_shuffle(first_b1, last_b1);
#else
                std::shuffle(first_b1, last_b1, rng);
#endif
                // TODO check that the ranges before and after range are still
                // sorted, and untouched.
                LOG("%s\n", b.c_str());
                str_sort(&a);
                std::sort(b.begin(), b.end());
                CHECK(a, b);
                break;
            }
#ifdef DEBUG
            case TEST_TRANSFORM_RANGE: {
                if (a.size < 2)
                    break;
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = str_init(a.vector);
                it = str_it_begin(&aa);
                /*str_it it = */
                str_transform_range(&range_a1, it, str_untrans);
                bb.resize(last_b1 - first_b1);
                /*auto iter = */
                std::transform(first_b1, last_b1, b.begin() + 1, bb.begin(), STR_bintrans);
                ADJUST_CAP("transform_range", aa, bb);
                // CHECK_ITER(it, bb, iter);
                CHECK(aa, bb);
                CHECK(a, b);
                str_free(&aa);
                break;
            }
            case TEST_GENERATE_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t off = first_b1 - b.begin();
                size_t count = TEST_RAND(20 - off);
                str_generate_reset();
                str_generate_n_range(&range_a1, count, str_generate);
                str_generate_reset();
                std::generate_n(first_b1, count, STR_generate);
                CHECK(a, b);
                break;
            }
#endif // DEBUG
            case TEST_COPY_IF: {
                aa = str_copy_if(&a, is_upper);
#ifndef _MSC_VER // fails to compile
#if __cplusplus >= 201103L
                std::copy_if(b.begin(), b.end(), std::back_inserter(bb), STL_is_upper);
#else
                for (auto &d: b) {
                    if (DIGI_is_upper(d))
                        bb.push_back(d);
                }
#endif
                ADJUST_CAP("copy_if", aa, bb);
                CHECK(aa, bb);
#endif
                str_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_COPY_IF_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                aa = str_copy_if_range(&range_a1, is_upper);
#ifndef _MSC_VER // fails to compile
#if __cplusplus >= 201103L
                std::copy_if(first_b1, last_b1, std::back_inserter(bb), STL_is_upper);
#else
                for (auto d = first_b1; d != last_b1; d++) {
                    if (STL_is_upper(*d))
                        bb.push_back(*d);
                }
#endif
                ADJUST_CAP("copy_if_range", aa, bb);
                CHECK(aa, bb);
#endif
                str_free(&aa);
                CHECK(a, b);
                break;
            }
            case TEST_MISMATCH: // 40
            {
                if (a.size < 2)
                    break;
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_it b1, b2;
                b1 = str_it_begin(&a);
                b2 = str_it_begin(&aa);
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                /*bool found_a = */ str_mismatch(&range_a1, &range_a2);
#if __cpp_lib_robust_nonmodifying_seq_ops >= 201304L
                auto pair = std::mismatch(first_b1, last_b1, first_b2, last_b2);
#else
                if (!bb.size() || !distance(first_b2, last_b2))
                {
                    printf("skip std::mismatch with empty 2nd range. use C++14\n");
                    str_free(&aa);
                    break;
                }
                auto pair = std::mismatch(first_b1, last_b1, first_b2);
#endif
                int d1a = str_it_distance(&b1, &range_a1);
                int d2a = str_it_distance(&b2, &range_a2);
                LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                // TODO check found_a against iter results
                assert(d1a == distance(b.begin(), pair.first));
                assert(d2a == distance(bb.begin(), pair.second));
                str_free(&aa);
                break;
            }
            case TEST_SEARCH: // 52, using strstr
                aa = str_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a1, bb, first_b1, last_b1);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    const size_t i = first_b1 - bb.begin();
                    str_set(&aa, i, ' ');
                    bb[i] = ' ';
                }
                LOG("search \"%s\" in \"%s\" (%zu)\n", range_a1.ref, a.vector, a.size);
                // print_str_range(range_a1);
                it = str_search(&a, &range_a1);
                iter = search(b.begin(), b.end(), first_b1, last_b1);
                LOG("found a: %s\n", str_it_done(&it) ? "no" : "yes");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                CHECK_ITER(it, b, iter);
                str_free(&aa);
                break;
            case TEST_SEARCH_RANGE:
                aa = str_copy(&a);
                bb = b;
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);
                if (aa.size && TEST_RAND(2))
                { // 50% unsuccessful
                    size_t i = first_b2 - bb.begin();
                    str_set(&aa, i, ' ');
                    bb[i] = ' ';
                }
                LOG("search \"%s\" in \"%s\" (%zu)\n", range_a2.ref, a.vector, a.size);
                // print_str_range(needle);
                it = str_it_begin(&a);
                found_a = str_search_range(&it, &range_a2);
                iter = search(b.begin(), b.end(), first_b2, last_b2);
                LOG("found a: %s\n", found_a ? "yes" : "no");
                LOG("found b: %s\n", iter == b.end() ? "no" : "yes");
                assert(found_a == !str_it_done(&it));
                CHECK_ITER(it, b, iter);
                str_free(&aa);
                break;
            case TEST_SEARCH_N: {
                //print_str(&a);
                size_t count = TEST_RAND(4);
                LOG("search_n %zu %c\n", count, value);
                it = str_search_n(&a, count, value);
                iter = search_n(b.begin(), b.end(), count, value);
                CHECK_ITER(it, b, iter);
                LOG("found %s at %zu\n", str_it_done(&it) ? "no" : "yes",
                    str_it_index(&it));
                break;
            }
            case TEST_SEARCH_N_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                size_t count = TEST_RAND(4);
                LOG("search_n_range_a1 %zu %c\n", count, value);
                //print_str_range(&range_a1);
                pos = str_search_n_range(&range_a1, count, value);
                iter = search_n(first_b1, last_b1, count, value);
                CHECK_RANGE(*pos, iter, last_b1);
                LOG("found %s at %zu\n", str_it_done(pos) ? "no" : "yes",
                    str_it_index(pos));
                break;
            }
            case TEST_ADJACENT_FIND: {
                LOG("%s\n", str_c_str(&a));
                it = str_adjacent_find(&a);
                iter = adjacent_find(b.begin(), b.end());
                CHECK_ITER(it, b, iter);
                LOG("found %s\n", str_it_done(&it) ? "no" : "yes");
                break;
            }
            case TEST_ADJACENT_FIND_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                LOG("%s\n", str_c_str(&a));
                pos = str_adjacent_find_range(&range_a1);
                iter = adjacent_find(first_b1, last_b1);
                CHECK_ITER(*pos, b, iter);
                LOG("found %s\n", str_it_done(pos) ? "no" : "yes");
                break;
            }
#ifdef DEBUG
            case TEST_UNIQUE: {
                // print_str(&a);
                it = str_unique(&a);
                found_a = !str_it_done(&it);
                index = str_it_index(&it);
                // print_str(&a);
                // C++ is special here with its move hack
                iter = unique(b.begin(), b.end());
                found_b = iter != b.end();
                long dist = std::distance(b.begin(), iter);
                b.resize(dist);
                LOG("found %s at %zu of \"%s\" ", found_a ? "yes" : "no", index, a.vector);
                LOG("vs found %s at %ld of \"%s\"\n", found_b ? "yes" : "no", dist, b.c_str());
                // print_string(b);
                assert(found_a == found_b);
                assert((long)index == dist);
                break;
            }
            case TEST_UNIQUE_RANGE: {
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                LOG("\"%.*s\" of \"%s\"\n", (int)(range_a1.end - range_a1.ref), range_a1.ref, a.vector);
                it = str_unique_range(&range_a1);
                found_a = !str_it_done(&it);
                index = str_it_index(&it);
                iter = unique(first_b1, last_b1);
                found_b = iter != last_b1;
                long dist = std::distance(b.begin(), iter);
                if (found_b)
                    b.erase(iter, last_b1);
                LOG("found %s at %zu => \"%.*s\" ", found_a ? "yes" : "no", index, (int)(range_a1.end - range_a1.ref),
                    range_a1.ref);
                LOG("vs found %s at %ld => \"%.*s\"\n", found_b ? "yes" : "no", dist, (int)(last_b1 - first_b1),
                    &(*first_b1));
                assert(found_a == found_b);
                assert((long)index == dist);
                break;
            }
#endif // DEBUG
            case TEST_LOWER_BOUND: {
                str_sort(&a);
                std::sort(b.begin(), b.end());
                it = str_lower_bound(&a, value);
                iter = lower_bound(b.begin(), b.end(), value);
                if (iter != b.end())
                {
                    LOG("%c: %c vs %c\n", value, *it.ref, *iter);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_UPPER_BOUND: {
                str_sort(&a);
                std::sort(b.begin(), b.end());
                it = str_upper_bound(&a, value);
                iter = upper_bound(b.begin(), b.end(), value);
                if (iter != b.end())
                {
                    LOG("%c: %c vs %c\n", value, *it.ref, *iter);
                }
                CHECK_ITER(it, b, iter);
                break;
            }
            case TEST_LOWER_BOUND_RANGE:
                str_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                pos = str_lower_bound_range(&range_a1, value);
                iter = lower_bound(first_b1, last_b1, value);
                if (iter != last_b1)
                {
                    LOG("%c: %c vs %c\n", value, *pos->ref, *iter);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            case TEST_UPPER_BOUND_RANGE:
                str_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                pos = str_upper_bound_range(&range_a1, value);
                iter = upper_bound(first_b1, last_b1, value);
                if (iter != last_b1)
                {
                    LOG("%c: %c vs %c\n", value, *pos->ref, *iter);
                }
                CHECK_RANGE(*pos, iter, last_b1);
                break;
            case TEST_BINARY_SEARCH: // 73
                str_sort(&a);
                std::sort(b.begin(), b.end());
                found_a = str_binary_search(&a, value);
                found_b = binary_search(b.begin(), b.end(), value);
                LOG("%c: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            case TEST_BINARY_SEARCH_RANGE:
                str_sort(&a);
                std::sort(b.begin(), b.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                found_a = str_binary_search_range(&range_a1, value);
                found_b = binary_search(first_b1, last_b1, value);
                LOG("%c: %d vs %d\n", value, (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            case TEST_MERGE:
                //str_sort(&a);
                //std::sort(b.begin(), b.end());
                gen_strings(&aa, bb, TEST_RAND(a.size));
                //str_sort(&aa);
                //std::sort(bb.begin(), bb.end());

                aaa = str_merge(&a, &aa);
# ifndef _MSC_VER
                std::merge(b.begin(), b.end(), bb.begin(), bb.end(), std::back_inserter(bbb));
                LOG("merge \"%s\", \"%s\" => \"%s\" (%zu)\n", a.vector, aa.vector, aaa.vector, aaa.size);
                LOG("vs    \"%s\", \"%s\" => \"%s\" (%zu)\n", b.c_str(), bb.c_str(), bbb.c_str(), bbb.size());
                ADJUST_CAP("merge", aaa, bbb);
                CHECK(aaa, bbb);
# endif
                str_free(&aa);
                str_free(&aaa);
                break;
            case TEST_MERGE_RANGE:
                str_sort(&a);
                std::sort(b.begin(), b.end());
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&aa);
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                aaa = str_merge_range(&range_a1, &range_a2);
#ifndef _MSC_VER
                std::merge(first_b1, last_b1, first_b2, last_b2, std::back_inserter(bbb));
                LOG("merge_range \"%.*s\", \"%.*s\" => \"%s\" (%zu)\n", (int)(range_a1.end - range_a1.ref),
                    range_a1.ref, (int)(range_a2.end - range_a2.ref), range_a2.ref, aaa.vector, aaa.size);
                LOG("vs          \"%.*s\", \"%.*s\" => \"%s\" (%zu)\n", (int)(last_b1 - first_b1), &(*first_b1),
                    (int)(last_b2 - first_b2), &(*first_b2), bbb.c_str(), bbb.size());
                ADJUST_CAP("merge_range", aaa, bbb);
                CHECK(aaa, bbb);
#endif
                str_free(&aa);
                str_free(&aaa);
                break;
            case TEST_INCLUDES:
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                found_a = str_includes(&a, &aa);
                found_b = std::includes(b.begin(), b.end(), bb.begin(), bb.end());
                LOG("includes \"%.*s\", \"%.*s\" => %d\n", (int)a.size, a.vector, (int)aa.size, aa.vector, (int)found_a);
                LOG("vs       \"%.*s\", \"%.*s\" => %d\n", (int)b.size(), b.c_str(), (int)bb.size(), bb.c_str(),
                    (int)found_b);
                assert(found_a == found_b);
                CHECK(aa, bb);
                str_free(&aa);
                break;
            case TEST_INCLUDES_RANGE:
                gen_strings(&aa, bb, TEST_RAND(a.size));
                str_sort(&a);
                str_sort(&aa);
                std::sort(b.begin(), b.end());
                std::sort(bb.begin(), bb.end());
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                get_random_iters(&aa, &range_a2, bb, first_b2, last_b2);

                found_a = str_includes_range(&range_a1, &range_a2);
                found_b = std::includes(first_b1, last_b1, first_b2, last_b2);
                LOG("includes_range   \"%.*s\", \"%.*s\" => %d\n", (int)(range_a1.end - range_a1.ref),
                    range_a1.ref, (int)(range_a2.end - range_a2.ref), range_a2.ref, (int)found_a);
                LOG("vs std::includes \"%.*s\", \"%.*s\" => %d\n", (int)(last_b1 - first_b1), &(*first_b1),
                    (int)(last_b2 - first_b2), &(*first_b2), (int)found_b);
                assert(found_a == found_b);
                CHECK(aa, bb);
                str_free(&aa);
                break;
            case TEST_IS_SORTED:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                //print_str_range(range_a1);
                found_a = str_is_sorted(&range_a1);
                found_b = std::is_sorted(first_b1, last_b1);
                LOG("a_yes: %d b_yes %d\n", (int)found_a, (int)found_b);
                assert(found_a == found_b);
                break;
            case TEST_IS_SORTED_UNTIL:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                //print_str_range(range_a1);
                range_a2 = range_a1;
                range_a2.ref = range_a1.end;
                pos = str_is_sorted_until(&range_a1, &range_a2);
                first_b1 = std::is_sorted_until(first_b1, last_b1);
                LOG("=> %s/%s, %ld/%ld: %c/%c\n", !str_it_done(pos) ? "yes" : "no", first_b1 != last_b1 ? "yes" : "no",
                    str_it_index(pos), distance(b.begin(), first_b1), !str_it_done(pos) ? *pos->ref : -1,
                    first_b1 != last_b1 ? *first_b1 : -1);
                CHECK_RANGE(*pos, first_b1, last_b1);
                break;
            case TEST_REVERSE:
                LOG("%s\n", a.vector);
                str_reverse(&a);
                std::reverse(b.begin(), b.end());
                LOG("%s\n", a.vector);
                CHECK(a, b);
                break;
            case TEST_REVERSE_RANGE:
                get_random_iters(&a, &range_a1, b, first_b1, last_b1);
                LOG("%s\n", a.vector);
                str_reverse_range(&range_a1);
                std::reverse(first_b1, last_b1);
                LOG("%s\n", a.vector);
                CHECK(a, b);
                break;

            default:
#ifdef DEBUG
                printf("unhandled testcase %d %s\n", which, test_names[which]);
#else
                printf("unhandled testcase %d\n", which);
#endif
                break;
            }
            CHECK(a, b);
            str_free(&a);
            free(base);
        }
    }
    FINISH_TEST(__FILE__);
}

#endif // C++11
