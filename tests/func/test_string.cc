#include "../test.h"
#if __cplusplus < 201103L
#pragma warning "Can only test against C++11 compilers"
OLD_MAIN
#else

#include <ctl/string.h>

#include <string>
#include <algorithm>

#define MIN_STR_SIZE  (30) // NO SUPPORT FOR SMALL STRINGS yet
#define ALPHA_LETTERS (23)

// mark functions which need 16 align
#define LOG_CAP(a,b) \
    LOG("ctl capacity %zu (0x%lx) vs %zu (0x%lx) %s\n", \
        a.capacity, a.capacity,                         \
        b.capacity(), b.capacity(), a.capacity == b.capacity() ? "" : "FAIL")

// tested variants
#if (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L && _GLIBCXX_RELEASE < 11)
// Tested ok with g++ 10, g++ 7.5,
// clang 10 (libc++ 11-18), apple clang 12 fail
# define ASSERT_EQUAL_CAP(c, s) assert(s.capacity() == c.capacity);
#else
// other llvm libc++ fail (gh actions), msvc also.
# define ASSERT_EQUAL_CAP(c, s) if (s.capacity() != c.capacity) \
    { printf("capacity %zu vs %zu FAIL\n", c.capacity, s.capacity()); fail++; }
#endif

// cheat growth
#define ADJUST_CAP(m, c, s)                                             \
    if (c.size == s.size() && c.capacity != s.capacity())               \
    {                                                                   \
        printf("%s capacity %zu => %zu FAIL\n", m, c.capacity, s.capacity()); \
        str_fit(&c, s.capacity());                                      \
    }

#define CHECK(_x, _y) {                              \
    assert(strlen(str_c_str(&_x)) == strlen(_y.c_str())); \
    assert(strcmp(str_c_str(&_x), _y.c_str()) == 0); \
    ASSERT_EQUAL_CAP(_x, _y);                        \
    assert(_x.size == _y.size());                    \
    assert(str_empty(&_x) == _y.empty());            \
    if(_x.size > 0) {                                \
        assert(_y.front() == *str_front(&_x));       \
        assert(_y.back() == *str_back(&_x));         \
    }                                                \
    std::string::iterator _iter = _y.begin();        \
    str_foreach(&_x, _ref) {                         \
        assert(*_ref == *_iter);                     \
        _iter++;                                     \
    }                                                \
    char* _it = str_begin(&_x);                      \
    for(auto& _d : _y) {                             \
        assert(*_it == _d);                          \
        _it++;                                       \
    }                                                \
    for(size_t i = 0; i < _y.size(); i++)            \
        assert(_y.at(i) == *str_at(&_x, i));         \
}

#define CHECK_ITER(aa,b,bb)                          \
    if (aa.ref != &aa.container->vector[aa.container->size]) \
    {                                                \
        assert (bb != b.end());                      \
        assert(*aa.ref == *bb);                      \
    } else                                           \
        assert (bb == b.end())

#define RAND_CHAR   ('0' + TEST_RAND('z' - '0'))
#define RAND_ALPHA  ((TEST_RAND(2) ? 'a' : 'A') + TEST_RAND(ALPHA_LETTERS))

static char*
create_test_string(size_t size)
{
    char* temp = (char*) malloc(size + 1);
    for(size_t i = 0; i < size; i++)
    {
        temp[i] = RAND_ALPHA;
    }
    temp[size] = '\0';
    return temp;
}

static int
char_compare(char* a, char* b)
{
    return *a < *b;
}

int is_upper(char* a) {
    return *a >= 'A' && *a <= 'Z';
}

int STL_is_upper(const char &a) {
    return a >= 'A' && a <= 'Z';
}

static int _generator_state = 0;
void str_generate_reset () {
    _generator_state = 0;
}
char str_generate (void) {
    _generator_state++;
    return '0' + (_generator_state % ('z' - '0'));
}
char STR_generate (void) {
    _generator_state++;
    return '0' + (_generator_state % ('z' - '0'));
}
char str_untrans (char* s) {
    return *s + 1;
}
char STR_untrans (const char& s) {
    return s + 1;
}
char str_bintrans (char* s1, char* s2) {
    return *s1 ^ *s2;
}
char STR_bintrans (const char& s1, const char& s2) {
    return s1 ^ s2;
}

static void
gen_strings(str* a, std::string& b, size_t size)
{
    char* _ta = create_test_string(size);
    *a = str_init(_ta);
    b = _ta;
    free (_ta);
}

static void
get_random_iters (str *a, str_it* first_a, str_it* last_a,
                  std::string& b, std::string::iterator &first_b,
                  std::string::iterator &last_b)
{
    size_t r1 = TEST_RAND(a->size / 2);
    const size_t rnd = TEST_RAND(a->size / 2);
    size_t r2 = MIN(r1 + rnd, a->size);
    LOG("iters %zu, %zu of %zu\n", r1, r2, a->size);
    if (a->size)
    {
        str_it it1 = str_it_begin(a);
        first_b = b.begin();
        str_it_advance(&it1, r1);
        first_b += r1;
        *first_a = it1;

        if (r1 == r2)
        {
            *last_a = it1;
            last_b = first_b;
        }
        else if (r2 == a->size)
        {
            *last_a = str_it_end(a);
            last_b = b.end();
        }
        else
        {
            str_it it2 = str_it_begin(a);
            last_b = b.begin();
            str_it_advance(&it2, r2);
            last_b += r2;
            *last_a = it2;
        }
    }
    else
    {
        str_it end = str_it_end(a);
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
        size_t str_size = TEST_RAND(TEST_MAX_SIZE);
        if(str_size < MIN_STR_SIZE)
            str_size = MIN_STR_SIZE;
#if defined(DEBUG) && !defined(LONG)
        //str_size = 2; short strings for certain methods
#endif
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            char* base = create_test_string(str_size);
            str a;
            std::string b;
            if(mode == MODE_DIRECT)
            {
                LOG("mode DIRECT\n");
                a = str_init(base);
                b = base;
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
                a = str_init("");
                for(size_t i = 0; i < str_size; i++)
                {
                    str_push_back(&a, base[i]);
                    b.push_back(base[i]);
                }
            }
            a.compare = char_compare;

#define FOREACH_METH(TEST) \
            TEST(PUSH_BACK) \
            TEST(POP_BACK) \
            TEST(APPEND) \
            TEST(C_STR) \
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
            TEST(INSERT_INDEX) \
            TEST(ASSIGN) \
            TEST(REPLACE) \
            TEST(FIND) \
            TEST(RFIND) \
            TEST(FIND_FIRST_OF) \
            TEST(FIND_LAST_OF) \
            TEST(FIND_FIRST_NOT_OF) \
            TEST(FIND_LAST_NOT_OF) \
            TEST(SUBSTR) \
            TEST(COMPARE) \
            TEST(COUNT) \
            TEST(COUNT_IF) \
            TEST(ALL_OF) \
            TEST(ANY_OF) \
            TEST(NONE_OF) \
            TEST(FIND_RANGE) \
            TEST(FIND_IF_RANGE) \
            TEST(FIND_IF_NOT_RANGE) \
            TEST(ALL_OF_RANGE) \
            TEST(ANY_OF_RANGE) \
            TEST(NONE_OF_RANGE) \
            TEST(COUNT_IF_RANGE) \
            TEST(COUNT_RANGE) \
            TEST(MISMATCH) \
            TEST(UNION) \
            TEST(DIFFERENCE) \
            TEST(SYMMETRIC_DIFFERENCE) \
            TEST(GENERATE) \
            TEST(GENERATE_RANGE) \
            TEST(GENERATE_N) \
            TEST(TRANSFORM) \
            TEST(TRANSFORM_IT) \

#define FOREACH_DEBUG(TEST) \
            TEST(INSERT_COUNT) /* 47 */ \
            TEST(INSERT_RANGE) \
            TEST(EQUAL_RANGE) \
            TEST(INTERSECTION) \
            TEST(UNION_RANGE) \
            TEST(DIFFERENCE_RANGE) \
            TEST(SYMMETRIC_DIFFERENCE_RANGE) \
            TEST(INTERSECTION_RANGE) \
            TEST(GENERATE_N_RANGE) \
            TEST(TRANSFORM_RANGE) \
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
            LOG ("TEST=%d %s (size %zu, cap %zu)\n", which, test_names[which], a.size, a.capacity);
            switch(which)
            {
                case TEST_PUSH_BACK:
                {
                    const char value = TEST_RAND(ALPHA_LETTERS);
                    b.push_back(value);
                    str_push_back(&a, value);
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_POP_BACK:
                {
                    if(a.size > 0)
                    {
                        b.pop_back();
                        str_pop_back(&a);
                    }
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_APPEND:
                {
                    char* temp = create_test_string(TEST_RAND(256));
                    str_append(&a, temp);
                    b.append(temp);
                    free(temp);
                    break;
                }
                case TEST_C_STR:
                {
                    assert(strlen(str_c_str(&a))); // strlen(NULL) is valid
                    assert(str_c_str(&a) == str_data(&a));
                    LOG("CTL C_STR %zu %zu\n", a.size, a.capacity);
                    break;
                }
                case TEST_REPLACE:
                {
                    char* temp = create_test_string(TEST_RAND(a.size));
                    const size_t index = TEST_RAND(a.size);
                    const size_t size = TEST_RAND(a.size);
                    str_replace(&a, index, size, temp);
                    b.replace(index, size, temp);
                    free(temp);
                    break;
                }
                case TEST_FIND:
                {
                    const size_t size = TEST_RAND(3);
                    char* temp = create_test_string(size);
                    assert(str_find(&a, temp) == b.find(temp));
                    free(temp);
                    break;
                }
                case TEST_RFIND:
                {
                    char* temp = create_test_string(TEST_RAND(3));
                    assert(str_rfind(&a, temp) == b.rfind(temp));
                    free(temp);
                    break;
                }
                case TEST_FIND_FIRST_OF:
                {
                    const size_t size = TEST_RAND(3);
                    char* temp = create_test_string(size);
                    assert(str_find_first_of(&a, temp) == b.find_first_of(temp));
                    free(temp);
                    break;
                }
                case TEST_FIND_LAST_OF:
                {
                    const size_t size = TEST_RAND(3);
                    char* temp = create_test_string(size);
                    assert(str_find_last_of(&a, temp) == b.find_last_of(temp));
                    free(temp);
                    break;
                }
                case TEST_FIND_FIRST_NOT_OF:
                {
                    const size_t size = TEST_RAND(192);
                    char* temp = create_test_string(size);
                    assert(str_find_first_not_of(&a, temp) == b.find_first_not_of(temp));
                    free(temp);
                    break;
                }
                case TEST_FIND_LAST_NOT_OF:
                {
                    const size_t size = TEST_RAND(192);
                    char* temp = create_test_string(size);
                    assert(str_find_last_not_of(&a, temp) == b.find_last_not_of(temp));
                    free(temp);
                    break;
                }
                case TEST_SUBSTR:
                {
                    const size_t index = TEST_RAND(a.size);
                    const size_t size = TEST_RAND(a.size - index);
                    if(size > MIN_STR_SIZE)
                    {
                        str substr1 = str_substr(&a, index, size);
                        std::string substr2 = b.substr(index, size);
                        CHECK(substr1, substr2);
                        str_free(&substr1);
                    }
                    break;
                }
                case TEST_COMPARE:
                {
                    size_t size = TEST_RAND(512);
                    char* _ta = create_test_string(size);
                    char* _tb = create_test_string(size);
                    str _a = str_init(_ta);
                    str _b = str_init(_tb);
                    std::string _aa = _ta;
                    std::string _bb = _tb;
                    assert(TEST_SIGN(str_compare(&_a, _tb)) == TEST_SIGN(_aa.compare(_tb)));
                    assert(TEST_SIGN(str_compare(&_b, _ta)) == TEST_SIGN(_bb.compare(_ta)));
                    assert(TEST_SIGN(str_compare(&_a, _ta)) == TEST_SIGN(_aa.compare(_ta)));
                    assert(TEST_SIGN(str_compare(&_b, _tb)) == TEST_SIGN(_bb.compare(_tb)));
                    str_free(&_a);
                    str_free(&_b);
                    free(_ta);
                    free(_tb);
                    break;
                }
                case TEST_CLEAR:
                {
                    str_clear(&a);
                    b.clear();
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_ERASE:
                {
                    const size_t index = TEST_RAND(a.size - 1);
                    b.erase(b.begin() + index);
                    str_it it = str_it_iter(&a, index);
                    str_erase(&it);
                    break;
                }
                case TEST_ERASE_INDEX:
                {
                    const size_t index = TEST_RAND(a.size - 1);
                    b.erase(b.begin() + index);
                    str_erase_index(&a, index);
                    break;
                }
                case TEST_INSERT_INDEX:
                {
                    size_t letters = TEST_RAND(512);
                    for(size_t count = 0; count < letters; count++)
                    {
                        const char value = RAND_ALPHA;
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        str_insert_index(&a, index, value);
                    }
                    break;
                }
                case TEST_INSERT:
                {
                    size_t letters = TEST_RAND(512);
                    for(size_t count = 0; count < letters; count++)
                    {
                        const char value = RAND_ALPHA;
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        str_it pos = str_it_begin(&a);
                        str_it_advance(&pos, index);
                        str_insert(&pos, value);
                    }
                    break;
                }
                case TEST_RESIZE:
                {
                    const size_t resize = 3 * TEST_RAND(a.size);
                    b.resize(resize);
                    str_resize(&a, resize, '\0');
                    LOG("CTL resize by %zu %zu %zu\n", resize, a.size, a.capacity);
                    LOG("STL resize by %zu %zu %zu\n", resize, b.size(), b.capacity());
                    break;
                }
                case TEST_RESERVE:
                {
                    const size_t capacity = 3 * TEST_RAND(a.capacity);
                    b.reserve(capacity);
                    str_reserve(&a, capacity);
                    LOG("CTL reserve by %zu %zu\n", a.capacity, a.capacity);
                    LOG("STL reserve by %zu %zu\n", capacity, b.capacity());
                    break;
                }
                case TEST_SHRINK_TO_FIT:
                {
                    b.shrink_to_fit();
                    str_shrink_to_fit(&a);
                    LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                    LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_SORT:
                {
                    LOG("before sort \"%s\"\n", str_c_str(&a));
                    str_sort(&a);
                    LOG("after  sort \"%s\"\n", str_c_str(&a));
                    std::sort(b.begin(), b.end());
                    LOG("STL    sort \"%s\"\n", b.c_str());
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_COPY:
                {
                    str ca = str_copy(&a);
                    std::string cb = b;
                    LOG("copy  a: \"%s\": %zu\n", str_c_str(&a), a.capacity);
                    LOG("copy ca: \"%s\": %zu\n", str_c_str(&ca), ca.capacity);
                    CHECK(ca, cb);
                    str_free(&ca);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const char value = RAND_ALPHA;
                    size_t assign_size = TEST_RAND(a.size);
                    str_assign(&a, assign_size, value);
                    b.assign(assign_size, value);
                    break;
                }
                case TEST_SWAP:
                {
                    str aa = str_copy(&a);
                    str aaa = str_init("");
                    std::string cb = b;
                    std::string bbb;
                    str_swap(&aaa, &aa);
                    std::swap(cb, bbb);
                    LOG_CAP(aaa, bbb);
                    CHECK(aaa, bbb);
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_COUNT:
                {
                    const char value = RAND_ALPHA;
                    assert(count(b.begin(), b.end(), value) == str_count(&a, value));
                    break;
                }
                case TEST_GENERATE:
                {
                    str_generate_reset();
                    str_generate(&a, str_generate);
                    str_generate_reset();
                    std::generate(b.begin(), b.end(), STR_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_GENERATE_N:
                {
                    size_t count = TEST_RAND(20);
                    str_generate_reset();
                    str_generate_n(&a, count, str_generate);
                    str_generate_reset();
                    std::generate_n(b.begin(), count, STR_generate);
                    CHECK(a, b);
                    break;
                }
                // wrong range end condition. ref == last is already too late.
                case TEST_FIND_RANGE:
                {
                    const char c = RAND_CHAR;
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = str_find_range(&first_a, &last_a, c);
                    auto bb = std::find(first_b, last_b, c);
                    CHECK_ITER(first_a, b, bb);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_IF_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = str_find_if_range(&first_a, &last_a, is_upper);
                    auto bb = std::find_if(first_b, last_b, STL_is_upper);
                    CHECK_ITER(first_a, b, bb);
                    break;
                }
                case TEST_FIND_IF_NOT_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    first_a = str_find_if_not_range(&first_a, &last_a, is_upper);
                    auto bb = std::find_if_not(first_b, last_b, STL_is_upper);
                    CHECK_ITER(first_a, b, bb);
                    break;
                }
                case TEST_ALL_OF_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = str_all_of_range(&first_a, &last_a, is_upper);
                    bool bb = std::all_of(first_b, last_b, STL_is_upper);
                    assert(aa == bb);
                    break;
                }
                case TEST_ANY_OF_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = str_any_of_range(&first_a, &last_a, is_upper);
                    bool bb = std::any_of(first_b, last_b, STL_is_upper);
                    assert(aa == bb);
                    break;
                }
                case TEST_NONE_OF_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    bool aa = str_none_of_range(&first_a, &last_a, is_upper);
                    bool bb = std::none_of(first_b, last_b, STL_is_upper);
                    assert(aa == bb);
                    break;
                }
                case TEST_COUNT_IF_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t numa = str_count_if_range(&first_a, &last_a, is_upper);
                    size_t numb = std::count_if(first_b, last_b, STL_is_upper);
                    assert(numa == numb); //fails. off by one, counts one too much
                    break;
                }
                case TEST_COUNT_RANGE:
                {
                    char c = RAND_CHAR;
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    // used to fail with 0,0 of 0
                    size_t numa = str_count_range(&first_a, &last_a, c);
                    size_t numb = count(first_b, last_b, c);
                    assert(numa == numb);
                    break;
                }
                case TEST_ALL_OF:
                {
                    bool is_a = str_all_of(&a, is_upper);
                    bool is_b = all_of(b.begin(), b.end(), STL_is_upper);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_ANY_OF:
                {
                    bool is_a = str_any_of(&a, is_upper);
                    bool is_b = any_of(b.begin(), b.end(), STL_is_upper);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_NONE_OF:
                {
                    bool is_a = str_none_of(&a, is_upper);
                    bool is_b = none_of(b.begin(), b.end(), STL_is_upper);
                    assert(is_a == is_b);
                    break;
                }
                case TEST_COUNT_IF:
                {
                    size_t count_a = str_count_if(&a, is_upper);
                    size_t count_b = count_if(b.begin(), b.end(), STL_is_upper);
                    assert(count_a == count_b);
                    break;
                }
                case TEST_GENERATE_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    str_generate_reset();
                    str_generate_range(&first_a, &last_a, str_generate);
                    str_generate_reset();
                    std::generate(first_b, last_b, STR_generate);
                    CHECK(a, b);
                    break;
                }
                case TEST_TRANSFORM:
                {
                    str aa = str_transform(&a, str_untrans);
                    std::string bb;
                    bb.resize(b.size());
                    std::transform(b.begin(), b.end(), bb.begin(), STR_untrans);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    str_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_IT:
                {
                    str_it pos = str_it_begin(&a);
                    str_it_advance(&pos, 1);
                    str aa = str_transform_it(&a, &pos, str_bintrans);
                    LOG("\"%s\" (%zu)\n", str_c_str(&aa), aa.size);
# ifndef _MSC_VER
                    std::string bb;
                    bb.reserve(b.size()-1);
                    std::transform(b.begin(), b.end()-1, b.begin()+1, std::back_inserter(bb),
                                   STR_bintrans);
                    LOG("\"%s\" (%zu)\n", bb.c_str(), bb.size());
                    ADJUST_CAP("transform_it", aa, bb);
                    CHECK(aa, bb);
# endif
                    CHECK(a, b);
                    str_free(&aa);
                    break;
                }
                case TEST_UNION: // 49
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str aaa = str_union(&a, &aa);
# ifndef _MSC_VER
                    std::string bbb;
                    std::set_union(b.begin(), b.end(), bb.begin(), bb.end(),
                                   std::back_inserter(bbb));
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
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
#ifdef DEBUG
                case TEST_INTERSECTION:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str aaa = str_intersection(&a, &aa);
# ifndef _MSC_VER
                    std::string bbb;
                    std::set_intersection(b.begin(), b.end(), bb.begin(), bb.end(),
                                          std::back_inserter(bbb));
                    ADJUST_CAP("intersection", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    //LOG(&a);
                    //LOG(&aa);
                    //LOG(&aaa);
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
#endif // DEBUG
                case TEST_SYMMETRIC_DIFFERENCE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str aaa = str_symmetric_difference(&a, &aa);
# ifndef _MSC_VER
                    std::string bbb;
                    std::set_symmetric_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                                  std::back_inserter(bbb));
                    ADJUST_CAP("symmetric_difference", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    //LOG(&a);
                    str aaa = str_difference(&a, &aa);
# ifndef _MSC_VER
                    std::string bbb;
                    std::set_difference(b.begin(), b.end(), bb.begin(), bb.end(),
                                        std::back_inserter(bbb));
                    ADJUST_CAP("difference", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("difference", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
#ifdef DEBUG
                case TEST_UNION_RANGE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str_it first_a1, last_a1;
                    std::string::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    str_it first_a2, last_a2;
                    std::string::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    //LOG_range(first_a1);
                    //LOG_range(first_a2);
                    str aaa = str_union_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    //LOG(&aaa);

                    std::string bbb;
                    LOG("STL b + bb\n");
                    //LOG(b);
                    //LOG(bb);
# ifndef _MSC_VER
                    std::set_union(first_b1, last_b1, first_b2, last_b2,
                                   std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    ADJUST_CAP("union_range", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("union_range", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_INTERSECTION_RANGE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str_it first_a1, last_a1;
                    std::string::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    str_it first_a2, last_a2;
                    std::string::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    //LOG_range(first_a1);
                    //LOG_range(first_a2);
                    str aaa = str_intersection_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    //LOG(&aaa);

                    std::string bbb;
                    LOG("STL b + bb\n");
                    //LOG(b);
                    //LOG(bb);
# ifndef _MSC_VER
                    std::set_intersection(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    ADJUST_CAP("intersection_range", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("intersection_range", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_DIFFERENCE_RANGE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str_it first_a1, last_a1;
                    std::string::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    str_it first_a2, last_a2;
                    std::string::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    //LOG_range(first_a1);
                    //LOG_range(first_a2);
                    str aaa = str_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    //LOG(&aaa);

                    std::string bbb;
                    LOG("STL b + bb\n");
                    //LOG(b);
                    //LOG(bb);
# ifndef _MSC_VER
                    std::set_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    ADJUST_CAP("difference_range", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("difference_range", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_SYMMETRIC_DIFFERENCE_RANGE:
                {
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_sort(&a);
                    str_sort(&aa);
                    std::sort(b.begin(), b.end());
                    std::sort(bb.begin(), bb.end());
                    str_it first_a1, last_a1;
                    std::string::iterator first_b1, last_b1;
                    get_random_iters (&a, &first_a1, &last_a1, b, first_b1, last_b1);
                    str_it first_a2, last_a2;
                    std::string::iterator first_b2, last_b2;
                    get_random_iters (&aa, &first_a2, &last_a2, bb, first_b2, last_b2);

                    LOG("CTL a + aa\n");
                    //LOG_range(first_a1);
                    //LOG_range(first_a2);
                    str aaa = str_symmetric_difference_range(&first_a1, &first_a2);
                    LOG("CTL => aaa\n");
                    //LOG(&aaa);

                    std::string bbb;
                    LOG("STL b + bb\n");
                    //LOG(b);
                    //LOG(bb);
# ifndef _MSC_VER
                    std::set_symmetric_difference(first_b1, last_b1, first_b2, last_b2,
                                          std::back_inserter(bbb));
                    LOG("STL => bbb\n");
                    ADJUST_CAP("symmetric_difference_range", aa, bb);
                    CHECK(aa, bb);
                    ADJUST_CAP("symmetric_difference_range", aaa, bbb);
                    CHECK(aaa, bbb);
# endif
                    str_free(&aaa);
                    str_free(&aa);
                    break;
                }
                case TEST_TRANSFORM_RANGE:
                {
                    if (a.size < 2)
                        break;
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    str aa = str_init(a.vector);
                    str_it dest = str_it_begin(&aa);
                    /*str_it it = */
                    str_transform_range(&first_a, &last_a, dest, str_untrans);
                    std::string bb;
                    bb.resize(last_b - first_b);
                    /*auto iter = */
                    std::transform(first_b, last_b, b.begin()+1, bb.begin(),
                                   STR_bintrans);
                    ADJUST_CAP("transform_range", aa, bb);
                    //CHECK_ITER(it, bb, iter);
                    CHECK(aa, bb);
                    CHECK(a, b);
                    str_free(&aa);
                    break;
                }
                case TEST_GENERATE_N_RANGE:
                {
                    str_it first_a, last_a;
                    std::string::iterator first_b, last_b;
                    get_random_iters (&a, &first_a, &last_a, b, first_b, last_b);
                    size_t off = first_b - b.begin();
                    size_t count = TEST_RAND(20 - off);
                    str_generate_reset();
                    str_generate_n_range(&first_a, count, str_generate);
                    str_generate_reset();
                    std::generate_n(first_b, count, STR_generate);
                    CHECK(a, b);
                    break;
                }
#endif // DEBUG
                case TEST_MISMATCH: // 38
                {
                    if(a.size < 2)
                        break;
                    str aa;
                    std::string bb;
                    gen_strings(&aa, bb, TEST_RAND(a.size));
                    str_it b1, b2;
                    b1 = str_it_begin(&a);
                    b2 = str_it_begin(&aa);
                    str_it r1a, last1_a, r2a, last2_a;
                    std::string::iterator r1b, last1_b, r2b, last2_b;
                    get_random_iters (&a, &r1a, &last1_a, b, r1b, last1_b);
                    get_random_iters (&aa, &r2a, &last2_a, bb, r2b, last2_b);
                    /*bool found_a = */str_mismatch(&r1a, &r2a);
                    auto pair = std::mismatch(r1b, last1_b, r2b, last2_b);
                    int d1a = str_it_distance(&b1, &r1a);
                    int d2a = str_it_distance(&b2, &r2a);
                    LOG("iter1 %d, iter2 %d\n", d1a, d2a);
                    //TODO check found_a against iter results
                    assert(d1a == distance(b.begin(), pair.first));
                    assert(d2a == distance(bb.begin(), pair.second));
                    str_free(&aa);
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
            str_free(&a);
            free(base);
        }
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}

#endif // C++11
