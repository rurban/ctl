#include "../test.h"

#include <ctl/string.h>
//#include "digi.hh"

#include <string>
#include <algorithm>

#define MIN_STR_SIZE  (30) // NO SUPPORT FOR SMALL STRINGS yet
#define ALPHA_LETTERS (23)

// mark functions which need 16 align
#define LOG_CAP(a,b) \
    LOG("ctl capacity %zu (0x%lx) vs %zu (0x%lx)\n", a.capacity, a.capacity, \
        b.capacity(), b.capacity())

#define CHECK(_x, _y) {                              \
    assert(strlen(str_c_str(&_x)) == strlen(_y.c_str())); \
    assert(strcmp(str_c_str(&_x), _y.c_str()) == 0); \
    assert(_x.capacity == _y.capacity());            \
    assert(_x.size == _y.size());                    \
    assert(str_empty(&_x) == _y.empty());            \
    if(_x.size > 0) {                                \
        assert(_y.front() == *str_front(&_x));       \
        assert(_y.back() == *str_back(&_x));         \
    }                                                \
    std::string::iterator _iter = _y.begin();        \
    foreach(str, &_x, _it) {                         \
        assert(*_it.ref == *_iter);                  \
        _iter++;                                     \
    }                                                \
    str_it _it = str_it_each(&_x);                   \
    for(auto& _d : _y) {                             \
        assert(*_it.ref == _d);                      \
        _it.step(&_it);                              \
    }                                                \
    for(size_t i = 0; i < _y.size(); i++)            \
        assert(_y.at(i) == *str_at(&_x, i));         \
}

static char*
create_test_string(size_t size)
{
    char* temp = (char*) malloc(size + 1);
    for(size_t i = 0; i < size; i++)
    {
        const int r = TEST_RAND(ALPHA_LETTERS);
        temp[i] = (TEST_RAND(2) ? 'a' : 'A') + r;
    }
    temp[size] = '\0';
    return temp;
}

static int
char_compare(char* a, char* b)
{
    return *a > *b;
}

int
main(void)
{
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
            TEST(RESIZE) \
            TEST(RESERVE) \
            TEST(SHRINK_TO_FIT) \
            TEST(SORT) \
            TEST(COPY) \
            TEST(SWAP) \
            TEST(INSERT) \
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
            TEST(COUNT)

#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

            enum {
                FOREACH_METH(GENERATE_ENUM)
                TEST_TOTAL
            };
#ifdef DEBUG
            static const char *test_names[] = {
                FOREACH_METH(GENERATE_NAME)
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
                    const size_t index = TEST_RAND(a.size);
                    b.erase(b.begin() + index);
                    str_erase(&a, index);
                    break;
                }
                case TEST_INSERT:
                {
                    size_t letters = TEST_RAND(512);
                    for(size_t count = 0; count < letters; count++)
                    {
                        const char value = TEST_RAND(ALPHA_LETTERS);
                        const size_t index = TEST_RAND(a.size);
                        b.insert(b.begin() + index, value);
                        str_insert(&a, index, value);
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
                    LOG("before sort \"%s\"\n", a.value);
                    str_sort(&a);
                    LOG("after  sort \"%s\"\n", a.value);
                    std::sort(b.begin(), b.end());
                    LOG("STL    sort \"%s\"\n", b.c_str());
                    LOG_CAP(a,b);
                    break;
                }
                case TEST_COPY:
                {
                    str ca = str_copy(&a);
                    std::string cb = b;
                    LOG("copy  a: \"%s\": %zu\n", a.value, a.capacity);
                    LOG("copy ca: \"%s\": %zu\n", ca.value, ca.capacity);
                    CHECK(ca, cb);
                    str_free(&ca);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const char value = TEST_RAND(ALPHA_LETTERS);
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
                    const char value = TEST_RAND(ALPHA_LETTERS);
                    assert(count(b.begin(), b.end(), value) == str_count(&a, value));
                    break;
                }
            }
            CHECK(a, b);
            str_free(&a);
            free(base);
        }
    }
    TEST_PASS(__FILE__);
}
