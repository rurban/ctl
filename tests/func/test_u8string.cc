#include "../test.h"

// rely on GNU libunistring backend for now
#include <uninorm.h>
#include <ctl/u8string.h>
#include <stdlib.h>
//#include <wchar.h>
#include <wctype.h>
#include <locale.h>

static locale_t utf8_locale;

// WHOA, not C++ support for u8string yet, even if defined a bit in C++20
#include <string>
#include <algorithm>

#define MIN_STR_SIZE  (30) // NO SUPPORT FOR SMALL STRINGS.
#define ALPHA_LETTERS (23)

#define CHECK(_x, _y) {                              \
    assert(u8strcmp(u8str_c_str(&_x), _y.c_str()) == 0); \
    assert(_x.capacity == _y.capacity());            \
    assert(_x.size == _y.size());                    \
    assert(u8str_empty(&_x) == _y.empty());          \
    if(_x.size > 0) {                                \
        assert(_y.front() == *u8str_front(&_x));     \
        assert(_y.back() == *u8str_back(&_x));       \
    }                                                \
    std::string::iterator _iter = _y.begin();        \
    foreach(u8str, &_x, _it) {                       \
        assert(*_it.ref == *_iter);                  \
        _iter++;                                     \
    }                                                \
    u8str_it _it = u8str_it_each(&_x);               \
    for(auto& _d : _y) {                             \
        assert(*_it.ref == _d);                      \
        _it.step(&_it);                              \
    }                                                \
    for(size_t i = 0; i < _y.size(); i++)            \
        assert(_y.at(i) == *u8str_at(&_x, i));       \
}

static int
is_proper_uni(wint_t wc)
{
    return (wc < 0x3400 ||
            (wc >= 0xa000 && wc < 0xAC00) ||
            (wc >= 0xd7b0 && wc < 0xd800) ||
            (wc >= 0xf900 && wc < 0x1BC6A));
}

// want u8"Привет, мир!"
static wint_t
rand_uni_alpha()
{
    wint_t a = 'A' + TEST_RAND(0x1BC6A);

    while (!is_proper_uni(a) || !iswalnum_l(a, utf8_locale))
        a = 'A' + TEST_RAND(0x1BC6A);
    return a;
}

static inline char*
rand_utf8_alpha()
{
    int i = 0;
    char *buf = (char*) calloc(1, MB_CUR_MAX);
    switch (TEST_RAND(4))
    {
    case 0: case_0:
        buf[0] = 'a' + TEST_RAND(ALPHA_LETTERS);
        return buf;
    case 1:
        buf[0] = 'A' + TEST_RAND(ALPHA_LETTERS);
        return buf;
    case 2:
    {
        wchar_t a = rand_uni_alpha();
        while (wctomb(buf, a) < 0 && i < 100)
        {
            a = rand_uni_alpha();
            i++;
        }
        if (i >= 100) // broken wctomb, e.g. glibc
            goto case_0;
        return buf;
    }
    case 3:
    {
        wchar_t a = towupper_l(rand_uni_alpha(), utf8_locale);
        while (wctomb(buf, a) < 0 && i < 100)
        {
            a = towupper_l(rand_uni_alpha(), utf8_locale);
            i++;
        }
        if (i >= 100) // broken wctomb, e.g. glibc
            goto case_0;
        return buf;
    }
    }
    return buf;
}

static char8_t*
create_test_string(size_t size)
{
    char8_t* temp = (char8_t*) malloc(size + 1);
    for(size_t i = 0; i < size; i++)
    {
        char *u8 = rand_utf8_alpha();
        int len = strlen(u8);
        if (len > 1)
        {
            size += len;
            temp = (char8_t*) realloc(temp, size);
        }
        strcpy ((char*)temp, u8);
        free (u8);
    }
    temp[size] = '\0';
    return temp;
}

// silly hacks for now
static int
u8strcmp(char8_t* a, const char* b)
{
    return strcmp((char*)a, b);
}

static int
char8_compare(char8_t* a, char8_t* b)
{
    return *a > *b;
}

int
main(void)
{
    INIT_SRAND;
    utf8_locale = newlocale(LC_ALL_MASK, "en_US.UTF8", (locale_t)0);
    setenv("LC_CTYPE", "en_US.UTF8", 1);
    size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    int test = -1;
    char *env = getenv ("TEST");
    if (env)
        sscanf(env, "%d", &test);
    if (test >= 0)
        loops = 30;
    for(size_t loop = 0; loop < loops; loop++)
    {
        size_t u8str_size = TEST_RAND(TEST_MAX_SIZE);
        if(u8str_size < MIN_STR_SIZE)
            u8str_size = MIN_STR_SIZE;
#if defined(DEBUG) && !defined(LONG)
        u8str_size = MIN_STR_SIZE;
#endif
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            char8_t* base = create_test_string(u8str_size);
            u8str a = u8str_init(u8"");
            a.compare = char8_compare;
            std::string b;
            if(mode == MODE_DIRECT)
            {
                u8str_free(&a);
                a = u8str_init(base);
                b = (char*)base;
            }
            if(mode == MODE_GROWTH)
            {
                for(size_t i = 0; i < u8str_size; i++)
                {
                    u8str_push_back(&a, base[i]);
                    b.push_back((char)base[i]);
                }
            }
            enum
            {
                TEST_PUSH_BACK,
                TEST_POP_BACK,
                TEST_APPEND,
                TEST_C_STR,
                TEST_CLEAR,
                TEST_ERASE,
                TEST_RESIZE,
                TEST_RESERVE,
                TEST_SHRINK_TO_FIT,
                TEST_SORT,
                TEST_COPY,
                TEST_SWAP,
                TEST_INSERT,
                TEST_ASSIGN,
                TEST_REPLACE,
                TEST_FIND,
                TEST_RFIND,
                TEST_FIND_FIRST_OF,
                TEST_FIND_LAST_OF,
                TEST_FIND_FIRST_NOT_OF,
                TEST_FIND_LAST_NOT_OF,
                TEST_SUBSTR,
                TEST_COMPARE,
                TEST_COUNT,
                TEST_TOTAL
            };
            int which = TEST_RAND(TEST_TOTAL);
            if (test >= 0 && test < (int)TEST_TOTAL)
                which = test;
            LOG ("TEST %d\n", which);
            switch(which)
            {
                case TEST_PUSH_BACK:
                {
                    const char value = TEST_RAND(ALPHA_LETTERS);
                    b.push_back(value);
                    u8str_push_back(&a, value);
                    CHECK(a, b);
                    break;
                }
                case TEST_POP_BACK:
                {
                    if(a.size > 0)
                    {
                        b.pop_back();
                        u8str_pop_back(&a);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_APPEND:
                {
                    char8_t* temp = create_test_string(TEST_RAND(256));
                    u8str_append(&a, temp);
                    b.append((char*)temp);
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_C_STR:
                {
                    assert(strlen((char*)u8str_c_str(&a)));
                    assert(u8str_c_str(&a) == u8str_data(&a));
                    CHECK(a, b);
                    break;
                }
                case TEST_REPLACE:
                {
                    char8_t* temp = create_test_string(TEST_RAND(a.size));
                    const size_t index = TEST_RAND(a.size);
                    const size_t size = TEST_RAND(a.size);
                    u8str_replace(&a, index, size, temp);
                    b.replace(index, size, (char*)temp);
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND:
                {
                    const size_t size = TEST_RAND(3);
                    char8_t* temp = create_test_string(size);
                    assert(u8str_find(&a, temp) == b.find((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_RFIND:
                {
                    char8_t* temp = create_test_string(TEST_RAND(3));
                    assert(u8str_rfind(&a, temp) == b.rfind((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_FIRST_OF:
                {
                    const size_t size = TEST_RAND(3);
                    char8_t* temp = create_test_string(size);
                    assert(u8str_find_first_of(&a, temp) == b.find_first_of((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_LAST_OF:
                {
                    const size_t size = TEST_RAND(3);
                    char8_t* temp = create_test_string(size);
                    assert(u8str_find_last_of(&a, temp) == b.find_last_of((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_FIRST_NOT_OF:
                {
                    const size_t size = TEST_RAND(192);
                    char8_t* temp = create_test_string(size);
                    assert(u8str_find_first_not_of(&a, temp) == b.find_first_not_of((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_FIND_LAST_NOT_OF:
                {
                    const size_t size = TEST_RAND(192);
                    char8_t* temp = create_test_string(size);
                    assert(u8str_find_last_not_of(&a, temp) == b.find_last_not_of((char*)temp));
                    free(temp);
                    CHECK(a, b);
                    break;
                }
                case TEST_SUBSTR:
                {
                    const size_t index = TEST_RAND(a.size);
                    const size_t size = TEST_RAND(a.size - index);
                    if(size > MIN_STR_SIZE)
                    {
                        u8str substr1 = u8str_substr(&a, index, size);
                        std::string substr2 = b.substr(index, size);
                        CHECK(substr1, substr2);
                        u8str_free(&substr1);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_COMPARE:
                {
                    size_t size = TEST_RAND(512);
                    char8_t* _ta = create_test_string(size);
                    char8_t* _tb = create_test_string(size);
                    u8str _a = u8str_init(_ta);
                    u8str _b = u8str_init(_tb);
                    std::string _aa = (char*)_ta;
                    std::string _bb = (char*)_tb;
                    assert(TEST_SIGN(u8str_compare(&_a, _tb)) == TEST_SIGN(_aa.compare((char*)_tb)));
                    assert(TEST_SIGN(u8str_compare(&_b, _ta)) == TEST_SIGN(_bb.compare((char*)_ta)));
                    assert(TEST_SIGN(u8str_compare(&_a, _ta)) == TEST_SIGN(_aa.compare((char*)_ta)));
                    assert(TEST_SIGN(u8str_compare(&_b, _tb)) == TEST_SIGN(_bb.compare((char*)_tb)));
                    u8str_free(&_a);
                    u8str_free(&_b);
                    free(_ta);
                    free(_tb);
                    CHECK(a, b);
                    break;
                }
                case TEST_CLEAR:
                {
                    u8str_clear(&a);
                    b.clear();
                    CHECK(a, b);
                    break;
                }
                case TEST_ERASE:
                {
                    const size_t index = TEST_RAND(a.size);
                    b.erase(b.begin() + index);
                    u8str_erase(&a, index);
                    CHECK(a, b);
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
                        u8str_insert(&a, index, value);
                    }
                    CHECK(a, b);
                    break;
                }
                case TEST_RESIZE:
                {
                    const size_t resize = 3 * TEST_RAND(a.size);
                    b.resize(resize);
                    u8str_resize(&a, resize, '\0');
                    CHECK(a, b);
                    break;
                }
                case TEST_RESERVE:
                {
                    const size_t capacity = 3 * TEST_RAND(a.capacity);
                    b.reserve(capacity);
                    u8str_reserve(&a, capacity);
                    LOG("CTL reserve %zu %zu\n", a.size, a.capacity);
                    LOG("STL reserve %zu %zu\n", b.size(), b.capacity());
                    CHECK(a, b);
                    break;
                }
                case TEST_SHRINK_TO_FIT:
                {
                    b.shrink_to_fit();
                    u8str_shrink_to_fit(&a);
                    LOG("CTL shrink_to_fit %zu %zu\n", a.size, a.capacity);
                    LOG("STL shrink_to_fit %zu %zu\n", b.size(), b.capacity());
                    CHECK(a, b);
                    break;
                }
                case TEST_SORT:
                {
                    LOG("before sort \"%s\"\n", (char*)a.value);
                    u8str_sort(&a);
                    LOG("after  sort \"%s\"\n", (char*)a.value);
                    std::sort(b.begin(), b.end());
                    LOG("STL    sort \"%s\"\n", b.c_str());
                    CHECK(a, b);
                    break;
                }
                case TEST_COPY:
                {
                    u8str ca = u8str_copy(&a);
                    std::string cb = b;
                    LOG("copy  a: \"%s\": %zu\n", (char*)a.value, a.capacity);
                    LOG("copy ca: \"%s\": %zu\n", (char*)ca.value, ca.capacity);
                    CHECK(ca, cb);
                    u8str_free(&ca);
                    CHECK(a, b);
                    break;
                }
                case TEST_ASSIGN:
                {
                    const char value = TEST_RAND(ALPHA_LETTERS);
                    size_t assign_size = TEST_RAND(a.size);
                    u8str_assign(&a, assign_size, value);
                    b.assign(assign_size, value);
                    CHECK(a, b);
                    break;
                }
                case TEST_SWAP:
                {
                    u8str aa = u8str_copy(&a);
                    u8str aaa = u8str_init(u8"");
                    std::string cb = b;
                    std::string bbb;
                    u8str_swap(&aaa, &aa);
                    std::swap(cb, bbb);
                    CHECK(aaa, bbb);
                    u8str_free(&aaa);
                    u8str_free(&aa);
                    CHECK(a, b);
                    break;
                }
                case TEST_COUNT:
                {
                    const char value = TEST_RAND(ALPHA_LETTERS);
                    assert(count(b.begin(), b.end(), value) == u8str_count(&a, value));
                    CHECK(a, b);
                    break;
                }
            }
            CHECK(a, b);
            u8str_free(&a);
            free(base);
        }
    }
    TEST_PASS(__FILE__);
}
