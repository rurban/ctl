/* Test the special MUST_ALIGN_16(T) logic */
#include "../test.h"

#include <string.h>
#include <ctl/string.h>
#include <string>

#define ASSERT_EQUAL_SIZE(c, s) (assert(s.size() == c.size))
#if defined(DEBUG)
#define ASSERT_EQUAL_CAP(c, s) if (s.capacity() != c.capacity) fail++
// capacity is implemention-defined and we tested against gcc libstdc++ v3
// and llvm libc++ v1 ver 18. MSVC ?
// gcc libstdc++ had the latest change with __cplusplus >= 201103L
// libc++ had the latest change in __grow_by in PR17148, 2013
#elif (_LIBCPP_STD_VER == 18 || \
       (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L))
#define ASSERT_EQUAL_CAP(c, s) (assert(s.capacity() == c.capacity))
#endif

int
main(void)
{
    INIT_SRAND;
    size_t fail = 0;
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t loop = 0; loop < loops; loop++)
    {
        char value = TEST_RAND(256);
        // guarantee short string coverage
        size_t size = loop ? TEST_RAND(TEST_MAX_SIZE) : TEST_RAND(30);
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            str a = str_init("");
            std::string b;
            if(mode == MODE_DIRECT)
            {
                LOG("mode DIRECT\n");
                b.resize (size);
                str_resize (&a, size, '\0');
                LOG("ctl resize 0 -> %zu vs %zu\n", a.size, b.size());
            }
            else if(mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    b.push_back (value); // double cap
                    str_push_back  (&a, value);
                    LOG("cap %zu (0x%lx) vs %zu (0x%lx) size:%zu %s\n", a.capacity, a.capacity,
                        b.capacity(), b.capacity(), a.size,
                        a.capacity != b.capacity() ? "FAIL" : "");
                }
                LOG("ctl growth   %zu vs %zu\n", a.size, b.size());
                if (TEST_RAND(10) < 3)
                {
                    b.shrink_to_fit();
                    str_shrink_to_fit(&a);
                    LOG("ctl shrink_to_fit cap %zu vs %zu\n", a.capacity, b.capacity());
                }
            }
            ASSERT_EQUAL_SIZE (a, b);
            LOG("ctl capacity %zu (0x%lx) vs %zu (0x%lx) %s\n", a.capacity, a.capacity,
                b.capacity(), b.capacity(), a.capacity != b.capacity() ? "FAIL" : "");
            ASSERT_EQUAL_CAP  (a, b);
            str_free  (&a);
        }
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
