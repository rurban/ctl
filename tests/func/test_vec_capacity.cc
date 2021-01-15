/* uint8_t uses MUST_ALIGN_16(T),
   the others not */
#include "../test.h"

#include <stdint.h>

#define POD
#define T uint8_t
#include <ctl/vector.h>

#define POD
#define T uint16_t
#include <ctl/vector.h>

#define POD
#define T uint32_t
#include <ctl/vector.h>

#define POD
#define T uint64_t
#include <ctl/vector.h>

#define POD
#define T float
#include <ctl/vector.h>

#define POD
#define T double
#include <ctl/vector.h>

#include <vector>

#define ASSERT_EQUAL_SIZE(_x, _y) (assert(_x.size() == _y.size))

// tested variants
#if /* (_LIBCPP_STD_VER >= 11 && _LIBCPP_STD_VER <= 18) ||*/ \
     (defined _GLIBCXX_RELEASE && __cplusplus >= 201103L)
// Tested ok with g++ 10, g++ 7.5, clang 10 (libc++ 11-18), apple clang 12
# define ASSERT_EQUAL_CAP(s, c) (assert(s.capacity() == c.capacity))
#else
// other llvm libc++ fail (gh actions), msvc untested
# define ASSERT_EQUAL_CAP(s, c) if (s.capacity() != c.capacity) \
    { printf("capacity %zu vs %zu FAIL\n", c.capacity, s.capacity()); fail++; }
#endif

int
main(void)
{
    INIT_SRAND;
    int fail = 0;
#if defined __GNUC__ && defined _GLIBCXX_RELEASE
    fprintf(stderr, "_GLIBCXX_RELEASE %d\n", (int)_GLIBCXX_RELEASE);
#elif defined _LIBCPP_STD_VER
    fprintf(stderr, "_LIBCPP_STD_VER %d\n", (int)_LIBCPP_STD_VER);
#else
    fprintf(stderr, "unknown libc++: __cplusplus %d\n", (int)__cplusplus);
#endif
    const size_t loops = TEST_RAND(TEST_MAX_LOOPS);
    for(size_t loop = 0; loop < loops; loop++)
    {
        uint8_t value = TEST_RAND(UINT8_MAX); // SMALLEST SIZE.
        size_t size = loop ? TEST_RAND(TEST_MAX_SIZE) : TEST_RAND(30);
        enum
        {
            MODE_DIRECT,
            MODE_GROWTH,
            MODE_TOTAL
        };
        for(size_t mode = MODE_DIRECT; mode < MODE_TOTAL; mode++)
        {
            std::vector<uint8_t>  a;
            std::vector<uint16_t> b;
            std::vector<uint32_t> c;
            std::vector<uint64_t> d;
            std::vector<float>    e;
            std::vector<double>   f;
            vec_uint8_t  aa = vec_uint8_t_init();
            vec_uint16_t bb = vec_uint16_t_init();
            vec_uint32_t cc = vec_uint32_t_init();
            vec_uint64_t dd = vec_uint64_t_init();
            vec_float    ee = vec_float_init();
            vec_double   ff = vec_double_init();
            if(mode == MODE_DIRECT)
            {
                LOG("mode DIRECT\n");
                a.resize (size);
                b.resize (size);
                c.resize (size);
                d.resize (size);
                e.resize (size);
                f.resize (size);
                vec_uint8_t_resize  (&aa, size, 0);
                LOG("uint8 resize    %zu vs %zu\n", aa.size, a.size());
                vec_uint16_t_resize (&bb, size, 0);
                vec_uint32_t_resize (&cc, size, 0);
                vec_uint64_t_resize (&dd, size, 0);
                vec_float_resize    (&ee, size, 0.0);
                vec_double_resize   (&ff, size, 0.0);
            }
            if(mode == MODE_GROWTH)
            {
                LOG("mode GROWTH\n");
                for(size_t pushes = 0; pushes < size; pushes++)
                {
                    a.push_back (value);
                    b.push_back (value);
                    c.push_back (value);
                    d.push_back (value);
                    e.push_back (value);
                    f.push_back (value);
                    vec_uint8_t_push_back  (&aa, value);
                    LOG("capacity  %zu (0x%lx) vs %zu (0x%lx) (%zu) %s\n", aa.capacity, aa.capacity,
                        a.capacity(), a.capacity(), aa.size,
                        aa.capacity != a.capacity() ? "FAIL" : "");
                    vec_uint16_t_push_back (&bb, value);
                    vec_uint32_t_push_back (&cc, value);
                    vec_uint64_t_push_back (&dd, value);
                    vec_float_push_back    (&ee, value);
                    vec_double_push_back   (&ff, value);
                }
            }
            LOG("uint8 size      %zu vs %zu\n", aa.size, a.size());
            ASSERT_EQUAL_SIZE (a, aa);
            LOG("uint16 size     %zu vs %zu\n", bb.size, b.size());
            ASSERT_EQUAL_SIZE (b, bb);
            ASSERT_EQUAL_SIZE (c, cc);
            ASSERT_EQUAL_SIZE (d, dd);
            ASSERT_EQUAL_SIZE (e, ee);
            ASSERT_EQUAL_SIZE (f, ff);
            LOG("uint8 capacity  %zu (0x%lx) vs %zu (0x%lx)\n", aa.capacity, aa.capacity,
                a.capacity(), a.capacity());
            ASSERT_EQUAL_CAP  (a, aa);
            LOG("uint16 capacity %zu vs %zu\n", bb.capacity, b.capacity());
            ASSERT_EQUAL_CAP  (b, bb);
            ASSERT_EQUAL_CAP  (c, cc);
            ASSERT_EQUAL_CAP  (d, dd);
            ASSERT_EQUAL_CAP  (e, ee);
            ASSERT_EQUAL_CAP  (f, ff);
            vec_uint8_t_free  (&aa);
            vec_uint16_t_free (&bb);
            vec_uint32_t_free (&cc);
            vec_uint64_t_free (&dd);
            vec_float_free    (&ee);
            vec_double_free   (&ff);
        }
    }
    if (fail)
        TEST_FAIL(__FILE__);
    else
        TEST_PASS(__FILE__);
}
