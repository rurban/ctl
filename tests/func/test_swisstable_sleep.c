// Test that we detect DDOS attacks (excessive probe runs from a
// degenerate hash) in the open-addressing <ctl/swisstable.h>.
#include "../test.h"

// default CTL_USET_SECURITY_COLLCOUNTING 2
#define POD
#define TK int
#define T int
#include <ctl/swisstable.h>

static int _slept = 0;

#ifndef _WIN32
// catch default CTL_USET_SECURITY_ACTION sleep(1)
inline unsigned int sleep(unsigned int seconds)
{
    (void)seconds;
    LOG("sleep() %d\n", _slept);
    return ++_slept;
}
#else
// catch default CTL_USET_SECURITY_ACTION Sleep(500)
inline void Sleep(uint32_t milliseconds)
{
    (void)milliseconds;
    LOG("Sleep() %d\n", _slept);
    return ++_slept;
}
#endif

static inline size_t
broken_hash(int *a)
{
    (void)a;
    return 0;
}

static inline int
int_equal(int *a, int *b)
{
    return *a == *b;
}

int main(void)
{
    srand(0xbebe);
    const int size = 148;
    swiss_int_int a = swiss_int_int_init(broken_hash, int_equal);
    swiss_int_int_reserve(&a, size);
    for (int i = 0; i < size; i++)
    {
        const int vb = TEST_RAND(1000);
        swiss_int_int_insert(&a, vb, vb);
    }
    swiss_int_int_free(&a);
    assert(_slept > 0);
}
