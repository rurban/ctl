// Test that we detect DDOS attacks
#include "../test.h"

// default CTL_USET_SECURITY_COLLCOUNTING 2
#define POD
#define T int
#include <ctl/unordered_set.h>

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
broken_hash(int* a)
{
    (void)a;
    return 0;
}

int main(void)
{
    srand(0xbebe);
    const int size = 148;
    uset_int a = uset_int_init(broken_hash, NULL);
    uset_int_rehash(&a, size);
    for (int i = 0; i < size; i++)
    {
        const int vb = TEST_RAND(1000);
        uset_int_insert(&a, vb);
    }
    uset_int_free(&a);
    assert(_slept > 0);
}
