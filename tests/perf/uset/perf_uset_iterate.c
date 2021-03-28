#include "../../test.h"

static size_t int_hash(int* a) { return *a; }
//static int int_equal(int* a, int* b)   { return *a == *b; }

#define POD
#define T int
#include <ctl/unordered_set.h>

#include <time.h>

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    uset_int c = uset_int_init();
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        unsigned int elems = TEST_PERF_CHUNKS * run;
        uset_int_reserve(&c, elems);
        for(unsigned int elem = 0; elem < elems; elem++)
            uset_int_insert(&c, rand() % elems);
        volatile int sum = 0;
        long t0 = TEST_TIME();
        foreach(uset_int, &c, it)
            sum = sum + *it.ref;
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
    }
    uset_int_free(&c);
}
