#include "../../test.h"

#define POD
#define T int
#include <ctl/unordered_set.h>

#include <time.h>

static size_t int_hash(int* a) { return *a; }
static int int_equal(int* a, int* b)   { return *a == *b; }

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        uset_int c = uset_int_init(int_hash, int_equal);
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            uset_int_insert(&c, rand() % elems);
        volatile int sum = 0;
        int t0 = TEST_TIME();
        foreach(uset_int, &c, it)
            sum += *it.ref;
        int t1 = TEST_TIME();
        printf("%10d %10d\n", elems, t1 - t0);
        uset_int_free(&c);
    }
}
