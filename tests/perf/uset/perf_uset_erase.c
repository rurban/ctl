#include "../../test.h"

#define POD
#define T int
#include <ctl/unordered_set.h>

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
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            uset_int_erase(&c, rand() % elems);
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
        uset_int_free(&c);
    }
}
