#include "../../test.h"

#define POD
#define T int
#include <ctl/vector.h>

#include <time.h>

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        vec_int c = vec_int_init();
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            vec_int_push_back(&c, rand());
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            vec_int_pop_back(&c);
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
        vec_int_free(&c);
    }
}
