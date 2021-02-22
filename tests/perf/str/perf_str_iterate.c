#include "../../test.h"

#include <ctl/string.h>

#include <time.h>

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        str c = str_init("");
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            str_push_back(&c, 'a'+TEST_RAND(23));
        long t0 = TEST_TIME();
        volatile int sum = 0;
        str_foreach(&c, ref)
            sum = sum + *ref;
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
        str_free(&c);
    }
}
