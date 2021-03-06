#include "../../test.h"

#define POD
#define T int
#include <ctl/priority_queue.h>

#include <time.h>

static int compare(int* a, int* b) { return *a < *b; }

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        pqu_int c = pqu_int_init(compare);
        int elems = TEST_PERF_CHUNKS * run;
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            pqu_int_push(&c, rand());
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
        pqu_int_free(&c);
    }
}
