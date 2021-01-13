#include "../../test.h"

#define POD
#define T int
#include <ctl/list.h>

#include <time.h>

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        list_int c = list_int_init();
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            list_int_push_front(&c, rand());
        int t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            list_int_pop_front(&c);
        int t1 = TEST_TIME();
        printf("%10d %10d\n", elems, t1 - t0);
        list_int_free(&c);
    }
}
