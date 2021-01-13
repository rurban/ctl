#include "../../test.h"

#define POD
#define T int
#include <ctl/list.h>

#include <time.h>

int main(int argc, char** argv)
{
    int silent = 0;
    int t0 = TEST_TIME();
    puts(__FILE__);
    srand(0xbeef);
    if (argc >= 2 && argv[1][0] == '-' && argv[1][1] == 's')
        silent = 1;
#ifdef PERF // calc. startup delay for perf stat -D
    int t1 = TEST_TIME();
    printf("-D%d usec\n", t1 - t0);
#endif
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        list_int c = list_int_init();
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            list_int_push_back(&c, rand());
        {
            t0 = TEST_TIME();
            volatile int sum = 0;
            foreach(list_int, &c, it)
                sum += *it.ref;
        }
        if (!silent)
            printf("%10d %10d\n", elems, TEST_TIME() - t0);
        list_int_free(&c);
    }
}
