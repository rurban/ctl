#include "../../test.h"

#define POD
#define T int
#include <ctl/set.h>

#include <time.h>

static int compare(int* a, int* b) { return *a == *b ? 0 : *a < *b ? -1 : 1; }

int main(void)
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        set_int c = set_int_init(compare);
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            set_int_insert(&c, rand() % elems);
        volatile int sum = 0;
        long t0 = TEST_TIME();
        foreach(set_int, &c, it)
            sum += *it.ref;
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
        set_int_free(&c);
    }
}
