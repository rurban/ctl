#include "../../test.h"

#include <set>
#include <time.h>

int main()
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        std::set<int> c;
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            c.insert(rand() % elems);
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            c.erase(rand() % elems);
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
    }
}
