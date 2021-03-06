#include "../../test.h"

#include <string>
#include <time.h>

int main()
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        std::string c;
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            c.push_back('a'+TEST_RAND(23));
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems/10; elem++)
            c.erase(elem, 1);
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
    }
}
