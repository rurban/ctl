#include "../../test.h"

#include <queue>

#include <time.h>

struct compare { bool operator()(const int& a, const int& b) { return a < b; } };

int main()
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        std::priority_queue<int, std::vector<int>, compare> c;
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            c.push(rand());
        volatile int sum = 0;
        long t0 = TEST_TIME();
        for(int elem = 0; elem < elems; elem++)
            sum += c.top();
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
    }
}
