#include "../../test.h"

#include <unordered_set>
#include <time.h>

class int_hash { public:
    std::size_t operator()(const int& a) const { return (size_t)a; }
};

int main()
{
    puts(__FILE__);
    srand(0xbeef);
    for(int run = 0; run < TEST_PERF_RUNS; run++)
    {
        std::unordered_set<int,int_hash> c;
        int elems = TEST_PERF_CHUNKS * run;
        for(int elem = 0; elem < elems; elem++)
            c.insert(rand() % elems);
        long t0 = TEST_TIME();
        volatile int sum = 0;
        for(auto& x : c)
            sum = sum + x;
        long t1 = TEST_TIME();
        printf("%10d %10ld\n", elems, t1 - t0);
    }
}
