#ifndef __TEST__H__
#define __TEST__H__

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include <time.h>
#ifndef _WIN32
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>
#else
#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <sysinfoapi.h>
#include <process.h>
#define getpid _getpid
#endif
#include <assert.h>

#ifdef LONG
#define TEST_MAX_SIZE  (4096)
#define TEST_MAX_LOOPS (8096)
#else
#define TEST_MAX_SIZE  (512)
#define TEST_MAX_LOOPS (512)
#endif

#define TEST_SIGN(a) ((a < 0) ? (-1) : (a > 0) ? (1) : (0))

#define TEST_PASS(f) printf("%s: PASS\n", f)
#define TEST_FAIL(f) printf("%s: FAIL\n", f)

#define TEST_RAND(max) (((max) == 0) ? 0 : (rand() % (max)))

#define TEST_PERF_RUNS (100)
#define TEST_PERF_CHUNKS (256)

#ifndef _WIN32
static inline long
TEST_TIME(void)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return 1000000L * now.tv_sec + now.tv_usec;
}
#else
static inline long
TEST_TIME(void)
{
    return GetTickCount();
}
#endif

#ifdef SRAND
#  ifdef SEED
#    define INIT_SRAND srand(SEED); printf("-DSEED=%u ", (unsigned)SEED)
#  else
#    define INIT_SRAND                                               \
       unsigned int seed = rand()*clock()*getpid();                  \
       srand(seed);                                                  \
       printf("SEED=%u ", seed);                                     \
       fflush(stdout)
#  endif
#else
#  define INIT_SRAND
#endif

#define INIT_TEST_LOOPS(n)                    \
    size_t loops = TEST_RAND(TEST_MAX_LOOPS); \
    int test = -1;                            \
    char *env = getenv ("TEST");              \
    if (env)                                  \
        sscanf(env, "%d", &test);             \
    if (test >= 0)                            \
        loops = n;                            \
    if ((env = getenv ("LOOPS")))             \
        sscanf(env, "%zu", &loops)


#endif
