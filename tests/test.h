#ifndef __TEST__H__
#define __TEST__H__

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifndef _WIN32
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>
#else
#define WIN32_LEAN_AND_MEAN
#define VC_EXTRALEAN
#include <windows.h>
#include <process.h>
#include <sysinfoapi.h>
#define getpid _getpid
#endif
#undef NDEBUG
#include <assert.h>

#define POD
#define T int
#include <ctl/queue.h>
#define POD
#define T short
#include <ctl/vector.h>
#include <ctl/string.h>

#ifdef LONG
#define TEST_MAX_SIZE (4096)
#define TEST_MAX_LOOPS (8096)
#else
#define TEST_MAX_SIZE (512)
#define TEST_MAX_LOOPS (512)
#endif

#define TEST_SIGN(a) ((a < 0) ? (-1) : (a > 0) ? (1) : (0))

#define TEST_PASS(f) printf("%s: PASS\n", f)
#define TEST_FAIL(f) printf("%s: FAIL\n", f)

#define TEST_RAND(max) (((max) == 0) ? 0 : (int)(rand() % (max)))

#define TEST_PERF_RUNS (100)
#define TEST_PERF_CHUNKS (256)

#ifndef _WIN32
static inline long TEST_TIME(void)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return 1000000L * now.tv_sec + now.tv_usec;
}
#else
static inline long TEST_TIME(void)
{
    return GetTickCount();
}
#endif

#ifdef SRAND
#ifdef SEED
#define INIT_SRAND                                                                                                     \
    srand(SEED);                                                                                                       \
    printf("-DSEED=%u ", (unsigned)SEED);                                                                              \
    fflush(stdout)
#else
#define INIT_SRAND                                                                                                     \
    unsigned int seed = rand() ^ clock() ^ getpid();                                                                   \
    srand(seed);                                                                                                       \
    printf("SEED=%u ", seed);                                                                                          \
    fflush(stdout)
#endif
#else
#define INIT_SRAND
#endif

// FIXME: ensure we have all cases covered
#define INIT_TEST_LOOPS(n)                                                                                             \
    unsigned loops = 10 + TEST_RAND(TEST_MAX_LOOPS - 10);                                                                \
    vec_short covvec = vec_short_init();                                                                               \
    queue_int tests = queue_int_init();                                                                                \
    static int test = -1;                                                                                              \
    char *env = getenv("TEST");                                                                                        \
    vec_short_resize(&covvec, TEST_TOTAL, 0);                                                                          \
    if (env)                                                                                                           \
        parse_TEST(env, &test, &tests, number_ok);                                                                     \
    if (tests.size)                                                                                                    \
    {                                                                                                                  \
        /* loop a single TEST=20 n times (=10) */                                                                      \
        loops = tests.size == 1 ? n : tests.size;                                                                      \
        LOG("LOOPS: %u\n", loops);                                                                                     \
    }                                                                                                                  \
    if ((env = getenv("LOOPS")))                                                                                       \
    {                                                                                                                  \
        sscanf(env, "%u", &loops);                                                                                     \
    }                                                                                                                  \
    loops:

#define RECORD_WHICH covvec.vector[which]++

#define FINISH_TEST(FILE)                                                                                              \
    /* check if we covered all tests. If not redo the missing */                                                       \
    int redo = 0;                                                                                                      \
    LOG("Test stats: ");                                                                                               \
    foreach (vec_short, &covvec, it)                                                                                   \
    {                                                                                                                  \
        int w = vec_short_it_index(&it);                                                                               \
        int c = *it.ref;                                                                                               \
        if (!c && w < number_ok)                                                                                       \
        {                                                                                                              \
            redo = 1;                                                                                                  \
            printf("Missing test %d\n", w);                                                                            \
            queue_int_push(&tests, w);                                                                                 \
            queue_int_push(&tests, w);                                                                                 \
            queue_int_push(&tests, w);                                                                                 \
            queue_int_push(&tests, w);                                                                                 \
        }                                                                                                              \
        else                                                                                                           \
        {                                                                                                              \
            LOG("%d: %dx, ", w, c);                                                                                     \
        }                                                                                                              \
    }                                                                                                                  \
    LOG("\n");                                                                                                         \
    if (redo)                                                                                                          \
    {                                                                                                                  \
        printf("Redo missing tests\n");                                                                                \
        loops = tests.size;                                                                                            \
        redo = 0;                                                                                                      \
        goto loops;                                                                                                    \
    }                                                                                                                  \
    queue_int_free(&tests);                                                                                            \
    vec_short_free(&covvec);                                                                                           \
    if (fail)                                                                                                          \
        TEST_FAIL(FILE);                                                                                               \
    else                                                                                                               \
        TEST_PASS(FILE);

/*
  TEST=OK tests all stable tests even with DEBUG
  TEST=1-10 or TEST=1,5,7,8-10 tests ranges.
*/
void parse_TEST(char *env, int *test, queue_int *tests, const int number_ok)
{
    if (!strcmp(env, "OK"))
    {
        for (int j = 0; j < number_ok; j++)
            queue_int_push(tests, j);
        LOG("TEST OK: 0-%d\n", number_ok - 1);
        return;
    }
    sscanf(env, "%d", test);
    if (!strchr(env, '-') && !strchr(env, ','))
        return;
    if (*test >= 0)
        queue_int_push(tests, *test);
    str s = str_init(env);
    str_it r1 = str_it_begin(&s);
    str alts = str_init("-,");
    str_it r2 = str_it_begin(&alts);
    while (str_find_first_of_range(&r1, &r2))
    {
        int i = 0;
        char *p = r1.ref;
        sscanf(p+1, "%d", &i);
        if (*p == '-' && i > *test)
            for (int j=*test+1; j<i; j++)
                queue_int_push(tests, j);
        else if (i && *p == ',')
            queue_int_push(tests, i);
        str_it_advance(&r1, 1);
    }
    str_free(&s);
    str_free(&alts);
}

#endif

#ifndef MAX
#define MAX(a, b) (a) > (b) ? (a) : (b)
#endif
#ifndef MIN
#define MIN(a, b) (a) < (b) ? (a) : (b)
#endif

#define OLD_MAIN                                                                                                       \
    int main(void)                                                                                                     \
    {                                                                                                                  \
        TEST_FAIL(__FILE__);                                                                                           \
    }
