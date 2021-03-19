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
typedef uint16_t u16;
#define POD
#define T u16
#include <ctl/vector.h>
#include <ctl/string.h>

// coverage counter for generic_iter: bitmask of 3 values
union gen_cov_u {
    struct {
        unsigned w1:8;
        unsigned t1:4;
        unsigned t2:4;
    } u;
    u16 w;
};

#ifdef LONG
#define TEST_MAX_SIZE (4096)
#undef TEST_MAX_LOOPS
#define TEST_MAX_LOOPS (8096)
#else
#define TEST_MAX_SIZE (512)
#ifndef TEST_MAX_LOOPS
# define TEST_MAX_LOOPS (512)
#endif
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
    const unsigned int seed = (rand() * (clock() & 0xffff)) ^ getpid();                                                \
    srand(seed);                                                                                                       \
    printf("SEED=%u ", seed);                                                                                          \
    fflush(stdout)
#endif
#else
#define INIT_SRAND
#endif

#define INIT_TEST_LOOPS(n, generic)                                                                                    \
    unsigned loops = TEST_TOTAL + TEST_RAND(TEST_MAX_LOOPS - TEST_TOTAL);                                              \
    vec_u16 covvec = vec_u16_init();                                                                                   \
    queue_int tests = queue_int_init();                                                                                \
    static int test = -1;                                                                                              \
    char *env = getenv("TEST");                                                                                        \
    vec_u16_resize(&covvec, TEST_TOTAL, 0);                                                                            \
    if (generic)                                                                                                       \
        loops *= 4;                                                                                                    \
    if (env)                                                                                                           \
        parse_TEST(env, &test, &tests, number_ok, generic);                                                            \
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

/* check if we covered all tests. If not redo the missing tests. */
static inline int check_redo(vec_u16 *covvec, queue_int *tests, const int number_ok)
{
    queue_int todo = queue_int_init();
    const char* env = getenv("TEST");
    int i = 0;
    LOG("Test stats: ");
    foreach (vec_u16, covvec, it)
    {
        union gen_cov_u wu;
        int w = vec_u16_it_index(&it); // which test
        wu.w = w;
        int c = *it.ref;               // test coverage count 
        if (!c && covvec->capacity > 1024)
        {
            // different validity. normally it is !c
            if (wu.u.w1 > number_ok ||
                wu.u.t1 > 5 ||
                wu.u.t2 > 5)
                continue;
        }
        if (!c && (wu.u.w1 < number_ok))
        {
            if (!env)
            {
                queue_int_push(&todo, w);
                queue_int_push(tests, w);
                queue_int_push(tests, w);
                queue_int_push(tests, w);
                //queue_int_push(tests, w);
            }
        }
        else if (covvec->capacity <= 1024) // not generic_iter
        {
            LOG("%d: %dx, ", w, c);
            if (!(++i % 12))
            {
                LOG("\n");
            }
        }
        else // generic_iter
        {
            LOG("%d-%d-%d: %dx, ", wu.u.w1, wu.u.t1, wu.u.t2, c);
            if (!(++i % 8))
            {
                LOG("\n");
            }
        }
    }
    LOG("\n");
    if (todo.size)
    {
        i = 0;
        printf("Redo missing tests: ");
        while (todo.size)
        {
            if (covvec->capacity > 1024) // 0x5514 or so
            {
                union gen_cov_u wu;
                wu.w = *queue_int_front(&todo);
                printf("%d-%d-%d ", wu.u.w1, wu.u.t1, wu.u.t2);
                //printf("0x%x ", *queue_int_front(&todo));
                if (!(++i % 12))
                    printf("\n");
            }
            else
            {
                printf("%d ", *queue_int_front(&todo));
                if (!(++i % 20))
                    printf("\n");
            }
            queue_int_pop(&todo);
        }
        printf("\n");
        queue_int_free(&todo);
        return 1;
    }
    queue_int_free(&todo);
    return 0;
}

#define FINISH_TEST(FILE)                                                                                              \
    if (check_redo(&covvec, &tests, number_ok))                                                                        \
    {                                                                                                                  \
        loops = tests.size;                                                                                            \
        goto loops;                                                                                                    \
    }                                                                                                                  \
    queue_int_free(&tests);                                                                                            \
    vec_u16_free(&covvec);                                                                                             \
    if (fail)                                                                                                          \
        TEST_FAIL(FILE);                                                                                               \
    else                                                                                                               \
        TEST_PASS(FILE);

/*
  TEST=OK tests all stable tests even with DEBUG
  TEST=1-10 or TEST=1,5,7,8-10 tests ranges.
*/
void parse_TEST(char *env, int *test, queue_int *tests, const int number_ok, bool generic)
{
    if (!strcmp(env, "OK"))
    {
        for (int j = 0; j < number_ok; j++)
        {
            if (generic)
            {
                union gen_cov_u wu;
                for (int k=0; k<4; k++)
                {
                    wu.u.t1 = TEST_RAND(6);
                    wu.u.t2 = TEST_RAND(6);
                    wu.u.w1 = j;
                    queue_int_push(tests, wu.w);
                }
            }
            else
                queue_int_push(tests, j);
        }
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
