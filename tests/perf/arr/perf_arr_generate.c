#include <stdio.h>
#include "../../test.h"

void generate_c (const int n, const char* file, const int i)
{
    FILE *f = fopen(file, "w");
    fprintf(f, "\n"
"#include \"../../test.h\"\n"
"\n"
"#define POD\n"
"#define T double\n"
"#define N %d\n"
"#include <ctl/array.h>\n"
"#include <time.h>\n"
"\n"
"int main(void)\n"
"{\n"
"    //puts(__FILE__);\n"
"    srand(0xbeef);\n"
"    arr%d_double c = arr%d_double_init();\n"
"    int elems = %d;\n"
"\n"
"    for(int elem = 0; elem < elems; elem++)\n"
"        *arr%d_double_at(&c, elem) = rand() * 1.0;\n", n, n, n, n, n);
    if (i < 2)
        fprintf(f,
"    const int n = elems/2;\n"
"    const double key = *arr%d_double_at(&c, n);\n", n);
    fprintf(f,
"    long t0 = TEST_TIME();\n\n");
    if (i == 0)
        fprintf(f, "    arr%d_double_find(&c, key);\n", n);
    else if (i == 1)
        fprintf(f, "    arr%d_double_fill_n(&c, n, key);\n", n);
    else if (i == 2)
        fprintf(f, "    arr%d_double_sort(&c);\n", n);
    else if (i == 3)
        fprintf(f,
"    volatile double sum = 0;\n"
"    foreach(arr%d_double, &c, it)\n"
"        sum += *it.ref;\n", n);
    fprintf(f, "\n"
"    long t1 = TEST_TIME();\n"
"    printf(\"%%10d %%10ld\\n\", elems, t1 - t0);\n"
"\n"
"    arr%d_double_free(&c);\n"
"}", n);
    fclose(f);
}

void generate_cc (const int n, const char* file, const int i)
{
    FILE *f = fopen(file, "w");
    fprintf(f, "\n"
"#include \"../../test.h\"\n"
"\n"
"#include <array>\n"
"#include <algorithm>\n"
"#include <time.h>\n");
    if (i == 2)
        fprintf(f, "\n"
"#include <stdbool.h>\n"
"static int double_compare(double& a, double& b) { return a < b; }\n");
    fprintf(f, "\n"
"int main(void)\n"
"{\n"
"    //puts(__FILE__);\n"
"    srand(0xbeef);\n"
"    std::array<double,%d> c;\n"
"    const int elems = %d;\n"
"\n"
"    for(int elem = 0; elem < elems; elem++)\n"
"        c[elem] = rand() * 1.0;\n", n, n);
    if (i < 2)
        fprintf(f,
"    const int n = elems/2;\n"
"    const double key = c[n];\n");
    fprintf(f,
"    long t0 = TEST_TIME();\n\n");
    if (i == 0)
        fprintf(f, "    std::find(c.begin(), c.end(), key);\n");
    else if (i == 1)
        fprintf(f, "    std::fill_n(c.begin(), n, key);\n");
    else if (i == 2)
        fprintf(f, "    std::sort(c.begin(), c.end(), double_compare);\n");
    else if (i == 3)
        fprintf(f,
"    volatile double sum = 0;\n"
"    for(auto& x : c)\n"
"        sum += x;\n");
    fprintf(f, "\n"
"    long t1 = TEST_TIME();\n"
"    printf(\"%%10d %%10ld\\n\", elems, t1 - t0);\n"
"}\n");
    fclose(f);
}

int main(void)
{
    static const char* m[] = {"find", "fill_n", "sort", "iterate"};
    for(int i = 0; i < 4; i++)
        for(int run = 0; run < TEST_PERF_RUNS; run++)
        {
            int elems = TEST_PERF_CHUNKS * run;
            char c[128], cc[128];
            if (!run)
                continue;
            sprintf(c, "tests/perf/arr/gen_arr%06d_%s.c", elems, m[i]);
            sprintf(cc, "tests/perf/arr/gen_array%06d_%s.cc", elems, m[i]);
            generate_c(elems, c, i);
            generate_cc(elems, cc, i);
        }
}
