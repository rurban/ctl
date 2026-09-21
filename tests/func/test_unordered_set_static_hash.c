#include <assert.h>
#include <stddef.h>

static size_t test_hash(int *value)
{
    return (size_t)(unsigned)*value * 2654435761u;
}

static int test_equal(int *left, int *right)
{
    return *left == *right;
}

#define CTL_USET_HASH(value) test_hash(value)
#define POD
#define T int
#include <ctl/unordered_set.h>

int main(void)
{
    uset_int values = uset_int_init(test_equal);
    for (int i = 0; i < 128; i++)
        uset_int_insert(&values, i);
    for (int i = 0; i < 128; i++)
        assert(uset_int_contains(&values, i));
    uset_int_insert(&values, 64);
    assert(values.size == 128);
    uset_int_free(&values);
    return 0;
}
