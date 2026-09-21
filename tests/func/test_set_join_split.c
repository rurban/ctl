#include <assert.h>
#include <stddef.h>

#define POD
#define T int
#include <ctl/set.h>

static void expect_values(set_int *values, const int *expected, size_t size)
{
    assert(values->size == size);
    set_int_it iter = set_int_begin(values);
    for (size_t i = 0; i < size; i++)
    {
        assert(!set_int_it_done(&iter));
        assert(*iter.ref == expected[i]);
        set_int_it_next(&iter);
    }
    assert(set_int_it_done(&iter));
}


static int compare3(int *left, int *right)
{
    return (*left > *right) - (*left < *right);
}
int main(void)
{
    set_int left = set_int_init(NULL);
    set_int right = set_int_init(NULL);
    const int left_values[] = {1, 3, 5};
    const int right_values[] = {3, 7, 9};

    for (size_t i = 0; i < sizeof(left_values) / sizeof(*left_values); i++)
        set_int_insert(&left, left_values[i]);
    for (size_t i = 0; i < sizeof(right_values) / sizeof(*right_values); i++)
        set_int_insert(&right, right_values[i]);

    set_int joined = set_int_join(&left, &right);
    const int joined_values[] = {1, 3, 5, 7, 9};
    expect_values(&joined, joined_values, sizeof(joined_values) / sizeof(*joined_values));
    expect_values(&left, left_values, sizeof(left_values) / sizeof(*left_values));
    expect_values(&right, right_values, sizeof(right_values) / sizeof(*right_values));

    set_int less = set_int_init(NULL);
    set_int greater = set_int_init(NULL);
    set_int_insert(&less, -1);
    set_int_insert(&greater, 11);

    assert(set_int_split(&joined, 5, &less, &greater));
    const int less_values[] = {1, 3};
    const int greater_values[] = {7, 9};
    expect_values(&less, less_values, sizeof(less_values) / sizeof(*less_values));
    expect_values(&greater, greater_values, sizeof(greater_values) / sizeof(*greater_values));
    expect_values(&joined, joined_values, sizeof(joined_values) / sizeof(*joined_values));

    assert(!set_int_split(&joined, 6, &less, &greater));
    const int less_without_key[] = {1, 3, 5};
    const int greater_without_key[] = {7, 9};
    expect_values(&less, less_without_key, sizeof(less_without_key) / sizeof(*less_without_key));
    expect_values(&greater, greater_without_key, sizeof(greater_without_key) / sizeof(*greater_without_key));

    set_int three_way = set_int_init(compare3);
    set_int three_way_less = set_int_init(NULL);
    set_int three_way_greater = set_int_init(NULL);
    set_int_insert(&three_way, 1);
    set_int_insert(&three_way, 3);
    set_int_insert(&three_way, 5);
    assert(set_int_split(&three_way, 3, &three_way_less, &three_way_greater));
    const int three_way_less_values[] = {1};
    const int three_way_greater_values[] = {5};
    expect_values(&three_way_less, three_way_less_values, 1);
    expect_values(&three_way_greater, three_way_greater_values, 1);

    set_int_free(&three_way);
    set_int_free(&three_way_less);
    set_int_free(&three_way_greater);

    set_int_free(&left);
    set_int_free(&right);
    set_int_free(&joined);
    set_int_free(&less);
    set_int_free(&greater);
    return 0;
}
