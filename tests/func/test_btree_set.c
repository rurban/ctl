#include <assert.h>
#include <stddef.h>

#define POD
#define T int
#include <ctl/btree_set.h>

static int compare3(int *left, int *right)
{
    return (*left > *right) - (*left < *right);
}

static void expect_order(btset_int *values, const int *expected, size_t size)
{
    assert(values->size == size);
    for (size_t i = 0; i < size; i++)
        assert(*btset_int_at(values, i) == expected[i]);

    btset_int_it iter = btset_int_begin(values);
    for (size_t i = 0; i < size; i++)
    {
        assert(!btset_int_it_done(&iter));
        assert(*iter.ref == expected[i]);
        btset_int_it_next(&iter);
    }
    assert(btset_int_it_done(&iter));
}

int main(void)
{
    btset_int values = btset_int_init(compare3);
    const int input[] = {10, 5, 20, 6, 12, 30, 7, 17, 3, 2, 4, 11, 13, 14, 15, 16, 18, 19, 1, 8, 9};
    const int ordered[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 30};

    for (size_t i = 0; i < sizeof(input) / sizeof(*input); i++)
        assert(btset_int_insert(&values, input[i]));
    assert(btset_int_insert(&values, 10));
    expect_order(&values, ordered, sizeof(ordered) / sizeof(*ordered));
    assert(btset_int_contains(&values, 14));
    assert(!btset_int_contains(&values, 21));
    assert(btset_int_count(&values, 1) == 1);
    assert(btset_int_count(&values, 21) == 0);
    assert(*btset_int_front(&values) == 1);
    assert(*btset_int_back(&values) == 30);

    assert(btset_int_erase(&values, 10));
    assert(!btset_int_erase(&values, 21));
    const int without_ten[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 30};
    expect_order(&values, without_ten, sizeof(without_ten) / sizeof(*without_ten));

    btset_int copy = btset_int_copy(&values);
    expect_order(&copy, without_ten, sizeof(without_ten) / sizeof(*without_ten));
    btset_int_free(&copy);
    btset_int_free(&values);
    return 0;
}
