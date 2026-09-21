#include <assert.h>
#include <ctl/strv.h>
int main(void)
{
    strv hello = strv_init("hello world");
    assert(strv_size(&hello) == 11);
    assert(!strv_empty(&hello));
    assert(strv_front(&hello) == 'h');
    assert(strv_back(&hello) == 'd');
    assert(strv_at(&hello, 6) == 'w');

    strv world = strv_substr(&hello, 6, STRV_NPOS);
    assert(world.size == 5);
    strv expect_world = strv_init("world");
    assert(strv_equal(&world, &expect_world));

    strv needle = strv_init("wor");
    assert(strv_find(&hello, &needle) == 6);
    strv missing = strv_init("xyz");
    assert(strv_find(&hello, &missing) == STRV_NPOS);

    strv prefix = strv_init("hello");
    assert(strv_starts_with(&hello, &prefix));
    strv suffix = strv_init("world");
    assert(strv_ends_with(&hello, &suffix));
    assert(!strv_starts_with(&hello, &suffix));

    strv a = strv_init("abc");
    strv b = strv_init("abd");
    assert(strv_compare(&a, &b) < 0);
    assert(strv_compare(&b, &a) > 0);
    assert(strv_compare(&a, &a) == 0);

    strv empty = strv_init_n(NULL, 0);
    assert(strv_empty(&empty));
    assert(strv_find(&hello, &empty) == 0);

    size_t sum = 0;
    for (const char *it = strv_begin(&hello); it != strv_end(&hello); it++)
        sum += (size_t)*it;
    assert(sum > 0);
    return 0;
}
