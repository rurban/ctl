#include <assert.h>
#include <stddef.h>

static size_t int_hash(int *value) { return (size_t)*value; }
static int int_equal(int *left, int *right) { return *left == *right; }

#define POD
#define T int
#include <ctl/vector.h>

#define POD
#define T double
#include <ctl/vector.h>

#define POD
#define T int
#include <ctl/unordered_set.h>

int main(void)
{
#if defined(__has_attribute) && __has_attribute(overloadable)
    // Overload resolution picks the right vec_T_/uset_T_ function purely
    // from the pointer type of the first argument, across container kinds.
    vec_int ints = vec_int_init();
    push_back(&ints, 1);
    push_back(&ints, 2);
    push_back(&ints, 3);
    assert(size(&ints) == 3);
    assert(!empty(&ints));
    assert(*at(&ints, 1) == 2);
    assert(*front(&ints) == 1);
    assert(*back(&ints) == 3);
    pop_back(&ints);
    assert(size(&ints) == 2);

    vec_double doubles = vec_double_init();
    push_back(&doubles, 1.5);
    push_back(&doubles, 2.5);
    assert(size(&doubles) == 2);
    assert(*at(&doubles, 0) == 1.5);

    vec_int copied = copy(&ints);
    assert(size(&copied) == size(&ints));
    swap(&copied, &ints);
    clear(&copied);
    assert(empty(&copied));

    uset_int set = uset_int_init(int_hash, int_equal);
    insert(&set, 10);
    insert(&set, 20);
    assert(size(&set) == 2);
    assert(contains(&set, 10));
    assert(count(&set, 10) == 1);
    erase(&set, 10);
    assert(!contains(&set, 10));

    vec_int_free(&ints);
    vec_double_free(&doubles);
    vec_int_free(&copied);
    uset_int_free(&set);
#endif
    return 0;
}
