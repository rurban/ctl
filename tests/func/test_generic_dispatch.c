#include <assert.h>
#include <stddef.h>

static size_t int_hash(int *value) { return (size_t)*value; }
static int int_equal(int *left, int *right) { return *left == *right; }

#define POD
#define T int
#include <ctl/vector.h>

#define POD
#define T int
#include <ctl/unordered_set.h>

// Portable C11 _Generic recipe (#4): the caller lists the instantiated
// types actually used in this translation unit; the compiler picks the
// matching prefixed function from the pointer type of `self`.
#define insert(self, ...) _Generic((self), \
    vec_int *: vec_int_push_back, \
    uset_int *: uset_int_insert)(self, __VA_ARGS__)

#define count_of(self) _Generic((self), \
    vec_int *: vec_int_size, \
    uset_int *: uset_int_size)(self)

int main(void)
{
    vec_int a = vec_int_init();
    insert(&a, 1);
    insert(&a, 2);
    assert(count_of(&a) == 2);

    uset_int b = uset_int_init(int_hash, int_equal);
    insert(&b, 10);
    insert(&b, 20);
    assert(count_of(&b) == 2);

    vec_int_free(&a);
    uset_int_free(&b);
    return 0;
}
