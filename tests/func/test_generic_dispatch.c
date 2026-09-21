#include <assert.h>
#include <stddef.h>
#include <stdlib.h>

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

#include <ctl/generic.h>

// Registries: only types that actually define the dispatched method name
// belong in the same list (push_back exists for vec_T, not uset_T; insert
// and contains exist for uset_T, not vec_T; size exists for every
// container, so it uses the combined list).
#define CTL_VEC_TYPES(X, ...)      \
    X(vec_int, __VA_ARGS__)        \
    X(vec_double, __VA_ARGS__)

#define CTL_USET_TYPES(X, ...)     \
    X(uset_int, __VA_ARGS__)

#define CTL_ALL_TYPES(X, ...)      \
    X(vec_int, __VA_ARGS__)        \
    X(vec_double, __VA_ARGS__)     \
    X(uset_int, __VA_ARGS__)

#define push_back(self, ...) CTL_GENERIC_DISPATCH(CTL_VEC_TYPES, push_back, self, __VA_ARGS__)
#define insert(self, ...) CTL_GENERIC_DISPATCH(CTL_USET_TYPES, insert, self, __VA_ARGS__)
#define contains(self, ...) CTL_GENERIC_DISPATCH(CTL_USET_TYPES, contains, self, __VA_ARGS__)
#define size(self) CTL_GENERIC_DISPATCH0(CTL_ALL_TYPES, size, self)
// A dispatch macro named ctl_free (not free) avoids shadowing libc's
// free(void*) altogether: _Generic requires an *exact* type match with no
// implicit conversion, so a `void *` fallback case only ever catches
// pointers already declared as `void *` -- not `int *`, `struct foo *`,
// etc. Redefining `free` itself is therefore unsafe for any file that
// also frees other heap pointers; a distinct name sidesteps the problem.
#define ctl_free(self) CTL_GENERIC_DISPATCH0(CTL_ALL_TYPES, free, self)

// CTL_GENERIC_DISPATCH_EXTRA: add one exact extra case (here, literal
// `void *`) alongside the registered container types.
static int ctl_is_null(void *p) { return p == NULL; }
#define CTL_USET_ONLY(X, ...) X(uset_int, __VA_ARGS__)
#define is_empty(self) CTL_GENERIC_DISPATCH_EXTRA0(CTL_USET_ONLY, empty, void *: ctl_is_null, self)

int main(void)
{
    vec_int a = vec_int_init();
    push_back(&a, 1);
    push_back(&a, 2);
    assert(size(&a) == 2);

    vec_double d = vec_double_init();
    push_back(&d, 1.5);
    assert(size(&d) == 1);

    uset_int b = uset_int_init(int_hash, int_equal);
    insert(&b, 10);
    insert(&b, 20);
    assert(size(&b) == 2);
    assert(contains(&b, 10));
    assert(!contains(&b, 99));

    // Same dispatch macro, both branches actually taken: uset_int_empty
    // for the registered type, ctl_is_null for the exact `void *` case.
    assert(!is_empty(&b));
    void *nothing = NULL;
    assert(is_empty(nothing));

    // A plain heap pointer keeps using libc free() untouched, because
    // ctl_free is a distinct name from free.
    int *raw = malloc(sizeof(int));
    *raw = 42;
    free(raw);

    ctl_free(&a);
    ctl_free(&d);
    ctl_free(&b);
    return 0;
}
