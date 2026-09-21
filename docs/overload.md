# Overload - dropping the type prefix (clang `overloadable` and C11 `_Generic`)

CTL function names are prefixed with the container/type pair (`vec_int_push_back`,
`uset_int_insert`, ...) so that plain C, with no overloading, never collides
across instantiations. Two opt-in, compiler-supported ways to drop the prefix
at call sites are available; both are strictly additive and off by default.

## `CTL_OVERLOADABLE` (clang only)

Define `CTL_OVERLOADABLE` before including a container header that supports
it (`vector.h`, `unordered_set.h`) to get `__attribute__((overloadable))`
wrappers for the common self-pointer methods, named after the method with no
prefix:

    #define CTL_OVERLOADABLE
    #define POD
    #define T int
    #include <ctl/vector.h>

    #define POD
    #define T int
    #include <ctl/unordered_set.h>

    vec_int a = vec_int_init();
    push_back(&a, 1);          // instead of vec_int_push_back(&a, 1)
    size(&a);                  // instead of vec_int_size(&a)

    uset_int b = uset_int_init(int_hash, int_equal);
    insert(&b, 1);             // instead of uset_int_insert(&b, 1)

Overload resolution is purely on the pointer type of the first argument
(`vec_int *` vs `vec_double *` vs `uset_int *`, ...), so multiple container
types and element types can coexist in the same translation unit without
collisions.

Two deliberate exclusions:

- `init`/`init_from` are never wrapped. Several containers declare a
  zero-argument `init(void)`; `__attribute__((overloadable))` dispatches on
  parameter types only, so two zero-arg `init`s cannot be disambiguated.
  Keep using the prefixed constructor (`vec_int_init()`, `uset_int_init(...)`).
- `free` is never wrapped, to avoid colliding with the standard library's
  `free(void*)`.

`CTL_OVERLOADABLE` is **not** undefined by the container headers (unlike
`POD`/`NOT_INTEGRAL`): define it once before your first container include to
enable the wrappers for every subsequent instantiation in the translation
unit.

## `_Generic` dispatch (any C11 compiler)

`_Generic` requires an exhaustive, compile-time list of types at the call
site, which only the caller can know — the library cannot synthesize it.
The recipe: `_Generic` on the pointer type to pick the right prefixed
function, then apply it to the arguments.

    #define insert(self, ...) _Generic((self),          \
        vec_int*:  vec_int_insert,                      \
        uset_int*: uset_int_insert)(self, __VA_ARGS__)

    vec_int a = vec_int_init();
    insert(&a, 1);   // expands to vec_int_insert(&a, 1)

Add one line per instantiated type your translation unit actually uses.
This works with any C11 compiler, not just clang.
