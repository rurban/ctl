# Overload - dropping the type prefix (clang `overloadable` and C11 `_Generic`)

CTL function names are prefixed with the container/type pair (`vec_int_push_back`,
`uset_int_insert`, ...) so that plain C, with no overloading, never collides
across instantiations. Two compiler-supported ways to drop the prefix
at call sites are available; both are strictly additive.

## `__attribute__((overloadable))` (clang only, automatic)

`vector.h` and `unordered_set.h` automatically declare
`__attribute__((overloadable))` wrappers for the common self-pointer
methods, named after the method with no prefix, whenever the compiler
advertises support (`__has_attribute(overloadable)`, true for clang, false
for gcc/MSVC). No opt-in macro is needed:

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

On a compiler without the attribute, the wrappers are simply never declared;
every instantiation still gets its normal prefixed API.

## `_Generic` dispatch: `<ctl/generic.h>` (any C11 compiler)

`_Generic` requires an exhaustive, compile-time type list at the call site,
which only the caller can know — the library cannot synthesize it, so the
caller supplies that list once as a variadic X-macro forwarding its extra
argument(s) to each entry:

    #define CTL_TYPES(X, ...) \
        X(vec_int,  __VA_ARGS__) \
        X(uset_int, __VA_ARGS__)

`<ctl/generic.h>` then turns that list into a dispatch macro with one line
per method name actually needed — not one line per (type, method) pair:

    #include <ctl/generic.h>

    #define insert(self, ...) CTL_GENERIC_DISPATCH(CTL_TYPES, insert, self, __VA_ARGS__)
    #define size(self)        CTL_GENERIC_DISPATCH0(CTL_TYPES, size, self)

    vec_int a = vec_int_init();
    insert(&a, 1);    // expands to vec_int_insert(&a, 1)
    size(&a);         // expands to vec_int_size(&a)

Adding a type only touches `CTL_TYPES`, not every method macro. Use
`CTL_GENERIC_DISPATCH0` for a method that takes no argument beyond `self`
(`size`, `empty`, ...) — `CTL_GENERIC_DISPATCH`'s trailing `...` otherwise
triggers `-Wpedantic`'s "ISO C99 requires at least one argument for the
`...`" under `-Werror`. A `self` type missing from the list fails to
compile/link, naming `ctl_generic_unregistered_self_type` instead of
surfacing a raw `_Generic` diagnostic.

This works with any C11 compiler (gcc, clang, MSVC `/std:c11+`), unlike the
clang-only `__attribute__((overloadable))` wrappers above. It shares the
same `init`/`init_from` exclusion (no `self` to switch on).

### Do not shadow `free`

`_Generic` dispatch is a macro, not a real overload: `#define free(self) ...`
textually replaces every `free` in the rest of the file, including calls on
plain heap pointers CTL knows nothing about. `_Generic` also requires an
*exact* type match with no implicit conversion, so a `void *` fallback case
(`CTL_GENERIC_DISPATCH_EXTRA`/`_EXTRA0`) only ever catches an argument whose
C type is literally `void *` — never `int *`, `struct foo *`, etc. There is
no way to write a fallback case that catches every other pointer type.
Use a distinct name instead (`ctl_free`, not `free`):

    #define ctl_free(self) CTL_GENERIC_DISPATCH0(CTL_TYPES, free, self)

    ctl_free(&a);   // vec_int_free(&a); plain free(ptr) elsewhere is untouched

`CTL_GENERIC_DISPATCH_EXTRA(TYPES, METHOD, EXTRA_CASE, self, ...)` and its
zero-argument counterpart `CTL_GENERIC_DISPATCH_EXTRA0` add one hand-written,
exact-type `_Generic` case ahead of the registered types, for the narrow
case where the extra type really is known and exact.
