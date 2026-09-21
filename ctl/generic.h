/* Optional C11 _Generic dispatch: reduces the boilerplate of dropping the
   vec_T_/uset_T_/... prefix at call sites to one line per requested method
   name, instead of one line per (type, method) pair. Works with any C11
   compiler (gcc, clang, MSVC /std:c11+), unlike CTL_OVERLOADABLE
   (clang-only). See docs/overload.md and #4.
   SPDX-License-Identifier: MIT */
#ifndef CTL_GENERIC_H
#define CTL_GENERIC_H

#include <ctl/ctl.h>

/* _Generic requires an exhaustive, compile-time type list; only the caller
   knows which container instantiations exist in their translation unit, so
   the caller must supply that list as a variadic X-macro forwarding its
   extra argument(s) to each case:

       #define CTL_TYPES(X, ...) \
           X(vec_int,  __VA_ARGS__) \
           X(uset_int, __VA_ARGS__)

   Then define one dispatch macro per method name actually needed:

       #define insert(self, ...) CTL_GENERIC_DISPATCH(CTL_TYPES, insert, self, __VA_ARGS__)
       #define size(self)        CTL_GENERIC_DISPATCH0(CTL_TYPES, size, self)

       insert(&a, 1);   // expands to vec_int_insert(&a, 1) or uset_int_insert(&a, 1)
       size(&a);        // expands to vec_int_size(&a) or uset_int_size(&a)

   Adding a type only touches CTL_TYPES, not every method macro. Methods
   with no A* self argument (init, init_from) cannot be dispatched this
   way, for the same reason CTL_OVERLOADABLE excludes them: there is
   nothing to switch on. */

/* one `<prefix> *: <prefix>_<method>,` case */
#define CTL_GENERIC_CASE(PREFIX, METHOD) PREFIX *: JOIN(PREFIX, METHOD),

/* Declared, never defined: gives the default _Generic association a
   well-formed prototype without ever being reachable in correct usage
   (self's real type always matches one of TYPES). If a self type missing
   from TYPES genuinely reaches this branch, calling it fails to link,
   naming the problem instead of surfacing a raw _Generic diagnostic. */
extern void ctl_generic_unregistered_self_type(void);

/* full dispatch: picks <prefix>_<method> from self's pointer type, then
   calls it with (self, ...). ##__VA_ARGS__ swallows the trailing comma
   when METHOD takes no extra arguments (gcc/clang extension). `default`
   only exists to satisfy _Generic's grammar after the last case's comma;
   correct usage (self's type is in TYPES) never selects it. A self type
   missing from TYPES selects it instead, producing a clear "implicit
   declaration of function 'ctl_generic_unregistered_self_type'" error
   instead of a raw _Generic diagnostic. */
#define CTL_GENERIC_DISPATCH(TYPES, METHOD, self, ...) \
    _Generic((self), TYPES(CTL_GENERIC_CASE, METHOD) default: ctl_generic_unregistered_self_type)(self, ##__VA_ARGS__)

/* Zero-argument variant (METHOD(self) with no further arguments, e.g.
   size/empty/free). Avoids "ISO C99 requires at least one argument for
   the '...'" under -Wpedantic -Werror, which CTL_GENERIC_DISPATCH would
   trigger when called with nothing beyond self. */
#define CTL_GENERIC_DISPATCH0(TYPES, METHOD, self) \
    _Generic((self), TYPES(CTL_GENERIC_CASE, METHOD) default: ctl_generic_unregistered_self_type)(self)

/* Variant accepting one extra, hand-written _Generic case (no trailing
   comma) ahead of `default`, for adding a single non-CTL type to the
   dispatch. _Generic requires an *exact* type match with no implicit
   conversion: a `void *` case only ever catches an argument whose C type
   is literally `void *`, never `int *`, `struct foo *`, etc. Redefining a
   libc name such as `free` is therefore unsafe in any file that also
   frees other heap pointers -- those calls silently stop compiling once
   `free` is a macro, and no single fallback case can catch every pointer
   type. Prefer a distinct name (`ctl_free`, not `free`) with
   CTL_GENERIC_DISPATCH/CTL_GENERIC_DISPATCH0 instead; reach for this
   variant only when the extra type is truly known and exact. */
#define CTL_GENERIC_DISPATCH_EXTRA(TYPES, METHOD, EXTRA_CASE, self, ...) \
    _Generic((self), TYPES(CTL_GENERIC_CASE, METHOD) EXTRA_CASE, default: ctl_generic_unregistered_self_type)(self, ##__VA_ARGS__)

/* Zero-argument counterpart to CTL_GENERIC_DISPATCH_EXTRA. */
#define CTL_GENERIC_DISPATCH_EXTRA0(TYPES, METHOD, EXTRA_CASE, self) \
    _Generic((self), TYPES(CTL_GENERIC_CASE, METHOD) EXTRA_CASE, default: ctl_generic_unregistered_self_type)(self)

#endif
