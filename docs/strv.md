# strv - CTL - C Container Template library

Defined in header **<ctl/strv.h>**, CTL prefix **strv**. Not templated: `T`
is fixed to `char`, like `std::string_view`.

## SYNOPSIS

    #include <ctl/strv.h>

    strv hello = strv_init("hello world");
    strv world = strv_substr(&hello, 6, STRV_NPOS);
    strv expect = strv_init("world");
    assert(strv_equal(&world, &expect));

## DESCRIPTION

`strv` is a **non-owning** view over a contiguous run of `char`: a pointer
and a size. It never allocates, copies, or frees, and does not require or
assume NUL termination past `size`. The viewed storage must outlive the
view.

Interop with `str` (`<ctl/string.h>`): build a view with
`strv_init_n(s.vector, s.size)`.

## Member functions

    strv init (const char* c_str)

constructs a view over a NUL-terminated C string (`strlen`-based).

    strv init_n (const char* data, size_t size)

constructs a view over `[data, data + size)`, independent of any NUL.

## Element access

    const char* data (strv* self)
    char at (strv* self, size_t index)   // asserts in-range
    char front (strv* self)
    char back (strv* self)

## Iterators

    const char* begin (strv* self)
    const char* end (strv* self)

## Capacity

    size_t size (strv* self)
    int empty (strv* self)

## Views and search

    strv substr (strv* self, size_t offset, size_t count)

a view over `[offset, offset + count)`; `count` is clamped, so
`STRV_NPOS` means "to the end".

    int compare (strv* self, strv* other)

three-way lexicographic byte comparison.

    int equal (strv* self, strv* other)

    size_t find (strv* self, strv* needle)

first index of `needle` in `self`, or `STRV_NPOS`.

    int starts_with (strv* self, strv* prefix)
    int ends_with (strv* self, strv* suffix)
