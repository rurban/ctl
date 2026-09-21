# flat_multiset - CTL - C Container Template library

Defined in header **<ctl/flat_multiset.h>**, CTL prefix **fmset**,
sibling of [flat_set](flat_set.md).

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/flat_multiset.h>

    fmset_int a = fmset_int_init(NULL);
    fmset_int_insert(&a, 3);
    fmset_int_insert(&a, 3);
    fmset_int_insert(&a, 1);
    printf("count 3: %zu\n", fmset_int_count(&a, 3)); // 2
    fmset_int_free(&a);

## DESCRIPTION

**flat_multiset** (C++23) is [flat_set](flat_set.md) instantiated with
`CTL_FLAT_MULTI` and the `fmset` prefix: a sorted contiguous associative
container that **keeps duplicate keys**. Equal keys retain their insertion
order (new equal keys are placed at the `upper_bound`).

The function names are composed of the prefix **fmset_**, the user-defined type
**T** and the method name.

It has the same API as [flat_set](flat_set.md), with these multi-key semantics:

    I insert (A* self, T value)

always inserts, at the upper bound of the equal run.

    size_t count (A* self, T key)

returns the number of elements equal to key (may be > 1).

    size_t erase (A* self, T key)

erases **all** elements equal to key and returns the count removed.

    equal_range (A* self, T key, I* lower, I* upper)

spans the whole run of equal keys.

See [flat_set](flat_set.md) for the full member list and
[algorithm](algorithm.md) for the generic methods.
