# flat_multimap - CTL - C Container Template library

Defined in header **<ctl/flat_multimap.h>**, CTL prefix **fmmap**,
deriving from [flat_set](flat_set.md), sibling of [flat_map](flat_map.md).

## SYNOPSIS

    typedef struct { int key; int value; } intint;
    static inline int intint_cmp(intint *a, intint *b) { return a->key < b->key; }

    #define POD
    #define NOT_INTEGRAL
    #define T intint
    #include <ctl/flat_multimap.h>

    fmmap_intint a = fmmap_intint_init(intint_cmp);
    fmmap_intint_insert(&a, (intint){1, 10});
    fmmap_intint_insert(&a, (intint){1, 11}); // duplicate key kept
    printf("count 1: %zu\n", fmmap_intint_count(&a, (intint){1,0})); // 2
    fmmap_intint_free(&a);

## DESCRIPTION

**flat_multimap** (C++23) is [flat_set](flat_set.md) instantiated with
`CTL_FLAT_MULTI` and the `fmmap` prefix, with `T` a key/value struct ordered by
the key only: a sorted contiguous associative container of key/value pairs that
**keeps duplicate keys**. Equal keys retain their insertion order.

The function names are composed of the prefix **fmmap_**, the user-defined type
**T** and the method name.

It has the [flat_set](flat_set.md) API with multi-key semantics (see
[flat_multiset](flat_multiset.md)):

    I insert (A* self, T pair)

always inserts, at the upper bound of the equal-key run.

    size_t count (A* self, T key)

number of pairs whose key equals `key.key`.

    size_t erase (A* self, T key)

erases **all** pairs with that key, returning the count removed.

    equal_range (A* self, T key, I* lower, I* upper)

spans the whole run of pairs with equal keys.

See [flat_set](flat_set.md) and [algorithm](algorithm.md) for more.
