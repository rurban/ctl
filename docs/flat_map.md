# flat_map - CTL - C Container Template library

Defined in header **<ctl/flat_map.h>**, CTL prefix **fmap**,
deriving from [flat_set](flat_set.md).

## SYNOPSIS

    typedef struct { int key; int value; } intint;
    static inline int intint_cmp(intint *a, intint *b) { return a->key < b->key; }

    #define POD
    #define NOT_INTEGRAL
    #define T intint
    #include <ctl/flat_map.h>

    fmap_intint a = fmap_intint_init(intint_cmp);
    fmap_intint_insert(&a, (intint){1, 10});
    fmap_intint_insert_or_assign(&a, (intint){1, 99}); // overwrites value
    foreach(fmap_intint, &a, it) printf("%d=%d\n", it.ref->key, it.ref->value);
    fmap_intint_free(&a);

## DESCRIPTION

**flat_map** (C++23) is a sorted contiguous associative container of **unique**
key/value pairs, ordered by key. Like [map](map.md) derives from [set](set.md),
flat_map derives from [flat_set](flat_set.md) (remapping the `fset` prefix to
`fmap`) and adds the key/value-specific modifiers.

`T` must be a struct whose `compare`/`equal` order by the key only (e.g. the
`intint` or `strint` pair). Lookups accept a `T` whose key field is set.

The function names are composed of the prefix **fmap_**, the user-defined type
**T** and the method name.

## Member functions

flat_map has the full [flat_set](flat_set.md) API (init, insert, find, count,
contains, lower_bound, upper_bound, equal_range, erase, erase_it, copy, swap,
size, empty, ...), plus:

    I insert_or_assign (A* self, T pair)

inserts pair, or overwrites the mapped value of the existing equal key (freeing
the old element). Returns an iterator to the element.

    I insert_or_assign_found (A* self, T pair, int* foundp)

as above, reporting via `*foundp` whether the key already existed.

    I insert (A* self, T pair)

inserts a key/value pair with a unique key; a duplicate key is ignored (the
passed pair is freed). (C++23)

    size_t erase (A* self, T key)

erases the element whose key equals `key.key`.

See [flat_set](flat_set.md) and [algorithm](algorithm.md) for more.
