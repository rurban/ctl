# flat_set - CTL - C Container Template library

Defined in header **<ctl/flat_set.h>**, CTL prefix **fset**,
parent for [flat_map](flat_map.md), sibling of [flat_multiset](flat_multiset.md).

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/flat_set.h>

    fset_int a = fset_int_init(NULL); // NULL => default integral compare

    for (int i = 0; i < 1000; i++)
      fset_int_insert(&a, rand() % 100);

    foreach(fset_int, &a, it) { printf("%d ", *it.ref); }
    printf("contains 5: %d\n", fset_int_contains(&a, 5));
    fset_int_free(&a);

## DESCRIPTION

**flat_set** (C++23) is a sorted associative container of **unique** keys,
stored in a single contiguous array (deriving from [vector](vector.md)).
It trades O(n) insert/erase (the tail is shifted) for cache-friendly O(log n)
lookup and full random access, `at()` and `data()`, over the sorted elements.

Keys are ordered by the 2-way `compare` (`*a < *b`). Two keys are equivalent
(not unique) when neither compares less than the other:
`!compare(a, b) && !compare(b, a)`.

The function names are composed of the prefix **fset_**, the user-defined type
**T** and the method name. E.g `fset_int` with `#define T int`.

With `CTL_FLAT_MULTI` defined the core becomes a
[flat_multiset](flat_multiset.md) (duplicates kept).

## Member types

`T`                      value type

`A` being `fset_T`       container type

`I` being `fset_T_it`    iterator type

## Member functions

    A init (int compare(T*, T*))

constructs the flat_set. Pass `NULL` to use the default compare of an integral
POD `T`; otherwise a compare is required.

    free (A* self)

destructs the flat_set and all elements.

    A copy (A* self)

returns a sorted copy of the container.

## Element access

    T* at (A* self, size_t index)

random access to the index'th smallest element, with bounds checking.

    T* front (A* self)
    T* back (A* self)
    T* data (A* self)

## Iterators

    I begin (A* self)
    I end (A* self)
    I* advance (I* iter, long i)

Random-access iterators over the sorted elements. See [iterators](iterators.md).

## Capacity

    int empty (A* self)
    size_t size (A* self)
    size_t max_size (void)
    size_t capacity (A* self)
    reserve (A* self, size_t n)
    shrink_to_fit (A* self)

## Modifiers

    I insert (A* self, T value)

inserts value, keeping the array sorted. On a duplicate the passed value is
freed and the existing element is returned. (C++23)

    I insert_found (A* self, T value, int* foundp)

as `insert`, additionally reporting via `*foundp` whether an equal key existed.

    I emplace (A* self, T* value)

inserts `*value`.

    size_t erase (A* self, T key)

erases the element equal to key (all equal elements for a multiset) and returns
the number removed. The search key is borrowed, never freed.

    I erase_it (I* pos)

erases the element at pos and returns an iterator to the next element.

    I* erase_range (I* range)

erases a range of elements.

    swap (A* self, A* other)

    size_t remove_if (A* self, int match(T*))
    size_t erase_if  (A* self, int match(T*))

removes every element satisfying the predicate. (C++20)

    clear (A* self)

## Lookup

    size_t count (A* self, T key)

number of elements equal to key (0 or 1 for a flat_set).

    int contains (A* self, T key)

whether an equal key is present. (C++20)

    I find (A* self, T key)

iterator to the element equal to key, or `end`. Does not consume the key.

    I lower_bound (A* self, T key)

iterator to the first element not less than key.

    I upper_bound (A* self, T key)

iterator to the first element greater than key.

    equal_range (A* self, T key, I* lower, I* upper)

sets `lower`/`upper` to the `[first,last)` range of elements equal to key.

## Non-member functions

    int equal (A* self, A* other)

See [algorithm](algorithm.md) for the generic iterator methods.
