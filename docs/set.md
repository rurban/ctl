# set - CTL - C Container Template library

Defined in header **<ctl/set.h>**, CTL prefix **set**,
parent for [map](map.md).

## SYNOPSIS

    static inline int
    int_cmp(int *a, int *b) {
      return *a < *b;
    }

    #define POD
    #define T int
    #include <ctl/set.h>

    int i = 0;
    set_int a = set_int_init (int_cmp);

    for (i=0; i<1000; i++) {
      set_int_insert (&a, i);
    }

    foreach(set_int, &a, it) { i = it.ref->key); }
    printf("last key %d, ", i);

    printf("min {\"%s\", %d} ", set_int_min (a));
    printf("max {\"%s\", %d}\n", set_int_max (a));
    set_int_free(&a);

## DESCRIPTION

set is a sorted associative container that contains key-value pairs with unique
keys. Keys are sorted by using the custom comparison function. Search, removal,
and insertion operations have logarithmic complexity. set is implemented as red-black tree.

The function names are composed of the prefix **set_**, the user-defined type
**T** and the method name. E.g `set_int` with `#define T int`.

Everywhere the CTL uses the Compare requirements, uniqueness is
determined by using the equivalence relation. In imprecise terms, two objects a
and b are considered equivalent (not unique) if neither compares less than the
other: !comp(a, b) && !comp(b, a).

## Member types

`T`                     value type

`A` being `set_T`       container type

`B` being `set_T_node`  node type

`I` being `set_T_it`    iterator type

`IT` being `B*`, the generic type of iterators.

## Member functions

    A init (int compare(T*, T*))

constructs the set.

    free (A* self)

destructs the set.

    assign (A* self, A* other)

replaces the contents of the container.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* at (A* self, size_t index)

access specified element with bounds checking

## Iterators

    B* begin (A* self)

returns an iterator to the beginning

    B* end (A* self)

returns an iterator to the end

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

## Modifiers

    clear (A* self)

clears the contents

    B* insert (A* self, T value)

inserts the element. (C++17)

    emplace (A* self, T* value)

constructs elements in-place. _(NYI)_

    emplace_hint (A* self, B* pos, T* value)

constructs elements in-place at position. _(NYI)_

    erase (A* self, T value)

erases the element by value.

    erase_it (A* self, I* pos)

erases the element at pos.

    erase_range (A* self, I* first, I* last)

erases elements.

    swap (A* self, A* other)

swaps the contents

    extract (A* self, T key)

extracts a node from the container. _(NYI)_

    extract_it (A* self, I* pos)

extracts nodes from the container. _(NYI)_

    merge (A* self)

splices nodes from another container

## Lookup

    size_t count (A* self)

returns the number of elements matching specific key.

    B* find (A* self, T key)

finds element with specific key. does not consume/delete the key.

    int contains (A* self, T key)

checks if the container contains element with specific key. (C++20)

    equal_range ??

returns range of elements matching a specific key. _(NYI)_

    B* lower_bound (A* self, T key)

returns an iterator to the first element not less than the given key. _(NYI)_

    B* upper_bound (A* self, T key)

returns an iterator to the first element greater than the given key. _(NYI)_

## Observers

    value_comp (A* self)

Returns the function that compares keys in objects of type value_type T. _(NYI)_

## Non-member functions

    swap (A* self)

specializes the swap algorithm

    size_t remove_if (A* self, int match(T*))

Removes all elements satisfying specific criteria.

    erase_if (A* self, int match(T*))

erases all elements satisfying specific criteria. (C++20)

    A intersection (A* self, A* other)
    A union (A* self, A* other)
    A difference (A* self, A* other)
    A symmetric_difference (A* self, A* other)


See [algorithm](algorithm.md) for more.
